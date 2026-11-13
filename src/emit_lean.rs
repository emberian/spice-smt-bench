//! Lean 4 `Prop` target specification emitter (`--dialect lean4`).

use std::collections::BTreeMap;
use std::fmt::Write;

use crate::ast::{sanitize_ident, CmpOp, ExpectedStatus, Expr, Formula, InitSpec, TranMethod};
use crate::stamp::{StampedBody, StampedSystem};

/// Convert an `f64` into an exact Lean 4 `TranscendentalField` constructor term without exponent clamping.
pub fn format_lean_rat_call(v: f64) -> String {
    let (negative, numerator, denominator) = crate::numeral::exact_f64_to_rat(v)
        .expect("emitter requires finite stamped constants");
    if numerator == "0" { return "TF.zero".to_string(); }
    if numerator == "1" && denominator == "1" && !negative { return "TF.one".to_string(); }
    let numerator = if negative { format!("(-{numerator})") } else { numerator };
    if denominator == "1" { format!("(TF.ofInt {numerator})") }
    else { format!("(TF.ofRat {numerator} {denominator})") }
}

fn emit_expr_lean(e: &Expr) -> String {
    match e {
        Expr::Num(v) => format_lean_rat_call(*v),
        Expr::Var(name) => sanitize_lean_ident(name),
        Expr::NodeVolt(n) => sanitize_lean_ident(&format!("v_{}", sanitize_ident(n))),
        Expr::Time => "t_var".to_string(),
        Expr::Neg(a) => format!("(TF.neg {})", emit_expr_lean(a)),
        Expr::Add(a, b) => format!("(TF.add {} {})", emit_expr_lean(a), emit_expr_lean(b)),
        Expr::Sub(a, b) => format!("(TF.sub {} {})", emit_expr_lean(a), emit_expr_lean(b)),
        Expr::Mul(a, b) => format!("(TF.mul {} {})", emit_expr_lean(a), emit_expr_lean(b)),
        Expr::Div(a, b) => format!("(TF.div {} {})", emit_expr_lean(a), emit_expr_lean(b)),
        Expr::Exp(a) => format!("(TF.exp {})", emit_expr_lean(a)),
        Expr::Sqrt(a) => format!("(TF.sqrt {})", emit_expr_lean(a)),
        Expr::Ln1pExp(a) => format!("(TF.ln1pExp {})", emit_expr_lean(a)),
    }
}

fn emit_formula_lean(f: &Formula) -> String {
    match f {
        Formula::Cmp { op, lhs, rhs } => {
            let l = emit_expr_lean(lhs);
            let r = emit_expr_lean(rhs);
            match op {
                CmpOp::Eq => format!("({l} = {r})"),
                CmpOp::Le => format!("(TF.le {l} {r})"),
                CmpOp::Lt => format!("(TF.lt {l} {r})"),
                CmpOp::Ge => format!("(TF.le {r} {l})"),
                CmpOp::Gt => format!("(TF.lt {r} {l})"),
            }
        }
        Formula::And(items) => {
            if items.is_empty() {
                "True".to_string()
            } else {
                let parts: Vec<String> = items.iter().map(emit_formula_lean).collect();
                format!("({})", parts.join(" ∧ "))
            }
        }
        Formula::Or(items) => {
            if items.is_empty() {
                "False".to_string()
            } else {
                let parts: Vec<String> = items.iter().map(emit_formula_lean).collect();
                format!("({})", parts.join(" ∨ "))
            }
        }
        Formula::Not(inner) => format!("(¬ {})", emit_formula_lean(inner)),
    }
}

// Share repeated arithmetic subterms within each proposition. The emitted lets are
// definitionally equal to the expanded expression, keeping large transient stamps
// cheap for Lean's elaborator without changing their mathematical specification.
fn share_subterms(source: &str) -> String {
    if source.len() < 2000 { return source.to_owned(); }
    fn visit(source: &str, cache: &mut BTreeMap<String, String>, defs: &mut Vec<String>) -> String {
        let mut out = String::new();
        let mut start = 0;
        while let Some(offset) = source[start..].find('(') {
            let begin = start + offset;
            out.push_str(&source[start..begin]);
            let mut depth = 1;
            let mut end = begin + 1;
            while depth > 0 {
                match source.as_bytes()[end] { b'(' => depth += 1, b')' => depth -= 1, _ => {} }
                end += 1;
            }
            let inner = visit(&source[begin+1..end-1], cache, defs);
            let term = format!("({inner})");
            if inner.starts_with("TF.") && term.len() > 80 {
                let name = if let Some(name) = cache.get(&term) { name.clone() } else {
                    let name = format!("«shared{}»", defs.len());
                    defs.push(format!("let {name} := {term}; "));
                    cache.insert(term, name.clone());
                    name
                };
                out.push_str(&name);
            } else { out.push_str(&term); }
            start = end;
        }
        out.push_str(&source[start..]);
        out
    }
    let mut defs = Vec::new();
    let result = visit(source, &mut BTreeMap::new(), &mut defs);
    format!("({}{result})", defs.join(""))
}

fn conjunction(parts: &[String]) -> String {
    if parts.is_empty() { return "True".into(); }
    if parts.len() <= 16 { return parts.join(" ∧\n    "); }
    let mid = parts.len()/2;
    format!("({}) ∧ ({})", conjunction(&parts[..mid]), conjunction(&parts[mid..]))
}

fn sanitize_lean_ident(raw: &str) -> String {
    let s = sanitize_ident(raw);
    match s.as_str() {
        "in" | "out" | "end" | "def" | "theorem" | "let" | "fun" | "if" | "then" | "else"
        | "match" | "with" | "where" | "open" | "section" | "namespace" | "variable" => {
            format!("{s}_v")
        }
        _ => s,
    }
}

/// Emit a standalone or embeddable Lean 4 `Prop` definition for `sys`.
/// - For `ExpectedStatus::Unsat` (or unspecified), emits the universal safety target:
///   `∀ params vars, Box(params, vars) → Physics(params, vars) → ¬ Unsafe(params, vars)`.
/// - For `ExpectedStatus::Sat`, emits the existential defect / Trojan counterexample target:
///   `∃ params vars, Box(params, vars) ∧ Physics(params, vars) ∧ Unsafe(params, vars)`.
pub fn emit_lean_def(sys: &StampedSystem, def_name: &str, include_imports: bool) -> String {
    let mut out = String::with_capacity(4096);
    if include_imports {
        writeln!(out, "import SpiceSmtBench.PhysicsModels").unwrap();
        writeln!(out, "namespace SpiceSmtBench.Targets").unwrap();
        writeln!(out).unwrap();
    }

    let is_sat = sys.expected == Some(ExpectedStatus::Sat);
    writeln!(out, "/-- {}", sys.title).unwrap();
    if let Some(pdk) = sys.pdk {
        writeln!(out, "    PDK: `{pdk}`.").unwrap();
    }
    writeln!(
        out,
        "    Expected SMT status: `{}`. -/",
        if is_sat { "sat" } else { "unsat" }
    )
    .unwrap();
    writeln!(
        out,
        "def {} {{R : Type}} (TF : TranscendentalField R) : Prop :=",
        sanitize_ident(def_name)
    )
    .unwrap();

    let mut all_binders: Vec<(String, Option<(f64, f64)>)> = Vec::new();
    for p in &sys.params {
        all_binders.push((sanitize_lean_ident(&p.name), Some((p.lo, p.hi))));
    }

    let mut eq_hyps: Vec<String> = Vec::new();

    let unsafe_prop: String = match &sys.body {
        StampedBody::Algebraic { vars, constraints } => {
            for v in vars {
                all_binders.push((sanitize_lean_ident(&v.name), v.bounds));
            }
            for c in constraints {
                eq_hyps.push(emit_formula_lean(&c.formula));
            }
            emit_formula_lean(&sys.unsafe_formula)
        }
        StampedBody::Ode { .. } => return emit_lean_ode_def(sys, def_name, include_imports),
    };

    let eq_hyps: Vec<_> = eq_hyps.iter().map(|s| share_subterms(s)).collect();
    let quant = if is_sat { "∃" } else { "∀" };
    write!(out, "  {quant} (").unwrap();
    for (i, (bname, _)) in all_binders.iter().enumerate() {
        if i > 0 { write!(out, " ").unwrap(); }
        write!(out, "{bname}").unwrap();
    }
    writeln!(out, " : R),").unwrap();

    let mut box_conjuncts = Vec::with_capacity(all_binders.len());
    for (bname, bounds) in &all_binders {
        let Some((lo, hi)) = bounds else { continue; };
        box_conjuncts.push(format!(
            "(TF.le {} {bname} ∧ TF.le {bname} {})",
            format_lean_rat_call(*lo),
            format_lean_rat_call(*hi)
        ));
    }
    let box_str = if box_conjuncts.is_empty() {
        "True".to_string()
    } else {
        conjunction(&box_conjuncts)
    };
    let phys_str = if eq_hyps.is_empty() {
        "True".to_string()
    } else {
        conjunction(&eq_hyps)
    };

    if is_sat {
        writeln!(out, "    ({box_str}) ∧").unwrap();
        writeln!(out, "    ({phys_str}) ∧").unwrap();
        writeln!(out, "    {unsafe_prop}").unwrap();
    } else {
        writeln!(out, "    ({box_str}) →").unwrap();
        writeln!(out, "    ({phys_str}) →").unwrap();
        writeln!(out, "    ¬ {unsafe_prop}").unwrap();
    }

    if include_imports {
        writeln!(out).unwrap();
        writeln!(out, "end SpiceSmtBench.Targets").unwrap();
    }
    out
}

/// Keep the finite time index symbolic in Lean. This states precisely the same
/// recurrence as SMT unrolling, including its individually rounded sample times,
/// without duplicating the entire device model at every step.
fn emit_lean_ode_def(sys: &StampedSystem, def_name: &str, imports: bool) -> String {
    let StampedBody::Ode { static_vars, static_constraints, states, dt, steps, method } = &sys.body else { unreachable!() };
    let mut out = String::new();
    if imports { out.push_str("import SpiceSmtBench.PhysicsModels\nnamespace SpiceSmtBench.Targets\n\n"); }
    writeln!(out, "/-- {}: finite sampled transient target, including sample zero. -/", sys.title).unwrap();
    writeln!(out, "def {} {{R : Type}} (TF : TranscendentalField R) : Prop :=", sanitize_ident(def_name)).unwrap();
    let sat = sys.expected == Some(ExpectedStatus::Sat);
    let quant = if sat { "∃" } else { "∀" };
    let mut binders: Vec<_> = sys.params.iter().map(|p| (p.name.clone(), Some((p.lo,p.hi)))).collect();
    binders.extend(static_vars.iter().map(|v| (v.name.clone(), v.bounds)));
    if !binders.is_empty() {
        writeln!(out, "  {quant} ({} : R),", binders.iter().map(|(n,_)| sanitize_lean_ident(n)).collect::<Vec<_>>().join(" ")).unwrap();
    }
    writeln!(out, "  {quant} (state : Nat → Nat → R),").unwrap();
    let times: Vec<_> = (0..=*steps).map(|k| format_lean_rat_call(k as f64 * dt)).collect();
    writeln!(out, "    let _sampleTime : Nat → R := fun k => ([{}] : List R).getD k TF.zero", times.join(", ")).unwrap();
    let mut replacements = BTreeMap::new();
    let mut current = BTreeMap::new();
    let mut next = BTreeMap::new();
    for (i, st) in states.iter().enumerate() {
        let here = format!("sampleHere{i}"); let there = format!("sampleNext{i}");
        current.insert(st.name.clone(), Expr::var(&here)); next.insert(st.name.clone(), Expr::var(&there));
        replacements.insert(here, format!("(state k {i})"));
        replacements.insert(there, format!("(state (k+1) {i})"));
        replacements.insert(format!("derivativeHere{i}"), format!("(dx k {i})"));
        replacements.insert(format!("derivativeNext{i}"), format!("(dx (k+1) {i})"));
    }
    replacements.insert("sampleTimeHere".into(), "(_sampleTime k)".into());
    replacements.insert("sampleTimeNext".into(), "(_sampleTime (k+1))".into());
    let rewrite = |text: String| {
        let mut result = String::new(); let mut start = 0;
        while start < text.len() {
            let c = text[start..].chars().next().unwrap();
            if c.is_ascii_alphabetic() || c == '_' {
                let end = start + text[start..].bytes().take_while(|c| c.is_ascii_alphanumeric() || *c == b'_').count();
                let word = &text[start..end];
                result.push_str(replacements.get(word).map_or(word, String::as_str)); start = end;
            } else { result.push(c); start += c.len_utf8(); }
        }
        result
    };
    let nodes = BTreeMap::new();
    let time = Expr::var("sampleTimeHere");
    let mut physics: Vec<_> = static_constraints.iter().map(|c| emit_formula_lean(&c.formula)).collect();
    let mut bounds = Vec::new();
    for (name, interval) in &binders {
        if let Some((lo,hi)) = interval {
            bounds.push(format!("(TF.le {} {} ∧ TF.le {} {})",format_lean_rat_call(*lo),sanitize_lean_ident(name),sanitize_lean_ident(name),format_lean_rat_call(*hi)));
        }
    }
    let mut derivatives = Vec::new();
    let mut state_bounds = Vec::new(); let mut initial = Vec::new(); let mut recurrence = Vec::new();
    for (i, st) in states.iter().enumerate() {
        state_bounds.push(format!("(TF.le {} (state k {i}) ∧ TF.le (state k {i}) {})",format_lean_rat_call(st.lo),format_lean_rat_call(st.hi)));
        let init = match &st.init {
            InitSpec::Exact(e) => format!("(state k {i} = {})",rewrite(emit_expr_lean(&e.substitute(&current,&nodes,Some(&Expr::num(0.0)))))),
            InitSpec::Interval(lo,hi) => format!("(TF.le {} (state k {i}) ∧ TF.le (state k {i}) {})",format_lean_rat_call(*lo),format_lean_rat_call(*hi)),
        };
        initial.push(init);
        derivatives.push(rewrite(share_subterms(&emit_expr_lean(&st.rhs.substitute(&current,&nodes,Some(&time))))));
        let fnext = Expr::var(format!("derivativeNext{i}"));
        let rhs = match method {
            TranMethod::BackwardEuler => Expr::add(current[&st.name].clone(),Expr::mul(Expr::num(*dt),fnext)),
            TranMethod::Trapezoidal => Expr::add(current[&st.name].clone(),Expr::mul(Expr::num(0.5 * dt),Expr::add(Expr::var(format!("derivativeHere{i}")),fnext))),
        };
        recurrence.push(rewrite(share_subterms(&format!("(sampleNext{i} = {})",emit_expr_lean(&rhs)))));
    }
    writeln!(out, "    let dx : Nat → Nat → R := fun k i => ([{}] : List R).getD i TF.zero", derivatives.join(", ")).unwrap();
    bounds.push(format!("(∀ k : Nat, k ≤ {steps} → ({}))",conjunction(&state_bounds)));
    physics.push(format!("(let k : Nat := 0; {})",conjunction(&initial)));
    physics.push(format!("(∀ k : Nat, k < {steps} → ({}))",conjunction(&recurrence)));
    let unsafe_prop = rewrite(emit_formula_lean(&sys.unsafe_formula.substitute(&current,&nodes,Some(&time))));
    let unsafe_prop = format!("(∃ k : Nat, k ≤ {steps} ∧ {unsafe_prop})");
    let separator = if sat { "∧" } else { "→" };
    writeln!(out,"    ({}) {separator}\n    ({}) {separator}\n    {}{unsafe_prop}",conjunction(&bounds),conjunction(&physics),if sat {""} else {"¬ "}).unwrap();
    if imports { out.push_str("\nend SpiceSmtBench.Targets\n"); }
    out
}
