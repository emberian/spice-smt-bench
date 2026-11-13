//! Lean 4 `Prop` target specification emitter (`--dialect lean4`).

use std::collections::BTreeMap;
use std::fmt::Write;

use crate::ast::{sanitize_ident, CmpOp, ExpectedStatus, Expr, Formula, InitSpec, TranMethod};
use crate::stamp::{StampedBody, StampedSystem};

/// Convert an `f64` into an exact Lean 4 `TranscendentalField` constructor term without exponent clamping.
pub fn format_lean_rat_call(v: f64) -> String {
    if !v.is_finite() || v == 0.0 {
        return "TF.zero".to_string();
    }
    if v == 1.0 {
        return "TF.one".to_string();
    }
    let sign = if v < 0.0 { -1i128 } else { 1i128 };
    let av = v.abs();
    let sci = format!("{av:.12e}");
    if let Some((m_str, e_str)) = sci.split_once('e') {
        if let Ok(exp10) = e_str.parse::<i32>() {
            let digits: String = m_str.chars().filter(|c| *c != '.').collect();
            let frac_digits = m_str
                .split_once('.')
                .map_or(0i32, |(_, frac)| frac.len() as i32);
            if let Ok(mut mant) = digits.parse::<i128>() {
                let mut net_exp = exp10 - frac_digits;
                while mant != 0 && mant % 10 == 0 {
                    mant /= 10;
                    net_exp += 1;
                }
                if net_exp == 0 {
                    let num = sign * mant;
                    return if num < 0 {
                        format!("(TF.ofInt ({num}))")
                    } else {
                        format!("(TF.ofInt {num})")
                    };
                }
                if (1..=18).contains(&net_exp) {
                    let mut scaled = mant;
                    for _ in 0..(net_exp as usize) {
                        scaled *= 10;
                    }
                    let num = sign * scaled;
                    return if num < 0 {
                        format!("(TF.ofInt ({num}))")
                    } else {
                        format!("(TF.ofInt {num})")
                    };
                }
                if (-18..=-1).contains(&net_exp) {
                    let mut den: i128 = 1;
                    for _ in 0..((-net_exp) as usize) {
                        den *= 10;
                    }
                    let g = gcd_u128(mant.unsigned_abs(), den.unsigned_abs()) as i128;
                    let num = sign * (mant / g);
                    let den_red = den / g;
                    if den_red == 1 {
                        return if num < 0 {
                            format!("(TF.ofInt ({num}))")
                        } else {
                            format!("(TF.ofInt {num})")
                        };
                    }
                    return if num < 0 {
                        format!("(TF.ofRat ({num}) {den_red})")
                    } else {
                        format!("(TF.ofRat {num} {den_red})")
                    };
                }
                // Arbitrary scientific exponent (`|net_exp| > 18`): exact `TF.pow10` without clamping!
                let signed_mant = sign * mant;
                let mant_term = if signed_mant < 0 {
                    format!("(TF.ofInt ({signed_mant}))")
                } else {
                    format!("(TF.ofInt {signed_mant})")
                };
                return if net_exp > 0 {
                    format!("(TF.mul {mant_term} (TF.pow10 {net_exp}))")
                } else {
                    let k = -net_exp;
                    format!("(TF.div {mant_term} (TF.pow10 {k}))")
                };
            }
        }
    }
    "TF.zero".to_string()
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a.max(1)
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

    let mut all_binders: Vec<(String, f64, f64)> = Vec::new();
    for p in &sys.params {
        all_binders.push((sanitize_lean_ident(&p.name), p.lo, p.hi));
    }

    let mut eq_hyps: Vec<String> = Vec::new();

    let unsafe_prop: String = match &sys.body {
        StampedBody::Algebraic { vars, constraints } => {
            for v in vars {
                all_binders.push((sanitize_lean_ident(&v.name), v.lo, v.hi));
            }
            for c in constraints {
                eq_hyps.push(emit_formula_lean(&c.formula));
            }
            emit_formula_lean(&sys.unsafe_formula)
        }
        StampedBody::Ode {
            static_vars,
            static_constraints,
            states,
            dt,
            steps,
            method,
        } => {
            for v in static_vars {
                all_binders.push((sanitize_lean_ident(&v.name), v.lo, v.hi));
            }
            for c in static_constraints {
                eq_hyps.push(emit_formula_lean(&c.formula));
            }
            let empty_nodes = BTreeMap::new();
            let mut step_maps = Vec::with_capacity(*steps + 1);
            for k in 0..=*steps {
                let mut m = BTreeMap::new();
                for st in states {
                    let sk = format!("{}_s{k}", st.name);
                    all_binders.push((sanitize_lean_ident(&sk), st.lo, st.hi));
                    m.insert(st.name.clone(), Expr::var(sk));
                }
                step_maps.push(m);
            }
            for st in states {
                let s0 = sanitize_lean_ident(&format!("{}_s0", st.name));
                match &st.init {
                    InitSpec::Interval(lo, hi) => {
                        eq_hyps.push(format!(
                            "(TF.le {} {s0} ∧ TF.le {s0} {})",
                            format_lean_rat_call(*lo),
                            format_lean_rat_call(*hi)
                        ));
                    }
                    InitSpec::Exact(e) => {
                        let sub = e.substitute(&step_maps[0], &empty_nodes, Some(&Expr::num(0.0)));
                        eq_hyps.push(format!("({s0} = {})", emit_expr_lean(&sub)));
                    }
                }
            }
            let mut u_disj = Vec::with_capacity(*steps);
            for k in 1..=*steps {
                let tk = Expr::num((k as f64) * (*dt));
                let tk_prev = Expr::num(((k - 1) as f64) * (*dt));
                for st in states {
                    let xk = Expr::var(format!("{}_s{k}", st.name));
                    let xkp = Expr::var(format!("{}_s{}", st.name, k - 1));
                    let fk = st.rhs.substitute(&step_maps[k], &empty_nodes, Some(&tk));
                    let rhs = match method {
                        TranMethod::BackwardEuler => Expr::add(xkp, Expr::mul(Expr::num(*dt), fk)),
                        TranMethod::Trapezoidal => {
                            let fkp =
                                st.rhs
                                    .substitute(&step_maps[k - 1], &empty_nodes, Some(&tk_prev));
                            Expr::add(
                                xkp,
                                Expr::mul(Expr::num(0.5 * (*dt)), Expr::add(fkp, fk)),
                            )
                        }
                    };
                    eq_hyps.push(format!(
                        "({} = {})",
                        emit_expr_lean(&xk),
                        emit_expr_lean(&rhs)
                    ));
                }
                u_disj.push(emit_formula_lean(&sys.unsafe_formula.substitute(
                    &step_maps[k],
                    &empty_nodes,
                    Some(&tk),
                )));
            }
            format!("({})", u_disj.join(" ∨ "))
        }
    };

    let quant = if is_sat { "∃" } else { "∀" };
    write!(out, "  {quant} (").unwrap();
    for (i, (bname, _, _)) in all_binders.iter().enumerate() {
        if i > 0 {
            write!(out, " ").unwrap();
        }
        write!(out, "{bname}").unwrap();
    }
    writeln!(out, " : R),").unwrap();

    let mut box_conjuncts = Vec::with_capacity(all_binders.len());
    for (bname, lo, hi) in &all_binders {
        box_conjuncts.push(format!(
            "(TF.le {} {bname} ∧ TF.le {bname} {})",
            format_lean_rat_call(*lo),
            format_lean_rat_call(*hi)
        ));
    }
    let box_str = if box_conjuncts.is_empty() {
        "True".to_string()
    } else {
        box_conjuncts.join(" ∧\n    ")
    };
    let phys_str = if eq_hyps.is_empty() {
        "True".to_string()
    } else {
        eq_hyps.join(" ∧\n    ")
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
