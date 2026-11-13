//! SMT-LIB2 emitters for `--dialect smt2-exp` (`QF_NRA + exp`) and `--dialect dreal-ode` (`define-ode`).

use std::collections::BTreeMap;
use std::fmt::Write;

use crate::ast::{ sanitize_ident, CmpOp, Dialect, Expr, Formula, InitSpec, TranMethod};
use crate::stamp::{OdeState, StampedBody, StampedSystem, StampedVar, TaggedConstraint};

/// Format an `f64` strictly as an SMT-LIB 2.6 `Real` term without `1e-...` identifier ambiguity.
pub fn format_smt2_real(v: f64) -> String {
    if !v.is_finite() {
        return "0.0".to_string();
    }
    if v == 0.0 {
        return "0.0".to_string();
    }
    if v < 0.0 {
        return format!("(- {})", format_smt2_real(-v));
    }
    if (1.0e-3..1.0e9).contains(&v) {
        let mut s = format!("{v:.12}");
        while s.ends_with('0') {
            s.pop();
        }
        if s.ends_with('.') {
            s.push('0');
        }
        return s;
    }
    // Scientific range: represent exactly via rational power-of-10 scaling `(/ mantissa 10^k)` or `(* mantissa 10^k)`
    let sci = format!("{v:.14e}");
    if let Some((mant_str, exp_str)) = sci.split_once('e') {
        if let Ok(exp10) = exp_str.parse::<i32>() {
            let mut mant = mant_str.to_string();
            while mant.contains('.') && mant.ends_with('0') {
                mant.pop();
            }
            if mant.ends_with('.') {
                mant.push('0');
            }
            if !mant.contains('.') {
                mant.push_str(".0");
            }
            if exp10 >= 0 {
                let mut pow = String::from("1");
                for _ in 0..(exp10 as usize) {
                    pow.push('0');
                }
                pow.push_str(".0");
                return format!("(* {mant} {pow})");
            } else {
                let mut pow = String::from("1");
                for _ in 0..((-exp10) as usize) {
                    pow.push('0');
                }
                pow.push_str(".0");
                return format!("(/ {mant} {pow})");
            }
        }
    }
    format!("{v:.12}")
}

fn emit_expr_smt2(e: &Expr, allow_log: bool) -> Result<String, String> {
    match e {
        Expr::Num(v) => Ok(format_smt2_real(*v)),
        Expr::Var(name) => Ok(name.clone()),
        Expr::NodeVolt(n) => Ok(format!("v_{}", sanitize_ident(n))),
        Expr::Time => Ok("t".to_string()),
        Expr::Neg(a) => Ok(format!("(- {})", emit_expr_smt2(a, allow_log)?)),
        Expr::Add(a, b) => Ok(format!(
            "(+ {} {})",
            emit_expr_smt2(a, allow_log)?,
            emit_expr_smt2(b, allow_log)?
        )),
        Expr::Sub(a, b) => Ok(format!(
            "(- {} {})",
            emit_expr_smt2(a, allow_log)?,
            emit_expr_smt2(b, allow_log)?
        )),
        Expr::Mul(a, b) => Ok(format!(
            "(* {} {})",
            emit_expr_smt2(a, allow_log)?,
            emit_expr_smt2(b, allow_log)?
        )),
        Expr::Div(a, b) => Ok(format!(
            "(/ {} {})",
            emit_expr_smt2(a, allow_log)?,
            emit_expr_smt2(b, allow_log)?
        )),
        Expr::Exp(a) => Ok(format!("(exp {})", emit_expr_smt2(a, allow_log)?)),
        Expr::Ln1pExp(a) => {
            if allow_log {
                Ok(format!("(log (+ 1.0 (exp {})))", emit_expr_smt2(a, allow_log)?))
            } else {
                Err("internal error: unlowered Ln1pExp in pure-exp dialect".to_string())
            }
        }
    }
}

fn emit_formula_smt2(f: &Formula, allow_log: bool) -> Result<String, String> {
    match f {
        Formula::Cmp { op, lhs, rhs } => Ok(format!(
            "({op} {} {})",
            emit_expr_smt2(lhs, allow_log)?,
            emit_expr_smt2(rhs, allow_log)?
        )),
        Formula::And(items) => {
            if items.is_empty() {
                return Ok("true".to_string());
            }
            if items.len() == 1 {
                return emit_formula_smt2(&items[0], allow_log);
            }
            let mut s = String::from("(and");
            for it in items {
                s.push(' ');
                s.push_str(&emit_formula_smt2(it, allow_log)?);
            }
            s.push(')');
            Ok(s)
        }
        Formula::Or(items) => {
            if items.is_empty() {
                return Ok("false".to_string());
            }
            if items.len() == 1 {
                return emit_formula_smt2(&items[0], allow_log);
            }
            let mut s = String::from("(or");
            for it in items {
                s.push(' ');
                s.push_str(&emit_formula_smt2(it, allow_log)?);
            }
            s.push(')');
            Ok(s)
        }
        Formula::Not(inner) => Ok(format!("(not {})", emit_formula_smt2(inner, allow_log)?)),
    }
}

/// Replace any `Ln1pExp(z)` inside a time-stepped expression with a fresh pure-`exp` variable.
fn lower_step_ln1p(
    e: &Expr,
    step_idx: usize,
    aux_counter: &mut usize,
    extra_vars: &mut Vec<StampedVar>,
    extra_eqs: &mut Vec<TaggedConstraint>,
) -> Expr {
    match e {
        Expr::Num(v) => Expr::Num(*v),
        Expr::Var(s) => Expr::Var(s.clone()),
        Expr::NodeVolt(n) => Expr::NodeVolt(n.clone()),
        Expr::Time => Expr::Time,
        Expr::Neg(a) => Expr::neg(lower_step_ln1p(a, step_idx, aux_counter, extra_vars, extra_eqs)),
        Expr::Add(a, b) => Expr::add(
            lower_step_ln1p(a, step_idx, aux_counter, extra_vars, extra_eqs),
            lower_step_ln1p(b, step_idx, aux_counter, extra_vars, extra_eqs),
        ),
        Expr::Sub(a, b) => Expr::sub(
            lower_step_ln1p(a, step_idx, aux_counter, extra_vars, extra_eqs),
            lower_step_ln1p(b, step_idx, aux_counter, extra_vars, extra_eqs),
        ),
        Expr::Mul(a, b) => Expr::mul(
            lower_step_ln1p(a, step_idx, aux_counter, extra_vars, extra_eqs),
            lower_step_ln1p(b, step_idx, aux_counter, extra_vars, extra_eqs),
        ),
        Expr::Div(a, b) => Expr::div(
            lower_step_ln1p(a, step_idx, aux_counter, extra_vars, extra_eqs),
            lower_step_ln1p(b, step_idx, aux_counter, extra_vars, extra_eqs),
        ),
        Expr::Exp(a) => Expr::exp(lower_step_ln1p(a, step_idx, aux_counter, extra_vars, extra_eqs)),
        Expr::Ln1pExp(a) => {
            let z = lower_step_ln1p(a, step_idx, aux_counter, extra_vars, extra_eqs);
            *aux_counter += 1;
            let y_name = format!("y_sp_s{step_idx}_{}", *aux_counter);
            extra_vars.push(StampedVar {
                name: y_name.clone(),
                lo: 0.0,
                hi: 2000.0,
                comment: format!("Step {step_idx} pure-exp softplus auxiliary"),
            });
            extra_eqs.push(TaggedConstraint {
                comment: format!("Step {step_idx} softplus exp({y_name}) = 1 + exp(z)"),
                formula: Formula::Cmp {
                    op: CmpOp::Eq,
                    lhs: Expr::exp(Expr::var(&y_name)),
                    rhs: Expr::add(Expr::num(1.0), Expr::exp(z)),
                },
            });
            Expr::var(y_name)
        }
    }
}

fn lower_step_formula_ln1p(
    f: &Formula,
    step_idx: usize,
    aux_counter: &mut usize,
    extra_vars: &mut Vec<StampedVar>,
    extra_eqs: &mut Vec<TaggedConstraint>,
) -> Formula {
    match f {
        Formula::Cmp { op, lhs, rhs } => Formula::Cmp {
            op: *op,
            lhs: lower_step_ln1p(lhs, step_idx, aux_counter, extra_vars, extra_eqs),
            rhs: lower_step_ln1p(rhs, step_idx, aux_counter, extra_vars, extra_eqs),
        },
        Formula::And(items) => Formula::And(
            items
                .iter()
                .map(|it| lower_step_formula_ln1p(it, step_idx, aux_counter, extra_vars, extra_eqs))
                .collect(),
        ),
        Formula::Or(items) => Formula::Or(
            items
                .iter()
                .map(|it| lower_step_formula_ln1p(it, step_idx, aux_counter, extra_vars, extra_eqs))
                .collect(),
        ),
        Formula::Not(inner) => Formula::Not(Box::new(lower_step_formula_ln1p(
            inner,
            step_idx,
            aux_counter,
            extra_vars,
            extra_eqs,
        ))),
    }
}

/// Emit a `StampedSystem` in the requested SMT-LIB2 dialect (`Smt2Exp` or `DrealOde`).
pub fn emit_smt2(sys: &StampedSystem, dialect: Dialect) -> Result<String, String> {
    emit_smt2_with_logic(sys, dialect, None)
}

/// Emit a `StampedSystem` in SMT-LIB2 with an optional `(set-logic ...)` override
/// (defaults to `QF_NRA` for `dReal` compatibility; pass `Some("QF_NRAT")` or `Some("ALL")`
/// for `cvc5` / `z3` / `veriT` transcendental pipelines).
pub fn emit_smt2_with_logic(
    sys: &StampedSystem,
    dialect: Dialect,
    logic_override: Option<&str>,
) -> Result<String, String> {
    let logic = logic_override.unwrap_or("QF_NRA");
    let mut out = String::with_capacity(8192);
    writeln!(
        out,
        "; ============================================================================"
    )
    .unwrap();
    writeln!(out, "; Benchmark : {}", sys.title).unwrap();
    if let Some(pdk) = sys.pdk {
        writeln!(out, "; PDK       : {} ({})", pdk, pdk.profile().summary).unwrap();
    }
    writeln!(
        out,
        "; Dialect   : {}",
        match dialect {
            Dialect::Smt2Exp => "smt2-exp (QF_NRA + transcendental exp)",
            Dialect::DrealOde => "dreal-ode (QF_NRA + exp + continuous define-ode)",
            Dialect::Lean4 => "lean4",
        }
    )
    .unwrap();
    writeln!(
        out,
        "; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)"
    )
    .unwrap();
    writeln!(
        out,
        "; ============================================================================"
    )
    .unwrap();
    writeln!(out, "(set-logic {logic})").unwrap();
    writeln!(out, "(set-info :smt-lib-version 2.6)").unwrap();
    if let Some(exp) = sys.expected {
        writeln!(out, "(set-info :status {})", exp.as_smt2_str()).unwrap();
    }
    writeln!(out).unwrap();

    if !sys.params.is_empty() {
        writeln!(out, "; --- Continuous Parameter / Defect / Litho Uncertainty Box ---").unwrap();
        for p in &sys.params {
            writeln!(out, "(declare-fun {} () Real)", p.name).unwrap();
            writeln!(
                out,
                "(assert (and (>= {} {}) (<= {} {})))",
                p.name,
                format_smt2_real(p.lo),
                p.name,
                format_smt2_real(p.hi)
            )
            .unwrap();
        }
        writeln!(out).unwrap();
    }

    match (&sys.body, dialect) {
        (StampedBody::Algebraic { vars, constraints }, _) => {
            emit_algebraic_body(&mut out, vars, constraints, &sys.unsafe_formula)?;
        }
        (
            StampedBody::Ode {
                static_vars,
                static_constraints,
                states,
                dt,
                steps,
                method,
            },
            Dialect::Smt2Exp,
        ) => {
            emit_discretized_ode_smt2(
                &mut out,
                static_vars,
                static_constraints,
                states,
                *dt,
                *steps,
                *method,
                &sys.unsafe_formula,
            )?;
        }
        (
            StampedBody::Ode {
                static_vars,
                static_constraints,
                states,
                dt,
                steps,
                ..
            },
            Dialect::DrealOde,
        ) => {
            emit_native_dreal_ode(
                &mut out,
                static_vars,
                static_constraints,
                states,
                *dt * (*steps as f64),
                &sys.unsafe_formula,
            )?;
        }
        (_, Dialect::Lean4) => {
            return Err("use `emit_lean` for `Dialect::Lean4`".to_string());
        }
    }

    writeln!(out).unwrap();
    writeln!(out, "(check-sat)").unwrap();
    writeln!(out, "(exit)").unwrap();
    Ok(out)
}

fn emit_algebraic_body(
    out: &mut String,
    vars: &[StampedVar],
    constraints: &[TaggedConstraint],
    unsafe_formula: &Formula,
) -> Result<(), String> {
    writeln!(out, "; --- State & Auxiliary Variables ---").unwrap();
    for v in vars {
        writeln!(out, "; {}", v.comment).unwrap();
        writeln!(out, "(declare-fun {} () Real)", v.name).unwrap();
        writeln!(
            out,
            "(assert (and (>= {} {}) (<= {} {})))",
            v.name,
            format_smt2_real(v.lo),
            v.name,
            format_smt2_real(v.hi)
        )
        .unwrap();
    }
    writeln!(out).unwrap();

    writeln!(out, "; --- Constitutive & Conservation Laws (MNA / PCB EM / TCAD) ---").unwrap();
    for c in constraints {
        writeln!(out, "; {}", c.comment).unwrap();
        writeln!(out, "(assert {})", emit_formula_smt2(&c.formula, false)?).unwrap();
    }
    writeln!(out).unwrap();

    writeln!(out, "; --- Negated Safety Specification (.unsafe) ---").unwrap();
    writeln!(out, "(assert {})", emit_formula_smt2(unsafe_formula, false)?).unwrap();
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn emit_discretized_ode_smt2(
    out: &mut String,
    static_vars: &[StampedVar],
    static_constraints: &[TaggedConstraint],
    states: &[OdeState],
    dt: f64,
    steps: usize,
    method: TranMethod,
    unsafe_formula: &Formula,
) -> Result<(), String> {
    if !static_vars.is_empty() {
        writeln!(out, "; --- Time-Invariant Geometry & Interconnect Variables ---").unwrap();
        for v in static_vars {
            writeln!(out, "; {}", v.comment).unwrap();
            writeln!(out, "(declare-fun {} () Real)", v.name).unwrap();
            writeln!(
                out,
                "(assert (and (>= {} {}) (<= {} {})))",
                v.name,
                format_smt2_real(v.lo),
                v.name,
                format_smt2_real(v.hi)
            )
            .unwrap();
        }
        for c in static_constraints {
            writeln!(out, "; {}", c.comment).unwrap();
            writeln!(out, "(assert {})", emit_formula_smt2(&c.formula, false)?).unwrap();
        }
        writeln!(out).unwrap();
    }

    writeln!(
        out,
        "; --- Implicit {} Trajectory Unrolling ({steps} steps, dt = {dt:.4e} s) ---",
        match method {
            TranMethod::BackwardEuler => "Backward-Euler",
            TranMethod::Trapezoidal => "Trapezoidal",
        }
    )
    .unwrap();

    let empty_nodes = BTreeMap::new();
    let mut step_vars_maps: Vec<BTreeMap<String, Expr>> = Vec::with_capacity(steps + 1);
    for k in 0..=steps {
        let mut map = BTreeMap::new();
        for st in states {
            let sk = format!("{}_s{k}", st.name);
            writeln!(out, "(declare-fun {sk} () Real)").unwrap();
            writeln!(
                out,
                "(assert (and (>= {sk} {}) (<= {sk} {})))",
                format_smt2_real(st.lo),
                format_smt2_real(st.hi)
            )
            .unwrap();
            map.insert(st.name.clone(), Expr::var(sk));
        }
        step_vars_maps.push(map);
    }
    writeln!(out).unwrap();

    writeln!(out, "; --- Initial State Set X_0 ---").unwrap();
    let mut aux_counter = 0usize;
    for st in states {
        let s0 = format!("{}_s0", st.name);
        match &st.init {
            InitSpec::Interval(lo, hi) => {
                writeln!(
                    out,
                    "(assert (and (>= {s0} {}) (<= {s0} {})))",
                    format_smt2_real(*lo),
                    format_smt2_real(*hi)
                )
                .unwrap();
            }
            InitSpec::Exact(expr) => {
                let mut ev = Vec::new();
                let mut eq = Vec::new();
                let sub = expr.substitute(&step_vars_maps[0], &empty_nodes, Some(&Expr::num(0.0)));
                let low = lower_step_ln1p(&sub, 0, &mut aux_counter, &mut ev, &mut eq);
                for v in ev {
                    writeln!(out, "(declare-fun {} () Real)", v.name).unwrap();
                    writeln!(
                        out,
                        "(assert (and (>= {} {}) (<= {} {})))",
                        v.name,
                        format_smt2_real(v.lo),
                        v.name,
                        format_smt2_real(v.hi)
                    )
                    .unwrap();
                }
                for c in eq {
                    writeln!(out, "(assert {})", emit_formula_smt2(&c.formula, false)?).unwrap();
                }
                writeln!(out, "(assert (= {s0} {}))", emit_expr_smt2(&low, false)?).unwrap();
            }
        }
    }
    writeln!(out).unwrap();

    let mut unsafe_disjuncts: Vec<Formula> = Vec::with_capacity(steps);
    let mut extra_vars: Vec<StampedVar> = Vec::new();
    let mut extra_eqs: Vec<TaggedConstraint> = Vec::new();
    let mut step_eqs: Vec<(usize, String, Expr, Expr)> = Vec::new();

    for k in 1..=steps {
        let tk = Expr::num((k as f64) * dt);
        let tk_prev = Expr::num(((k - 1) as f64) * dt);
        for st in states {
            let xk = Expr::var(format!("{}_s{k}", st.name));
            let xk_prev = Expr::var(format!("{}_s{}", st.name, k - 1));
            let fk_raw = st.rhs.substitute(&step_vars_maps[k], &empty_nodes, Some(&tk));
            let fk = lower_step_ln1p(&fk_raw, k, &mut aux_counter, &mut extra_vars, &mut extra_eqs);

            let rhs = match method {
                TranMethod::BackwardEuler => Expr::add(xk_prev, Expr::mul(Expr::num(dt), fk)),
                TranMethod::Trapezoidal => {
                    let fk_prev_raw =
                        st.rhs
                            .substitute(&step_vars_maps[k - 1], &empty_nodes, Some(&tk_prev));
                    let fk_prev = lower_step_ln1p(
                        &fk_prev_raw,
                        k,
                        &mut aux_counter,
                        &mut extra_vars,
                        &mut extra_eqs,
                    );
                    Expr::add(
                        xk_prev,
                        Expr::mul(Expr::num(0.5 * dt), Expr::add(fk_prev, fk)),
                    )
                }
            };
            step_eqs.push((k, st.name.clone(), xk, rhs));
        }

        let u_sub = unsafe_formula.substitute(&step_vars_maps[k], &empty_nodes, Some(&tk));
        let u_low = lower_step_formula_ln1p(
            &u_sub,
            k,
            &mut aux_counter,
            &mut extra_vars,
            &mut extra_eqs,
        );
        unsafe_disjuncts.push(u_low);
    }

    if !extra_vars.is_empty() {
        writeln!(out, "; --- Step-Local Transcendental Softplus Auxiliaries ---").unwrap();
        for v in &extra_vars {
            writeln!(out, "(declare-fun {} () Real)", v.name).unwrap();
            writeln!(
                out,
                "(assert (and (>= {} {}) (<= {} {})))",
                v.name,
                format_smt2_real(v.lo),
                v.name,
                format_smt2_real(v.hi)
            )
            .unwrap();
        }
        for c in &extra_eqs {
            writeln!(out, "(assert {})", emit_formula_smt2(&c.formula, false)?).unwrap();
        }
        writeln!(out).unwrap();
    }

    writeln!(out, "; --- Discrete-Time Nonlinear DAE / ODE Step Equations ---").unwrap();
    for (k, sname, lhs, rhs) in &step_eqs {
        writeln!(
            out,
            "; Step {k}: {sname}"
        )
        .unwrap();
        writeln!(
            out,
            "(assert (= {} {}))",
            emit_expr_smt2(lhs, false)?,
            emit_expr_smt2(rhs, false)?
        )
        .unwrap();
    }
    writeln!(out).unwrap();

    writeln!(
        out,
        "; --- Existential Unsafe Trajectory Violation Across Steps 1..={steps} ---"
    )
    .unwrap();
    let any_unsafe = Formula::Or(unsafe_disjuncts);
    writeln!(out, "(assert {})", emit_formula_smt2(&any_unsafe, false)?).unwrap();
    Ok(())
}

fn emit_native_dreal_ode(
    out: &mut String,
    static_vars: &[StampedVar],
    static_constraints: &[TaggedConstraint],
    states: &[OdeState],
    t_horizon: f64,
    unsafe_formula: &Formula,
) -> Result<(), String> {
    if !static_vars.is_empty() {
        writeln!(out, "; --- Time-Invariant Geometry & Interconnect Variables ---").unwrap();
        for v in static_vars {
            writeln!(out, "; {}", v.comment).unwrap();
            writeln!(out, "(declare-fun {} () Real)", v.name).unwrap();
            writeln!(
                out,
                "(assert (and (>= {} {}) (<= {} {})))",
                v.name,
                format_smt2_real(v.lo),
                v.name,
                format_smt2_real(v.hi)
            )
            .unwrap();
        }
        for c in static_constraints {
            writeln!(out, "; {}", c.comment).unwrap();
            writeln!(out, "(assert {})", emit_formula_smt2(&c.formula, true)?).unwrap();
        }
        writeln!(out).unwrap();
    }

    writeln!(out, "; --- Continuous ODE Flow Variables & Initial/Final Endpoints ---").unwrap();
    writeln!(out, "(declare-fun t () Real)").unwrap();
    writeln!(out, "(declare-fun t_0 () Real)").unwrap();
    writeln!(out, "(declare-fun t_t () Real)").unwrap();
    writeln!(out, "(declare-fun tau_hit () Real)").unwrap();
    writeln!(
        out,
        "(assert (and (= t_0 0.0) (>= tau_hit 0.0) (<= tau_hit {}) (= t_t tau_hit)))",
        format_smt2_real(t_horizon)
    )
    .unwrap();

    let mut end_map = BTreeMap::new();
    let empty_nodes = BTreeMap::new();
    for st in states {
        let n = &st.name;
        writeln!(out, "; {}", st.comment).unwrap();
        writeln!(out, "(declare-fun {n} () Real)").unwrap();
        writeln!(out, "(declare-fun {n}_0 () Real)").unwrap();
        writeln!(out, "(declare-fun {n}_t () Real)").unwrap();
        writeln!(
            out,
            "(assert (and (>= {n}_0 {}) (<= {n}_0 {})))",
            format_smt2_real(st.lo),
            format_smt2_real(st.hi)
        )
        .unwrap();
        writeln!(
            out,
            "(assert (and (>= {n}_t {}) (<= {n}_t {})))",
            format_smt2_real(st.lo),
            format_smt2_real(st.hi)
        )
        .unwrap();
        end_map.insert(n.clone(), Expr::var(format!("{n}_t")));
    }
    writeln!(out).unwrap();

    // Initial state assertions
    let mut init_map = BTreeMap::new();
    for st in states {
        init_map.insert(st.name.clone(), Expr::var(format!("{}_0", st.name)));
    }
    writeln!(out, "; --- Initial Condition X_0 ---").unwrap();
    for st in states {
        let s0 = format!("{}_0", st.name);
        match &st.init {
            InitSpec::Interval(lo, hi) => {
                writeln!(
                    out,
                    "(assert (and (>= {s0} {}) (<= {s0} {})))",
                    format_smt2_real(*lo),
                    format_smt2_real(*hi)
                )
                .unwrap();
            }
            InitSpec::Exact(e) => {
                let sub = e.substitute(&init_map, &empty_nodes, Some(&Expr::num(0.0)));
                writeln!(out, "(assert (= {s0} {}))", emit_expr_smt2(&sub, true)?).unwrap();
            }
        }
    }
    writeln!(out).unwrap();

    // `(define-ode flow_1 ((= d/dt[t] 1.0) (= d/dt[x_i] f_i(x, p, t)) ...))`
    writeln!(out, "; --- Continuous Nonlinear Circuit ODE Flow ---").unwrap();
    writeln!(out, "(define-ode flow_1 (").unwrap();
    writeln!(out, "  (= d/dt[t] 1.0)").unwrap();
    for st in states {
        writeln!(
            out,
            "  (= d/dt[{}] {})",
            st.name,
            emit_expr_smt2(&st.rhs, true)?
        )
        .unwrap();
    }
    writeln!(out, "))").unwrap();
    writeln!(out).unwrap();

    // Trajectory invariant + integral link `(= [t_t x1_t ...] (integral 0.0 tau_hit [t_0 x1_0 ...] flow_1))`
    write!(out, "(assert (= [t_t").unwrap();
    for st in states {
        write!(out, " {}_t", st.name).unwrap();
    }
    write!(out, "] (integral 0.0 tau_hit [t_0").unwrap();
    for st in states {
        write!(out, " {}_0", st.name).unwrap();
    }
    writeln!(out, "] flow_1)))").unwrap();

    for st in states {
        writeln!(
            out,
            "(assert (forall_t 1 [0.0 tau_hit] (and (>= {}_t {}) (<= {}_t {}))))",
            st.name,
            format_smt2_real(st.lo),
            st.name,
            format_smt2_real(st.hi)
        )
        .unwrap();
    }
    writeln!(out).unwrap();

    writeln!(
        out,
        "; --- Existential Unsafe Reachability at Hit Time tau_hit in [0, {}] ---",
        format_smt2_real(t_horizon)
    )
    .unwrap();
    let unsafe_end = unsafe_formula.substitute(&end_map, &empty_nodes, Some(&Expr::var("tau_hit")));
    writeln!(out, "(assert {})", emit_formula_smt2(&unsafe_end, true)?).unwrap();
    Ok(())
}
