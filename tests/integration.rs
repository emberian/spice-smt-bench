use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;

use spice2smt::ast::{CmpOp, Dialect, ExpectedStatus, Expr, Formula, InitSpec, TranMethod};
use spice2smt::pdk::PdkId;
use spice2smt::stamp::{StampedBody, StampedSystem};
use spice2smt::{compile_str, parser, paving, stamp};

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn check_balanced_parens(smt2: &str, label: &str) {
    let mut depth = 0i64;
    for line in smt2.lines() {
        let code = match line.find(';') {
            Some(idx) => &line[..idx],
            None => line,
        };
        for ch in code.chars() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    assert!(depth >= 0, "unbalanced `)` in {label}");
                }
                _ => {}
            }
        }
    }
    assert_eq!(depth, 0, "unclosed `(` in {label}");
}

#[test]
fn test_all_pdk_profiles_load() {
    assert_eq!(PdkId::all().len(), 6);
    for pdk in PdkId::all() {
        let prof = pdk.profile();
        assert!(!prof.default_models.is_empty());
        assert!(prof.vdd_nom_v > 0.0);
        assert!(prof.lg_nom_nm > 0.0);
    }
    assert_eq!(PdkId::parse("gaa2n"), Some(PdkId::Gt2n));
    assert_eq!(PdkId::parse("ASAP7"), Some(PdkId::Asap7));
    assert_eq!(PdkId::parse("sg13g2"), Some(PdkId::IhpSg13g2));
}

#[test]
fn test_all_benchmark_decks_compile_all_dialects() {
    let sp_dir = repo_root().join("benchmarks/sp");
    let mut decks: Vec<PathBuf> = fs::read_dir(&sp_dir)
        .expect("benchmarks/sp directory exists")
        .filter_map(|e| e.ok().map(|x| x.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "sp"))
        .collect();
    decks.sort();
    assert!(
        decks.len() >= 18,
        "expected at least 18 graded benchmark decks, found {}",
        decks.len()
    );

    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;

    for path in &decks {
        let name = path.file_name().unwrap().to_str().unwrap();
        let src = fs::read_to_string(path).unwrap();
        let parsed = parser::parse_deck(&src).unwrap_or_else(|e| panic!("{name}: {e}"));
        match parsed.expected {
            Some(ExpectedStatus::Sat) => sat_count += 1,
            Some(ExpectedStatus::Unsat) => unsat_count += 1,
            None => panic!("{name}: missing `.expected sat|unsat`"),
        }

        let smt_exp = compile_str(&src, Dialect::Smt2Exp, None, None)
            .unwrap_or_else(|e| panic!("{name} smt2-exp: {e}"));
        check_balanced_parens(&smt_exp, &format!("{name} [smt2-exp]"));
        assert!(
            smt_exp.contains("(set-logic ALL)"),
            "{name} missing ALL logic"
        );
        assert!(
            !smt_exp.contains("(log "),
            "{name} smt2-exp must be 100% pure `exp` without `log`"
        );

        let smt_dreal = compile_str(&src, Dialect::DrealOde, None, None)
            .unwrap_or_else(|e| panic!("{name} dreal-ode: {e}"));
        check_balanced_parens(&smt_dreal, &format!("{name} [dreal-ode]"));
        if matches!(parsed.mode, spice2smt::ast::AnalysisMode::Tran { .. }) {
            assert!(
                smt_dreal.contains("(define-ode flow_1"),
                "{name} dreal-ode missing define-ode"
            );
            assert!(
                smt_dreal.contains("(forall_t 1"),
                "{name} dreal-ode missing forall_t"
            );
        }

        let lean_out = compile_str(&src, Dialect::Lean4, None, Some("BenchSpec"))
            .unwrap_or_else(|e| panic!("{name} lean4: {e}"));
        assert!(
            lean_out.contains("def BenchSpec {R : Type} (TF : TranscendentalField R) : Prop :="),
            "{name} lean4 missing header"
        );
    }

    assert!(sat_count >= 5, "expected >= 5 SAT counterexample decks");
    assert!(unsat_count >= 13, "expected >= 13 UNSAT safety decks");
}

#[test]
fn test_verify_paving_sound_and_rejects_tampering() {
    let sp_src =
        fs::read_to_string(repo_root().join("benchmarks/sp/01_diode_clipper_pvt.sp")).unwrap();
    let json_src =
        fs::read_to_string(repo_root().join("examples/diode_clipper_paving.json")).unwrap();
    let deck = parser::parse_deck(&sp_src).unwrap();
    let sys = stamp::stamp_deck(&deck).unwrap();
    let pav = paving::parse_paving_json(&json_src).unwrap();
    let rep = paving::verify_paving(&sys, &pav).expect("diode clipper paving must verify");
    assert_eq!(rep.total_leaves, 3);
    assert_eq!(rep.unsafe_refuted_leaves, 1);
    assert_eq!(rep.physics_refuted_leaves, 2);

    // Tamper 1: claim the entire root box refutes `.unsafe` without splitting -> must fail!
    let bad_root = paving::parse_paving_json(r#"{"type": "leaf", "reason": "unsafe_false"}"#)
        .unwrap();
    assert!(
        paving::verify_paving(&sys, &bad_root).is_err(),
        "unsound single-leaf paving must be rejected"
    );

    // Tamper 2: split out of bounds -> must fail!
    let bad_split = paving::parse_paving_json(
        r#"{"type": "split", "var": "v_out", "mid": 99.0, "left": {"type": "leaf", "reason": "unsafe_false"}, "right": {"type": "leaf", "reason": "unsafe_false"}}"#,
    )
    .unwrap();
    assert!(
        paving::verify_paving(&sys, &bad_split).is_err(),
        "out-of-bounds split point must be rejected"
    );
}

#[test]
fn test_coupled_inductors_and_1d_pn_baseline() {
    let coupled_deck = r#"
* Coupled transformer transient test
.expected unsat
.mode tran dt=1.0e-9 steps=3 method=trap
.param k_cpl [0.5, 0.8]
.bound v(sec) [-5.0, 5.0]
.init v(sec) = 0.0
Vpri pri 0 STEP(base=0.0 step=1.0 t0=0.5e-9 tau=0.2e-9)
L1   pri 0   10.0e-9 Rser=0.5
L2   sec 0   10.0e-9 Rser=0.5
K12  L1  L2  {k_cpl}
Csec sec 0   50.0e-12
Rsec sec 0   100.0
.unsafe v(sec) > 4.0
.end
"#;
    let smt = compile_str(coupled_deck, Dialect::Smt2Exp, None, None).unwrap();
    check_balanced_parens(&smt, "coupled_inductors");
    assert!(smt.contains("M_L1_L2"));

    let pn1d_deck = r#"
* Baseline 1D p-n junction Poisson check
.pdk sky130
.expected unsat
.mode dc
.param q_dope [1.2, 1.4]
.param temp_k [273.0, 360.0]
.tcad_pn_1d junc1 nodes=7 length_um=0.6 junction_um=0.25 q_dope={q_dope} nd_plus=50.0 temp={temp_k} v_bias=1.2
.unsafe E_junc_v_per_um_junc1 > 80.0
.end
"#;
    let smt_pn = compile_str(pn1d_deck, Dialect::Smt2Exp, None, None).unwrap();
    check_balanced_parens(&smt_pn, "pn1d_baseline");
}

/// Relative residual against the magnitudes of additive equation terms. This
/// prevents ampere-scale tolerances from accepting unsolved pF/nH equations.
fn equation_scale(lhs: &Expr, rhs: &Expr, env: &BTreeMap<String, f64>, t: f64) -> Result<f64, String> {
    fn magnitude(e: &Expr, env: &BTreeMap<String, f64>, t: f64) -> Result<f64, String> {
        match e {
            Expr::Add(a,b) | Expr::Sub(a,b) => Ok(magnitude(a,env,t)? + magnitude(b,env,t)?),
            Expr::Neg(a) => magnitude(a,env,t),
            Expr::Mul(a,b) => Ok(magnitude(a,env,t)? * magnitude(b,env,t)?),
            Expr::Div(a,b) => Ok(magnitude(a,env,t)? / b.eval_f64(env,t)?.abs()),
            _ => Ok(e.eval_f64(env,t)?.abs()),
        }
    }
    Ok(magnitude(lhs,env,t)?.max(magnitude(rhs,env,t)?).max(1e-10))
}

fn equation_residual(lhs: &Expr, rhs: &Expr, env: &BTreeMap<String, f64>, t: f64) -> Result<f64, String> {
    let lv = lhs.eval_f64(env,t)?;
    let rv = rhs.eval_f64(env,t)?;
    let scale = equation_scale(lhs,rhs,env,t)?;
    if lv.is_nan() || rv.is_nan() || !lv.is_finite() || !rv.is_finite() || !scale.is_finite() {
        return Err("non-finite equation operand".into());
    }
    Ok((lv-rv)/scale)
}

/// Damped Newton-Raphson solver on a `StampedSystem`'s equality constraints for witness / non-vacuity checks.
fn solve_equality_system(
    var_names: &[String],
    init_guess: &BTreeMap<String, f64>,
    fixed_params: &BTreeMap<String, f64>,
    eqs: &[(Expr, Expr)],
    t: f64,
) -> Option<BTreeMap<String, f64>> {
    let n = var_names.len();
    assert_eq!(n, eqs.len(), "square system expected: vars={n}, eqs={}", eqs.len());
    let mut env = fixed_params.clone();
    for vn in var_names {
        let val = init_guess.get(vn).copied().unwrap_or(0.2);
        env.insert(vn.clone(), val);
    }

    let scales: Vec<_> = eqs.iter().map(|(l,r)| equation_scale(l,r,&env,t).map(|v| v.clamp(1e-7,1.0))).collect::<Result<_,_>>().ok()?;
    let eval_res = |e_map: &BTreeMap<String, f64>| -> Result<Vec<f64>, String> {
        let mut r = Vec::with_capacity(n);
        for ((lhs, rhs), scale) in eqs.iter().zip(&scales) {
            let residual = (lhs.eval_f64(e_map, t)? - rhs.eval_f64(e_map, t)?) / scale;
            if !residual.is_finite() { return Err("non-finite Newton residual".into()); }
            r.push(residual);
        }
        Ok(r)
    };

    for _iter in 0..400 {
        let res = eval_res(&env).ok()?;
        let max_r = res.iter().fold(0.0f64, |a, b| a.max(b.abs()));
        if max_r < 1.0e-8 {
            return Some(env);
        }

        // Finite-difference Jacobian J (n x n)
        let mut jac = vec![vec![0.0; n]; n];
        for (j, vj) in var_names.iter().enumerate() {
            let orig = env[vj];
            let eps = 1.0e-7 * orig.abs().max(1.0);
            env.insert(vj.clone(), orig + eps);
            let rp = eval_res(&env).ok()?;
            env.insert(vj.clone(), orig);
            for i in 0..n {
                jac[i][j] = (rp[i] - res[i]) / eps;
            }
        }

        // Gaussian elimination with partial pivoting for J * dx = -res
        let mut aug = vec![vec![0.0; n + 1]; n];
        for i in 0..n {
            for j in 0..n {
                aug[i][j] = jac[i][j];
            }
            aug[i][n] = -res[i];
        }
        for col in 0..n {
            let mut piv = col;
            for row in (col + 1)..n {
                if aug[row][col].abs() > aug[piv][col].abs() {
                    piv = row;
                }
            }
            if aug[piv][col].abs() < 1.0e-28 {
                eprintln!("  [diag-piv] singular col={col} ({}) piv={}", var_names[col], aug[piv][col]);
                return None;
            }
            aug.swap(col, piv);
            let diag = aug[col][col];
            for val in &mut aug[col][col..=n] {
                *val /= diag;
            }
            let pivot = aug[col][col..=n].to_vec();
            for (row, values) in aug.iter_mut().enumerate().take(n) {
                if row != col {
                    let f = values[col];
                    for (value, pivot_value) in values[col..=n].iter_mut().zip(&pivot) {
                        *value -= f * pivot_value;
                    }
                }
            }
        }

        let step: Vec<f64> = (0..n).map(|i| aug[i][n]).collect();
        // Keep exact Newton direction `-J^{-1} F(x)`; choose initial `alpha <= 1` so voltage jumps <= 0.25V
        let mut max_vstep = 0.0f64;
        for (j, vj) in var_names.iter().enumerate() {
            if vj.starts_with("v_") || vj.starts_with("psi_") || vj.starts_with("phin_") {
                max_vstep = max_vstep.max(step[j].abs());
            }
        }
        let mut alpha = if max_vstep > 0.25 {
            0.25 / max_vstep
        } else {
            1.0
        };

        // Backtracking line search on L_inf residual norm (or accept damped Newton step)
        let base_env = env.clone();
        let mut accepted = false;
        let min_alpha = alpha / 64.0;
        while alpha >= min_alpha {
            for (j, vj) in var_names.iter().enumerate() {
                env.insert(vj.clone(), base_env[vj] + alpha * step[j]);
            }
            if let Ok(rn) = eval_res(&env) {
                let nr = rn.iter().fold(0.0f64, |a, b| a.max(b.abs()));
                if nr.is_finite() && nr < max_r {
                    accepted = true;
                    break;
                }
            }
            alpha *= 0.5;
        }
        if !accepted {
            let damp = (0.25 / max_vstep.max(0.25)).min(0.5);
            for (j, vj) in var_names.iter().enumerate() {
                env.insert(vj.clone(), base_env[vj] + damp * step[j]);
            }
        }
    }
    None
}

fn exact_bernoulli(d: f64) -> f64 {
    if d.abs() < 1.0e-5 {
        let d2 = d * d;
        1.0 - 0.5 * d + d2 / 12.0 - (d2 * d2) / 720.0
    } else {
        d / d.exp_m1()
    }
}

/// Extract equality equations from an algebraic or ODE stamped system and solve at `param_vals`,
/// then independently verify EVERY stamped bound, equality (`|lhs - rhs| <= 1e-8`), and inequality.
fn simulate_stamped(
    sys: &StampedSystem,
    param_vals: &BTreeMap<String, f64>,
    dc_seed: &BTreeMap<String, f64>,
) -> Option<(BTreeMap<String, f64>, bool)> {
    let constraints = match &sys.body { StampedBody::Algebraic {constraints, ..} => constraints, StampedBody::Ode {static_constraints, ..} => static_constraints };
    let mut known = param_vals.clone();
    for _ in 0..constraints.len() {
        let before = known.len();
        for c in constraints {
            if let Formula::Cmp {op: CmpOp::Eq, lhs, rhs} = &c.formula {
                let candidate = match lhs {
                    Expr::Var(n) => rhs.eval_f64(&known, 0.0).ok().map(|v| (n, v)),
                    Expr::Exp(a) => if let Expr::Var(n) = a.as_ref() { rhs.eval_f64(&known, 0.0).ok().map(|v| (n, v.ln())) } else { None },
                    Expr::Mul(a,b) if a == b => if let Expr::Var(n) = a.as_ref() { rhs.eval_f64(&known, 0.0).ok().map(|v| (n, v.sqrt())) } else { None },
                    Expr::Mul(a,b) => if let Expr::Var(n) = a.as_ref() { rhs.eval_f64(&known, 0.0).ok().zip(b.eval_f64(&known, 0.0).ok()).map(|(r,d)| (n, r/d)) } else { None },
                    _ => None,
                };
                if let Some((n, v)) = candidate { if v.is_finite() { known.entry(n.clone()).or_insert(v); } }
            }
        }
        if before == known.len() { break; }
    }
    let param_vals = &known;
    match &sys.body {
        StampedBody::Algebraic { vars, constraints } => {
            // Separate closed-form TCAD auxiliary/Slotboom variables (`E_*`, `Bp_*`, `phin_*`,
            // `id_leak_ua_*`, `I_stack_ua_*`, `psi_mid_*`) during Newton iteration on `(psi, T_ch)`
            // so the Jacobian is strictly elliptic/non-singular, then verify EVERY unmodified
            // stamped constraint (including raw `phin` continuity and `Bp*(E-1)=Delta`) on `sol`!
            let mut sg_edges: Vec<(String, String, Expr)> = Vec::new();
            let mut cont_edges: Vec<Expr> = Vec::new();
            let mut phin_vars: Vec<String> = Vec::new();
            let mut explicit_defs: Vec<(String, Expr)> = Vec::new();
            let mut primary_eqs: Vec<(Expr, Expr)> = Vec::new();
            let mut all_eqs: Vec<(Expr, Expr)> = Vec::new();
            let mut ineqs: Vec<Formula> = Vec::new();

            for v in vars {
                if v.name.starts_with("phin_") {
                    phin_vars.push(v.name.clone());
                }
            }

            for c in constraints {
                if let Formula::Cmp {
                    op: CmpOp::Eq,
                    lhs,
                    rhs,
                } = &c.formula
                {
                    all_eqs.push((lhs.clone(), rhs.clone()));
                    if (c.comment == "Electron SG continuity" || c.comment == "Hole SG continuity") && vars.iter().filter(|v| v.name.starts_with("phin_") || v.name.starts_with("phip_")).all(|v| param_vals.contains_key(&v.name)) { continue; }
                    if lhs.eval_f64(param_vals, 0.0).is_ok() && rhs.eval_f64(param_vals, 0.0).is_ok() { continue; }
                    if let Expr::Mul(a, b) = lhs {
                        if a == b { if let Expr::Var(name) = a.as_ref() {
                            explicit_defs.push((name.clone(), Expr::sqrt(rhs.clone()))); continue;
                        } }
                    }
                    if let Expr::Var(name) = lhs {
                        if name.starts_with("ic_") || name.starts_with("ib_") || (name.starts_with("i_") && c.comment.contains("current")) {
                            explicit_defs.push((name.clone(), rhs.clone())); continue;
                        }
                    }
                    if let (Expr::Exp(y), Expr::Add(_, ez)) = (lhs, rhs) {
                        if let (Expr::Var(name), Expr::Exp(z)) = (y.as_ref(), ez.as_ref()) {
                            if name.starts_with("y_sp_") {
                                explicit_defs.push((name.clone(), Expr::ln1p_exp((**z).clone())));
                                continue;
                            }
                        }
                    }
                    if let (Expr::Var(ename), Expr::Exp(delta_box)) = (lhs, rhs) {
                        if let Some(rest) = ename.strip_prefix("E_pn_") {
                            sg_edges.push((ename.clone(),format!("Bp_pn_{rest}"),(**delta_box).clone())); continue;
                        }
                        if let Some(rest) = ename.strip_prefix("E_sg_") {
                            sg_edges.push((
                                ename.clone(),
                                format!("Bp_sg_{rest}"),
                                (**delta_box).clone(),
                            ));
                            continue;
                        }
                        if let Some(rest) = ename.strip_prefix("E_gaa_") {
                            sg_edges.push((
                                ename.clone(),
                                format!("Bp_gaa_{rest}"),
                                (**delta_box).clone(),
                            ));
                            continue;
                        }
                    }
                    if let Expr::Mul(bp_box, _) = lhs {
                        if let Expr::Var(bp_name) = bp_box.as_ref() {
                            if bp_name.starts_with("Bp_sg_") || bp_name.starts_with("Bp_gaa_") || bp_name.starts_with("Bp_pn_") {
                                continue;
                            }
                        }
                    }
                    if c.comment.contains("current continuity") {
                        if cont_edges.is_empty() {
                            cont_edges.push(rhs.clone());
                        }
                        cont_edges.push(lhs.clone());
                        continue;
                    }
                    if let Expr::Var(vname) = lhs {
                        if vname.starts_with("J_a_per_cm2_") || vname.starts_with("E_junc_v_per_um_") || vname.starts_with("id_leak_ua_")
                            || vname.starts_with("I_stack_ua_")
                            || vname.starts_with("psi_mid_")
                        {
                            explicit_defs.push((vname.clone(), rhs.clone()));
                            continue;
                        }
                    }
                    primary_eqs.push((lhs.clone(), rhs.clone()));
                } else {
                    ineqs.push(c.formula.clone());
                }
            }

            let is_eliminated = |name: &str| {
                explicit_defs.iter().any(|(n, _)| n == name) || name.starts_with("E_pn_") || name.starts_with("Bp_pn_") || name.starts_with("E_peak_v_per_um_") || name.starts_with("y_sp_") || name.starts_with("E_sg_")
                    || name.starts_with("Bp_sg_")
                    || name.starts_with("E_gaa_")
                    || name.starts_with("Bp_gaa_")
                    || name.starts_with("phin_")
                    || name.starts_with("id_leak_ua_")
                    || name.starts_with("I_stack_ua_")
                    || name.starts_with("psi_mid_")
            };
            let primary_vnames: Vec<String> = vars
                .iter()
                .filter(|v| !is_eliminated(&v.name) && !param_vals.contains_key(&v.name))
                .map(|v| v.name.clone())
                .collect();

            let solve_with_sg_projection =
                |guess_map: &BTreeMap<String, f64>| -> Option<BTreeMap<String, f64>> {
                    let n = primary_vnames.len();
                    assert_eq!(
                        n,
                        primary_eqs.len(),
                        "square primary system expected for {}: vars={n} ({primary_vnames:?}), eqs={}",
                        sys.title,
                        primary_eqs.len()
                    );
                    let mut env = param_vals.clone();
                    for vn in &primary_vnames {
                        env.insert(vn.clone(), guess_map.get(vn).copied().unwrap_or(0.2));
                    }
                    let refresh_sg = |m: &mut BTreeMap<String, f64>| -> Result<(), String> {
                        for (n, rhs) in &explicit_defs { if let Ok(v) = rhs.eval_f64(m, 0.0) { m.insert(n.clone(), v); } }
                        for (ename, bpname, delta_expr) in &sg_edges {
                            let d = delta_expr.eval_f64(m, 0.0)?;
                            m.insert(ename.clone(), d.exp());
                            m.insert(bpname.clone(), exact_bernoulli(d));
                        }
                        if !cont_edges.is_empty() && !phin_vars.is_empty() {
                            // Extract thermal voltage `vt` and drain bias `vds` from device setup:
                            // `vt = KB_OVER_Q * T` where T is `T_ch_*` if present, else `temp_k`
                            let kb_q = 8.617_333_262e-5_f64;
                            let temp = m
                                .iter()
                                .find(|(k, _)| k.starts_with("T_ch_"))
                                .map(|(_, v)| *v)
                                .or_else(|| m.get("temp_k").copied())
                                .unwrap_or(300.0);
                            let vt = kb_q * temp;
                            // Probe `vds` from the last edge `cont_edges[last]` where `phin_R = vds`:
                            // setting `phin_{last} = 0` makes `edge = G_last * (1 - exp(-vds/vt))`,
                            // and comparing against `G_last` from an interior edge gives exact `G_e`!
                            // Even simpler: in `13` vds=0.70, in `14a` vds=0.65, in `14b` vds=0.75;
                            // we can read `u_end = exp(-vds/vt)` directly with zero hardcoding by probing
                            // `cont_edges.last()` at `phin_last = 0.0` and `phin_last = vt * ln(2)`!
                            // Let `J(0) = G * (1 - u_end)` and `J(vt*ln2) = G * (0.5 - u_end)`:
                            // Then `J(0) - J(vt*ln2) = 0.5 * G` => `G = 2 * (J(0) - J(vt*ln2))`,
                            // and `u_end = 1.0 - J(0) / G`!
                            let n_edges = cont_edges.len();
                            let ln2_vt = vt * 2.0_f64.ln();
                            let mut inv_g = Vec::with_capacity(n_edges);
                            let mut u_end = 0.0f64;
                            for (e, edge_expr) in cont_edges.iter().enumerate() {
                                let g_e = if e == 0 {
                                    // phin_0 = 0 (fixed), phin_1 = phin_vars[0]
                                    m.insert(phin_vars[0].clone(), ln2_vt);
                                    2.0 * edge_expr.eval_f64(m, 0.0)?
                                } else if e + 1 < n_edges {
                                    m.insert(phin_vars[e - 1].clone(), 0.0);
                                    m.insert(phin_vars[e].clone(), ln2_vt);
                                    2.0 * edge_expr.eval_f64(m, 0.0)?
                                } else {
                                    let pv = &phin_vars[e - 1];
                                    m.insert(pv.clone(), 0.0);
                                    let j0 = edge_expr.eval_f64(m, 0.0)?;
                                    m.insert(pv.clone(), ln2_vt);
                                    let j1 = edge_expr.eval_f64(m, 0.0)?;
                                    let g = 2.0 * (j0 - j1);
                                    u_end = (1.0 - j0 / g).max(1.0e-300);
                                    g
                                };
                                inv_g.push(1.0 / g_e.max(1.0e-300));
                            }
                            let w_total: f64 = inv_g.iter().sum();
                            for (idx, pv) in phin_vars.iter().enumerate() {
                                let i_node = idx + 1;
                                let w_lt: f64 = inv_g[..i_node].iter().sum();
                                let w_ge: f64 = inv_g[i_node..].iter().sum();
                                let u_i = (u_end * w_lt + w_ge) / w_total;
                                m.insert(pv.clone(), -vt * u_i.ln());
                            }
                        }
                        for c in constraints {
                            if c.comment == "Exact maximum field magnitude" {
                                if let Formula::Or(choices) = &c.formula {
                                    let mut peak = f64::NEG_INFINITY;
                                    let mut name = None;
                                    for f in choices {
                                        if let Formula::Cmp {lhs:Expr::Var(n),rhs,..} = f {
                                            peak = peak.max(rhs.eval_f64(m,0.0)?); name = Some(n);
                                        }
                                    }
                                    if let Some(name) = name { m.insert(name.clone(),peak); }
                                }
                            }
                        }
                        for (vname, rhs_expr) in &explicit_defs {
                            let val = rhs_expr.eval_f64(m, 0.0)?;
                            m.insert(vname.clone(), val);
                        }
                        Ok(())
                    };
                    let mut scale_env = env.clone();
                    refresh_sg(&mut scale_env).ok()?;
                    let scales: Vec<_> = primary_eqs.iter().map(|(l,r)| equation_scale(l,r,&scale_env,0.0).map(|v| v.clamp(1e-7,1.0))).collect::<Result<_,_>>().ok()?;
                    let eval_res = |m: &BTreeMap<String, f64>| -> Result<Vec<f64>, String> {
                        let mut m_full = m.clone();
                        refresh_sg(&mut m_full)?;
                        let mut r = Vec::with_capacity(n);
                        for ((lhs, rhs), scale) in primary_eqs.iter().zip(&scales) {
                            let residual = (lhs.eval_f64(&m_full, 0.0)? - rhs.eval_f64(&m_full, 0.0)?) / scale;
                            if !residual.is_finite() { return Err("non-finite projected Newton residual".into()); }
                            r.push(residual);
                        }
                        Ok(r)
                    };

                    for _iter in 0..400 {
                        let res = eval_res(&env).ok()?;
                        let max_r = res.iter().fold(0.0f64, |a, b| a.max(b.abs()));
                        if max_r < 1.0e-10 {
                            refresh_sg(&mut env).ok()?;
                            return Some(env);
                        }
                        let mut jac = vec![vec![0.0; n]; n];
                        for (j, vj) in primary_vnames.iter().enumerate() {
                            let orig = env[vj];
                            let eps = 1.0e-7 * orig.abs().max(1.0);
                            env.insert(vj.clone(), orig + eps);
                            let rp = eval_res(&env).ok()?;
                            env.insert(vj.clone(), orig);
                            for i in 0..n {
                                jac[i][j] = (rp[i] - res[i]) / eps;
                            }
                        }
                        let mut aug = vec![vec![0.0; n + 1]; n];
                        for i in 0..n {
                            for j in 0..n {
                                aug[i][j] = jac[i][j];
                            }
                            aug[i][n] = -res[i];
                        }
                        for col in 0..n {
                            let mut piv = col;
                            for row in (col + 1)..n {
                                if aug[row][col].abs() > aug[piv][col].abs() {
                                    piv = row;
                                }
                            }
                            if aug[piv][col].abs() < 1.0e-28 {
                                eprintln!(
                                    "  [diag-piv] {}: singular col={col} ({})",
                                    sys.title, primary_vnames[col]
                                );
                                return None;
                            }
                            aug.swap(col, piv);
                            let diag = aug[col][col];
                            for val in &mut aug[col][col..=n] {
                                *val /= diag;
                            }
                            let pivot = aug[col][col..=n].to_vec();
                            for (row, values) in aug.iter_mut().enumerate().take(n) {
                                if row != col {
                                    let f = values[col];
                                    for (value, pivot_value) in values[col..=n].iter_mut().zip(&pivot) {
                                        *value -= f * pivot_value;
                                    }
                                }
                            }
                        }
                        let step: Vec<f64> = (0..n).map(|i| aug[i][n]).collect();
                        let mut max_vstep = 0.0f64;
                        for (j, vj) in primary_vnames.iter().enumerate() {
                            if vj.starts_with("v_")
                                || vj.starts_with("psi_")
                                || vj.starts_with("phin_")
                            {
                                max_vstep = max_vstep.max(step[j].abs());
                            } else if vj.starts_with("T_ch_") {
                                max_vstep = max_vstep.max(step[j].abs() / 80.0);
                            }
                        }
                        let mut alpha = if max_vstep > 0.20 {
                            0.20 / max_vstep
                        } else {
                            1.0
                        };
                        let base_env = env.clone();
                        let mut accepted = false;
                        let min_alpha = alpha / 64.0;
                        while alpha >= min_alpha {
                            for (j, vj) in primary_vnames.iter().enumerate() {
                                env.insert(vj.clone(), base_env[vj] + alpha * step[j]);
                            }
                            if let Ok(rn) = eval_res(&env) {
                                let nr = rn.iter().fold(0.0f64, |a, b| a.max(b.abs()));
                                if nr.is_finite() && nr < max_r {
                                    accepted = true;
                                    break;
                                }
                            }
                            alpha *= 0.5;
                        }
                        if !accepted {
                            let damp = (0.20 / max_vstep.max(0.20)).min(0.5);
                            for (j, vj) in primary_vnames.iter().enumerate() {
                                env.insert(vj.clone(), base_env[vj] + damp * step[j]);
                            }
                        }
                    }
                    None
                };

            let mut guess = dc_seed.clone();
            for v in vars {
                guess.entry(v.name.clone()).or_insert_with(|| {
                    if v.name.starts_with("y_sp_")
                        || v.name.starts_with("su_")
                        || v.name.starts_with("seeff_")
                        || v.name.starts_with("lam_")
                    {
                        1.2
                    } else if v.name.starts_with("psi_") {
                        0.45
                    } else if v.name.starts_with("phin_") {
                        let parts: Vec<&str> = v.name.split('_').collect();
                        let i_slice = parts
                            .get(2)
                            .and_then(|s| s.parse::<usize>().ok())
                            .unwrap_or(1);
                        0.12 * (i_slice as f64)
                    } else if v.name.starts_with("Z0_") {
                        50.0
                    } else if v.name.starts_with("Zdiff_") {
                        100.0
                    } else if v.name.starts_with("T_ch_") {
                        340.0
                    } else if v.name.starts_with("id_leak_")
                        || v.name.starts_with("istack_")
                        || v.name.starts_with("p_diss_")
                    {
                        0.001
                    } else {
                        v.bounds.map_or(0.0, |(lo, hi)| (0.5 * (lo + hi)).clamp(-2.0, 2.0))
                    }
                });
            }
            let Some(sol) = solve_with_sg_projection(&guess) else {
                eprintln!("  [diag] {}: Newton did not converge", sys.title);
                return None;
            };
            // Verify EVERY original stamped equality (including E_e and Bp_e*(E_e-1)=Delta_e!)
            for (lhs, rhs) in &all_eqs {
                let lv = lhs.eval_f64(&sol, 0.0).ok()?;
                let rv = rhs.eval_f64(&sol, 0.0).ok()?;
                if !lv.is_finite() || !rv.is_finite() || equation_residual(lhs, rhs, &sol, 0.0).ok()?.abs() > 1.0e-7 {
                    eprintln!(
                        "  [diag] {}: equality residual too large: |{lv} - {rv}|",
                        sys.title
                    );
                    return None;
                }
            }
            for v in vars {
                let val = sol[&v.name];
                if !val.is_finite() || v.bounds.is_some_and(|(lo, hi)| val < lo - 1e-7 || val > hi + 1e-7) {
                    eprintln!(
                        "  [diag] {}: var `{}` = {} out of bounds [{}, {}]",
                        sys.title, v.name, val, v.bounds.map_or(f64::NEG_INFINITY, |b| b.0), v.bounds.map_or(f64::INFINITY, |b| b.1)
                    );
                    return None;
                }
            }
            for iq in &ineqs {
                if !iq.eval_f64(&sol, 0.0).ok()? {
                    eprintln!("  [diag] {}: inequality violated: {iq:?}", sys.title);
                    return None;
                }
            }
            let is_unsafe = sys.unsafe_formula.eval_f64(&sol, 0.0).ok()?;
            Some((sol, is_unsafe))
        }
        StampedBody::Ode {
            static_vars,
            static_constraints,
            states,
            dt,
            steps,
            method,
        } => {
            let mut full_params = param_vals.clone();
            if !static_vars.is_empty() {
                let sv_names: Vec<String> = static_vars.iter().filter(|v| !param_vals.contains_key(&v.name)).map(|v| v.name.clone()).collect();
                let mut s_eqs = Vec::new();
                for c in static_constraints {
                    if let Formula::Cmp {
                        op: CmpOp::Eq,
                        lhs,
                        rhs,
                    } = &c.formula
                    {
                        if lhs.eval_f64(param_vals, 0.0).is_err() || rhs.eval_f64(param_vals, 0.0).is_err() { s_eqs.push((lhs.clone(), rhs.clone())); }
                    }
                }
                let mut s_guess = BTreeMap::new();
                for v in static_vars {
                    s_guess.insert(
                        v.name.clone(),
                        if v.name.starts_with("Z0_") {
                            50.0
                        } else if v.name.starts_with("Zdiff_") {
                            100.0
                        } else if v.name.starts_with("M_")
                            || v.name.starts_with("Ltot_")
                            || v.name.starts_with("Lm_")
                        {
                            1.0e-9
                        } else if v.name.starts_with("Ctot_") || v.name.starts_with("Cm_") {
                            2.0e-12
                        } else {
                            1.5
                        },
                    );
                }
                let s_sol =
                    solve_equality_system(&sv_names, &s_guess, param_vals, &s_eqs, 0.0)?;
                for (k, v) in s_sol {
                    full_params.insert(k, v);
                }
            }

            let st_names: Vec<String> = states.iter().map(|s| s.name.clone()).collect();
            let mut cur_state = full_params.clone();
            for st in states {
                let x0 = match &st.init {
                    InitSpec::Interval(lo, hi) => 0.5 * (lo + hi),
                    InitSpec::Exact(e) => e.eval_f64(&cur_state, 0.0).ok()?,
                };
                cur_state.insert(st.name.clone(), x0);
            }

            let validate = |env: &BTreeMap<String,f64>, t: f64| -> Option<()> {
                if env.values().any(|v| v.is_nan() || !v.is_finite()) { return None; }
                for v in static_vars {
                    let x = env[&v.name];
                    if v.bounds.is_some_and(|(lo,hi)| x < lo-1e-7 || x > hi+1e-7) { return None; }
                }
                for c in static_constraints {
                    let valid = match &c.formula {
                        Formula::Cmp {op:CmpOp::Eq,lhs,rhs} => equation_residual(lhs,rhs,env,t).ok()?.abs() <= 1e-7,
                        f => f.eval_f64(env,t).ok()?,
                    };
                    if !valid { return None; }
                }
                for st in states {
                    let x = env[&st.name];
                    if x < st.lo-1e-7 || x > st.hi+1e-7 || !st.rhs.eval_f64(env,t).ok()?.is_finite() { return None; }
                }
                Some(())
            };
            validate(&cur_state,0.0)?;
            let mut hit_unsafe = sys.unsafe_formula.eval_f64(&cur_state, 0.0).ok()?;
            for k in 1..=*steps {
                let tk = (k as f64) * (*dt);
                let tk_prev = ((k - 1) as f64) * (*dt);
                let mut step_eqs = Vec::with_capacity(states.len());
                for st in states {
                    let x_prev = cur_state[&st.name];
                    let rhs_step = match method {
                        TranMethod::BackwardEuler => {
                            Expr::add(Expr::num(x_prev), Expr::mul(Expr::num(*dt), st.rhs.clone()))
                        }
                        TranMethod::Trapezoidal => {
                            let f_prev = st.rhs.eval_f64(&cur_state, tk_prev).ok()?;
                            Expr::add(
                                Expr::num(x_prev + 0.5 * (*dt) * f_prev),
                                Expr::mul(Expr::num(0.5 * (*dt)), st.rhs.clone()),
                            )
                        }
                    };
                    step_eqs.push((Expr::var(&st.name), rhs_step));
                }
                let sol_k =
                    solve_equality_system(&st_names, &cur_state, &full_params, &step_eqs, tk)?;
                for st in states {
                    let val = sol_k[&st.name];
                    if !val.is_finite() || val < st.lo - 1e-7 || val > st.hi + 1e-7 {
                        eprintln!("state bound: {}={val} at step {k}", st.name);
                        return None;
                    }
                }
                validate(&sol_k,tk)?;
                for (lhs,rhs) in &step_eqs {
                    if equation_residual(lhs,rhs,&sol_k,tk).ok()?.abs() > 1e-7 { return None; }
                }
                if sys.unsafe_formula.eval_f64(&sol_k, tk).ok()? {
                    hit_unsafe = true;
                }
                cur_state = sol_k;
            }
            Some((cur_state, hit_unsafe))
        }
    }
}

#[test]
fn test_physical_nonvacuity_and_sat_witnesses_across_all_19_benchmarks() {
    let sp_dir = repo_root().join("benchmarks/sp");
    let mut decks: Vec<PathBuf> = fs::read_dir(&sp_dir)
        .unwrap()
        .filter_map(|e| e.ok().map(|x| x.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "sp"))
        .collect();
    decks.sort();

    let mut failures = Vec::new();
    for path in &decks {
        let fname = path.file_name().unwrap().to_str().unwrap();
        let src = fs::read_to_string(path).unwrap();
        let deck = parser::parse_deck(&src).unwrap();
        let sys = stamp::stamp_deck(&deck).unwrap();

        let mut mid_params = BTreeMap::new();
        for p in &sys.params {
            mid_params.insert(p.name.clone(), 0.5 * (p.lo + p.hi));
        }

        match sys.expected.unwrap() {
            ExpectedStatus::Unsat => {
                let mut seed = BTreeMap::new();
                if fname.starts_with("03a_") {
                    seed.insert("v_q".to_string(), 0.68);
                    seed.insert("v_qb".to_string(), 0.04);
                } else if fname.starts_with("04b_") {
                    seed.insert("v_vdd".to_string(), 3.0);
                    seed.insert("v_ref".to_string(), 1.20);
                    seed.insert("v_e0".into(), 0.55);
                    seed.insert("v_vc1".into(), 2.5);
                    seed.insert("v_ve2".to_string(), 0.60);
                    seed.insert("i_Vsup".to_string(), -0.0006);
                } else if fname.starts_with("05_") {
                    seed.insert("v_sup".to_string(), 0.90);
                    seed.insert("v_nwell".to_string(), 0.90);
                    seed.insert("v_psub".to_string(), 0.0);
                }
                match simulate_stamped(&sys, &mid_params, &seed) {
                    Some((sol, false)) => {
                        if fname.starts_with("13_") {
                            let leak = sol["id_leak_ua_fin7"];
                            assert!(
                                leak > 0.0 && leak < 0.000010,
                                "13 FinFET off-state leakage must be positive and < 10 pA/um, got {leak}"
                            );
                        }
                        if fname.starts_with("14a_") {
                            let tch = sol["T_ch_gaa2n"];
                            assert!(
                                tch > 315.0 && tch < 410.0,
                                "14a GAA channel temperature must self-heat (> T_amb) yet stay < 410 K, got {tch}"
                            );
                        }
                        println!("  [OK UNSAT non-vacuous] {fname}");
                    }
                    Some((sol, true)) => {
                        failures.push(format!("{fname}: expected UNSAT, but nominal solution hit .unsafe ({sol:?})"));
                    }
                    None => {
                        failures.push(format!("{fname}: failed non-vacuity convergence"));
                    }
                }
            }
            ExpectedStatus::Sat => {
                let mut p = mid_params.clone();
                let mut seed = BTreeMap::new();
                if fname.starts_with("03b_") {
                    p.insert("dtfin_nm".into(), 0.0);
                } else if fname.starts_with("04a_") {
                    seed.insert("v_vdd".to_string(), 3.0);
                    seed.insert("v_ref".to_string(), 0.001);
                    seed.insert("v_e0".to_string(), 0.0);
                    seed.insert("v_ve2".to_string(), 0.0);
                    seed.insert("v_vc1".to_string(), 2.999);
                    for i in 1..=4 {
                        seed.insert(format!("y_sp_Mp1_f_{i}"), 1.0e-4);
                        seed.insert(format!("y_sp_Mp1_r_{i}"), 1.0e-4);
                        seed.insert(format!("y_sp_Mp2_f_{i}"), 1.0e-4);
                        seed.insert(format!("y_sp_Mp2_r_{i}"), 1.0e-4);
                    }
                } else if fname.starts_with("09b_") {
                    p.insert("dw_etch".to_string(), -40.0e-6);
                    p.insert("dh_lam".to_string(), 16.0e-6);
                    p.insert("t_cu".to_string(), 29.0e-6);
                    p.insert("er_lam".to_string(), 3.88);
                } else if fname.starts_with("12a_") {
                    p.insert("er_p".to_string(), 4.68);
                    p.insert("er_n".to_string(), 3.82);
                    p.insert("slot_width".to_string(), 0.012);
                } else if fname.starts_with("14b_") {
                    p.insert("dtns_nm".to_string(), 0.55);
                    p.insert("tamb_k".to_string(), 382.0);
                    p.insert("rth_kw".to_string(), 1.35e6);
                    seed.insert("T_ch_gaa2n".to_string(), 435.0);
                }

                match simulate_stamped(&sys, &p, &seed) {
                    Some((sol, true)) => {
                        if fname.starts_with("14b_") {
                            let tch = sol["T_ch_gaa2n"];
                            assert!(
                                tch > 410.0,
                                "14b GAA thermal runaway witness must satisfy T_ch > 410 K, got {tch}"
                            );
                        }
                        println!("  [OK SAT witness]       {fname}");
                    }
                    Some((sol, false)) => {
                        failures.push(format!("{fname}: expected SAT witness, but .unsafe was false ({sol:?})"));
                    }
                    None => {
                        failures.push(format!("{fname}: failed SAT witness convergence"));
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "Benchmark physical checks failed:\n{}", failures.join("\n"));
}

#[test]
fn test_corner_soundness_and_scientific_literal_precision() {
    // 1. Verify exact exponent handling without clamping in Lean and SMT-LIB2 emitters
    let lean_tiny = spice2smt::emit_lean::format_lean_rat_call(1.0e-30);
    assert_eq!(lean_tiny, "(TF.ofRat 1 1000000000000000000000000000000)");
    let smt_ns = spice2smt::emit_smt2::format_smt2_real(1.375e-9);
    assert_eq!(smt_ns, "0.000000001375");

    // 2. Verify all 2^5 = 32 vertices of 09a's 5D DFM polytope stay strictly safe (Z0 in [45,55], Zdiff in [90,110])
    let src_09a =
        fs::read_to_string(repo_root().join("benchmarks/sp/09a_pcb_microstrip_dfm_unsat.sp"))
            .unwrap();
    let sys_09a = stamp::stamp_deck(&parser::parse_deck(&src_09a).unwrap()).unwrap();
    for mask in 0..32usize {
        let mut p = BTreeMap::new();
        for (bit, param) in sys_09a.params.iter().enumerate() {
            let v = if ((mask >> bit) & 1) == 0 {
                param.lo
            } else {
                param.hi
            };
            p.insert(param.name.clone(), v);
        }
        let (sol, is_unsafe) =
            simulate_stamped(&sys_09a, &p, &BTreeMap::new()).expect("09a corner must solve");
        assert!(
            !is_unsafe,
            "09a corner mask={mask} violated impedance spec: Z0={}, Zdiff={}",
            sol["Z0_tl50"], sol["Zdiff_diff90"]
        );
    }

    // 3. Verify extremal corners of 04b guarded SiGe HBT reference have inhabited DC equilibria > 0.40V
    let src_04b =
        fs::read_to_string(repo_root().join("benchmarks/sp/04b_ihp_sige_bandgap_guarded_unsat.sp"))
            .unwrap();
    let sys_04b = stamp::stamp_deck(&parser::parse_deck(&src_04b).unwrap()).unwrap();
    for &(vdd, temp_k, deg_ge) in &[(2.7, 373.0, 0.090), (3.3, 273.0, 0.080)] {
        let mut p = BTreeMap::new();
        p.insert("vdd".to_string(), vdd);
        p.insert("temp_k".to_string(), temp_k);
        p.insert("deg_ge".to_string(), deg_ge);
        let mut seed = BTreeMap::new();
        seed.insert("v_vdd".to_string(), vdd);
        seed.insert("v_ref".to_string(), 1.20);
        seed.insert("v_e0".into(), 0.55);
        seed.insert("v_vc1".into(), vdd-0.5);
        seed.insert("v_ve2".to_string(), 0.60);
        seed.insert("i_Vsup".to_string(), -0.0006);
        let (sol, is_unsafe) =
            simulate_stamped(&sys_04b, &p, &seed).expect("04b extremal corner must have DC equilibrium");
        assert!(
            !is_unsafe && sol["v_ref"] > 0.45,
            "04b corner ({vdd}, {temp_k}, {deg_ge}) unsafe or collapsed: v_ref={}",
            sol["v_ref"]
        );
    }

    // 4. Verify all 2^4 = 16 corners of 13 (ASAP7 2D FinFET) and 14a (gt2n GAA electro-thermal) stay strictly safe!
    for rel in [
        "benchmarks/sp/13_asap7_finfet_2d_poisson_qconfinement.sp",
        "benchmarks/sp/14a_gt2n_gaa_nanosheet_electrothermal_unsat.sp",
    ] {
        let src = fs::read_to_string(repo_root().join(rel)).unwrap();
        let sys = stamp::stamp_deck(&parser::parse_deck(&src).unwrap()).unwrap();
        for mask in 0..16usize {
            let mut p = BTreeMap::new();
            for (bit, param) in sys.params.iter().enumerate() {
                let v = if ((mask >> bit) & 1) == 0 {
                    param.lo
                } else {
                    param.hi
                };
                p.insert(param.name.clone(), v);
            }
            let (sol, is_unsafe) =
                simulate_stamped(&sys, &p, &BTreeMap::new()).expect("TCAD corner must converge");
            assert!(
                !is_unsafe,
                "{rel} corner mask={mask} unexpectedly hit .unsafe: {sol:?}"
            );
        }
    }
}

#[test]
fn rejects_malformed_transient_and_source_inputs() {
    for config in ["dt=0 steps=1", "dt=-1n steps=1", "dt=1n steps=0",
        "dt=1n steps=1.5", "dt=1n steps=1 method=typo", "dt=1n steps=1 extra=1",
        "dt=1n dt=2n steps=1"] {
        assert!(parser::parse_deck(&format!(".mode tran {config}\n.unsafe v(a)>1\n")).is_err(), "{config}");
    }
    for literal in ["NaN", "inf", "-inf", "1e999", "1e308t"] {
        assert!(parser::parse_spice_number(literal).is_err(), "{literal}");
    }
    for source in ["V1 a 0 DC 1 extra", "V1 a 0 1 extra", "L1 a 0 1n typo=1"] {
        assert!(parser::parse_deck(&format!("{source}\n.unsafe v(a)>1\n")).is_err(), "{source}");
    }
    let duplicate = ".mode tran dt=1n steps=1\nV1 a 0 DC 1\nV2 a 0 DC 2\nR1 a b 1k\nC1 b 0 1p\n.unsafe v(b)>1\n";
    assert!(compile_str(duplicate, Dialect::Smt2Exp, None, None).is_err());
}

#[test]
fn discrete_safety_includes_initial_state_and_logic_matches_dialect() {
    let source = ".mode tran dt=1n steps=1\nR1 a 0 1k\nC1 a 0 1p\n.init v(a) = 2\n.unsafe v(a)>1\n";
    let smt = compile_str(source, Dialect::Smt2Exp, None, None).unwrap();
    assert!(smt.contains("(or (> v_a_s0 1.0) (> v_a_s1 1.0))"));
    let lean = compile_str(source, Dialect::Lean4, None, None).unwrap();
    assert!(lean.contains("(∃ k : Nat, k ≤ 1 ∧ (TF.lt TF.one (state k 0)))"));
    let ode = compile_str(source, Dialect::DrealOde, None, None).unwrap();
    assert!(ode.contains("(set-logic QF_NRA_ODE)"));
}

#[test]
fn certified_transcendental_intervals_cover_reference_values() {
    use spice2smt::paving::Iv;
    for x in [-1025.0, -745.0, -700.0, -30.0, -1.0, -0.5, 0.0, 0.5, 1.0, 30.0, 700.0, 710.0] {
        let enclosure = Iv::exact(x).exp();
        // Library values are a numerical cross-check, not the enclosure's justification.
        assert!(enclosure.lo <= x.exp() && x.exp() <= enclosure.hi, "exp({x}): {enclosure:?}");
        let softplus = Iv::exact(x).ln1p_exp();
        let reference = x.max(0.0) + (-x.abs()).exp().ln_1p();
        assert!(softplus.lo <= reference && reference <= softplus.hi, "softplus({x}): {softplus:?}");
    }
    for index in ["-1", "0.5", "1e999"] {
        let json = format!("{{\"type\":\"leaf\",\"reason\":\"constraint_violated\",\"constraint_index\":{index}}}");
        assert!(paving::parse_paving_json(&json).is_err());
    }
}

#[test]
fn rejects_unresolved_references_and_constant_cycles() {
    for source in [
        ".const a = b\n.const b = a\nR1 a 0 1k\n.unsafe v(a)>1\n",
        "R1 a 0 {missing}\n.unsafe v(a)>1\n",
        "R1 a 0 {time+1}\n.unsafe v(a)>1\n",
        "R1 a 0 {1e308*1e308}\n.unsafe v(a)>1\n",
        "R1 a 0 1k\n.bound v(typo) [0,1]\n.unsafe v(a)>1\n",
        "R1 a 0 1k\nR1 b 0 1k\n.unsafe v(a)>1\n",
    ] {
        assert!(compile_str(source, Dialect::Smt2Exp, None, None).is_err(), "{source}");
    }
    let forward = ".const a = b\n.const b = 1000\nR1 a 0 {a}\n.unsafe v(a)>1\n";
    assert!(compile_str(forward, Dialect::Smt2Exp, None, None).is_ok());
}

#[test]
fn shortest_decimal_rationals_preserve_distinct_values() {
    use spice2smt::numeral::exact_f64_to_rat;
    assert_eq!(exact_f64_to_rat(0.1).unwrap(), (false, "1".into(), "10".into()));
    assert_ne!(spice2smt::emit_smt2::format_smt2_real(1.0000000000004), spice2smt::emit_smt2::format_smt2_real(1.0000000000002));
    for value in [f64::INFINITY, f64::NEG_INFINITY, f64::NAN] {
        assert!(exact_f64_to_rat(value).is_err());
    }
    let (_, numerator, denominator) = exact_f64_to_rat(f64::from_bits(1)).unwrap();
    assert_eq!(numerator, "1");
    assert_eq!(denominator.len(), 324);
}

#[test]
fn committed_artifacts_are_fresh() {
    let root = repo_root();
    let bundle = fs::read_to_string(root.join("lean/SpiceSmtBench/TargetsGenerated.lean")).unwrap();
    let mut generated_defs = String::new();
    let mut paths: Vec<_> = fs::read_dir(root.join("benchmarks/sp")).unwrap()
        .map(|e| e.unwrap().path()).filter(|p| p.extension().is_some_and(|e| e == "sp")).collect();
    paths.sort();
    for path in paths {
        let source = fs::read_to_string(&path).unwrap();
        let stem = path.file_stem().unwrap().to_str().unwrap();
        for (dialect, directory) in [(Dialect::Smt2Exp, "smt2-exp"), (Dialect::DrealOde, "dreal-ode")] {
            let generated = compile_str(&source, dialect, None, None).unwrap();
            let committed = fs::read_to_string(root.join(format!("benchmarks/smt2/{directory}/{stem}.smt2"))).unwrap();
            assert_eq!(generated, committed, "stale artifact: {directory}/{stem}");
        }
        let sys = stamp::stamp_deck(&parser::parse_deck(&source).unwrap()).unwrap();
        generated_defs.push_str(&spice2smt::emit_lean::emit_lean_def(&sys, &format!("Bench_{stem}"), false));
        generated_defs.push('\n');
    }
    let (_, body) = bundle.split_once("namespace SpiceSmtBench.Targets\n\n").unwrap();
    assert_eq!(body, format!("{generated_defs}end SpiceSmtBench.Targets\n"), "stale Lean definitions");
    let source = fs::read_to_string(root.join("benchmarks/sp/01_diode_clipper_pvt.sp")).unwrap();
    let sys = stamp::stamp_deck(&parser::parse_deck(&source).unwrap()).unwrap();
    let certificate = paving::generate_paving(&sys, &[("v_out".into(), 0.84), ("i_D1".into(), 0.005)]).unwrap();
    assert_eq!(format!("{}\n", certificate.to_json()), fs::read_to_string(root.join("examples/diode_clipper_paving.json")).unwrap());
}

#[test]
fn series_esr_remains_active_without_esl() {
    let source = ".mode tran dt=1n steps=1\nV1 a 0 DC 1\nC_MLCC1 a 0 C0=1u Cmin=0 Vsat=1 ESR=2 ESL=0\n.unsafe vc_C_MLCC1>2\n";
    let sys = stamp::stamp_deck(&parser::parse_deck(source).unwrap()).unwrap();
    let StampedBody::Ode { states, .. } = sys.body else { panic!("expected ODE") };
    let state = states.iter().find(|s| s.name == "vc_C_MLCC1").expect("series capacitor voltage state");
    let env = BTreeMap::from([("vc_C_MLCC1".into(), 0.0)]);
    assert!((state.rhs.eval_f64(&env, 0.0).unwrap() - 500_000.0).abs() < 1e-8);
}

#[test]
fn scr_guarded_full_box_and_unguarded_latch() {
    let source = fs::read_to_string(repo_root().join("benchmarks/sp/05_cmos_scr_latchup_holding.sp")).unwrap();
    let sys = stamp::stamp_deck(&parser::parse_deck(&source).unwrap()).unwrap();
    let StampedBody::Algebraic { vars, .. } = &sys.body else { panic!("expected SCR DC stamp") };
    assert!(vars.iter().filter(|v| v.name == "i_Vsup" || v.name.starts_with("ic_") || v.name.starts_with("ib_")).all(|v| v.bounds.is_none()), "SCR proof must not assume current clamps");
    let splits = ["v_nwell", "v_psub", "v_ep", "v_en", "temp_k"].map(String::from);
    let boxes = paving::prove_unsat(&sys, &splits, 8191).expect("global SCR protection proof without current bounds");
    println!("SCR global proof: {boxes} boxes");
    let source = source.replace(".expected unsat", ".expected sat").replace("[0.70, 0.88]", "[1.2, 1.2]")
        .replace("[6.0, 14.0]", "[150, 150]").replace("[5.0, 12.0]", "[120, 120]")
        .replace("R_ep sup ep 20", "R_ep sup ep 1").replace("R_en en 0 20", "R_en en 0 1");
    let sys = stamp::stamp_deck(&parser::parse_deck(&source).unwrap()).unwrap();
    let params = BTreeMap::from([("vsupply".into(),1.2),("r_well".into(),150.0),("r_sub".into(),120.0),("temp_k".into(),300.0)]);
    let seed = BTreeMap::from([("v_sup".into(),1.2),("v_nwell".into(),0.4),("v_psub".into(),0.8),("v_ep".into(),1.15),("v_en".into(),0.05)]);
    let (sol, unsafe_root) = simulate_stamped(&sys, &params, &seed).expect("unguarded latched root");
    assert!(unsafe_root && -sol["i_Vsup"] > 0.005, "SCR latch witness: {sol:?}");
}

#[test]
fn pcb_full_box_interval_certificate() {
    let source = fs::read_to_string(repo_root().join("benchmarks/sp/09a_pcb_microstrip_dfm_unsat.sp")).unwrap();
    let sys = stamp::stamp_deck(&parser::parse_deck(&source).unwrap()).unwrap();
    let splits: Vec<_> = sys.params.iter().map(|p| p.name.clone()).collect();
    let boxes = paving::prove_unsat(&sys, &splits, 4095).expect("global PCB impedance enclosure");
    println!("PCB global proof: {boxes} boxes");
}

#[test]
fn bandgap_twins_have_nominal_and_startup_witnesses() {
    let root = repo_root().join("benchmarks/sp");
    let a = fs::read_to_string(root.join("04a_ihp_sige_bandgap_trojan_sat.sp")).unwrap();
    let b = fs::read_to_string(root.join("04b_ihp_sige_bandgap_guarded_unsat.sp")).unwrap();
    let core = |s: &str| s.lines().filter(|l| l.starts_with("Mp") || l.starts_with('Q') || l.starts_with('R')).collect::<Vec<_>>().join("\n");
    assert_eq!(core(&a), core(&b));
    let params = BTreeMap::from([("vdd".into(),3.0),("temp_k".into(),300.0),("deg_ge".into(),0.085)]);
    let high = BTreeMap::from([("v_vdd".into(),3.0),("v_ref".into(),1.2),("v_e0".into(),0.55),("v_ve2".into(),0.60),("v_vc1".into(),2.4)]);
    for source in [&a, &b] {
        let sys = stamp::stamp_deck(&parser::parse_deck(source).unwrap()).unwrap();
        let (sol, unsafe_root) = simulate_stamped(&sys, &params, &high).expect("nominal bandgap equilibrium");
        assert!(!unsafe_root && (1.18..=1.22).contains(&sol["v_ref"]), "nominal reference: {}", sol["v_ref"]);
    }
    let low = BTreeMap::from([("v_vdd".into(),3.0),("v_ref".into(),0.001),("v_e0".into(),0.0),("v_ve2".into(),0.0),("v_vc1".into(),2.999)]);
    let sys = stamp::stamp_deck(&parser::parse_deck(&a).unwrap()).unwrap();
    assert!(simulate_stamped(&sys, &params, &low).expect("low-current equilibrium").1);
}

#[test]
fn sram_zero_defect_and_pdn_without_mlcc_counterfactuals() {
    let source = fs::read_to_string(repo_root().join("benchmarks/sp/03b_asap7_sram_6t_fin_collapse_sat.sp")).unwrap();
    let sys = stamp::stamp_deck(&parser::parse_deck(&source).unwrap()).unwrap();
    let params = BTreeMap::from([("dtfin_nm".into(),0.0),("dt_fin_pdb".into(),0.0),("dphim".into(),0.0)]);
    let (sol, unsafe_root) = simulate_stamped(&sys, &params, &BTreeMap::new()).expect("zero-defect SRAM");
    assert!(!unsafe_root && sol["v_q"]-sol["v_qb"] > 0.35);
    let source = fs::read_to_string(repo_root().join("benchmarks/sp/11_pcb_pdn_mlcc_derating_droop_ode.sp")).unwrap();
    let source = source.lines().filter(|l| !l.starts_with("C_MLCC1") && !l.contains("vc_C_MLCC1") && !l.contains("i_C_MLCC1")).collect::<Vec<_>>().join("\n");
    let sys = stamp::stamp_deck(&parser::parse_deck(&source).unwrap()).unwrap();
    let params = BTreeMap::from([("r_void".into(),0.028),("v_sat".into(),0.55),("di_step".into(),1.10)]);
    assert!(simulate_stamped(&sys, &params, &BTreeMap::new()).expect("PDN counterfactual trajectory").1, "MLCC removal must breach 0.80 V");
}

#[test]
fn confinement_is_load_bearing_for_leakage() {
    let source = fs::read_to_string(repo_root().join("benchmarks/sp/13_asap7_finfet_2d_poisson_qconfinement.sp")).unwrap();
    let mut sys = stamp::stamp_deck(&parser::parse_deck(&source).unwrap()).unwrap();
    fn remove_confinement(e: &mut Expr) {
        match e {
            Expr::Num(v) if *v == 0.8357 => *v = 0.0,
            Expr::Neg(a) | Expr::Exp(a) | Expr::Sqrt(a) | Expr::Ln1pExp(a) => remove_confinement(a),
            Expr::Add(a,b) | Expr::Sub(a,b) | Expr::Mul(a,b) | Expr::Div(a,b) => { remove_confinement(a); remove_confinement(b); }
            _ => {}
        }
    }
    fn modify(f: &mut Formula) {
        match f {
            Formula::Cmp {lhs,rhs,..} => { remove_confinement(lhs); remove_confinement(rhs); }
            Formula::And(fs) | Formula::Or(fs) => for f in fs { modify(f); },
            Formula::Not(f) => modify(f),
        }
    }
    if let StampedBody::Algebraic {constraints,..} = &mut sys.body { for c in constraints { modify(&mut c.formula); } }
    let p = BTreeMap::from([("dtfin_nm".into(),0.5),("dlg_nm".into(),-1.2),("dphim".into(),-0.02),("temp_k".into(),360.0)]);
    let (sol, unsafe_root) = simulate_stamped(&sys,&p,&BTreeMap::new()).expect("unconfined device equilibrium");
    assert!(unsafe_root, "unconfined leakage must exceed 10 pA/um: {}",sol["id_leak_ua_fin7"]);
}

#[test]
fn guarded_bandgap_full_box_interval_certificate() {
    let source = fs::read_to_string(repo_root().join("benchmarks/sp/04b_ihp_sige_bandgap_guarded_unsat.sp")).unwrap();
    let sys = stamp::stamp_deck(&parser::parse_deck(&source).unwrap()).unwrap();
    let split_vars = ["temp_k", "v_e0", "v_ve2", "v_vc1", "vdd", "deg_ge"].map(String::from);
    let boxes = paving::prove_unsat(&sys,&split_vars,511).expect("global guarded bandgap certificate");
    println!("Bandgap global proof: {boxes} boxes");
}

#[test]
fn contractors_never_close_known_sat_boxes() {
    for unsafe_expr in ["v(a)>0.5", "v(a)*v(a)>0.5", "exp(v(a))>2"] {
        let source = format!(".expected unsat\n.param supply [0,1]\nV1 a 0 DC {{supply}}\nR1 a 0 1k\n.unsafe {unsafe_expr}\n");
        let sys = stamp::stamp_deck(&parser::parse_deck(&source).unwrap()).unwrap();
        assert!(paving::prove_unsat(&sys,&["supply".into()],31).is_err(), "known SAT box was closed: {unsafe_expr}");
    }
}

#[test]
fn coupled_pn_poisson_sg_equilibrium() {
    let source = ".mode dc\n.pdk sky130\n.tcad_pn_1d pn nodes=5 length_um=0.6 junction_um=0.3 q_dope=1 nd_plus=1 temp=300 v_bias=0\n.unsafe E_peak_v_per_um_pn>80\n";
    let sys = stamp::stamp_deck(&parser::parse_deck(source).unwrap()).unwrap();
    let mut fixed = BTreeMap::new();
    for i in 1..4 { fixed.insert(format!("phin_pn_{i}"),0.0); fixed.insert(format!("phip_pn_{i}"),0.0); }
    let seed = BTreeMap::from([("psi_pn_1".into(),-0.25),("psi_pn_2".into(),0.20),("psi_pn_3".into(),0.30)]);
    let (sol, unsafe_root) = simulate_stamped(&sys,&fixed,&seed).expect("coupled PN equilibrium");
    assert!(!unsafe_root && sol["J_a_per_cm2_pn"].abs()<1e-9);
    assert!(sol["E_peak_v_per_um_pn"] > 0.1);
}

#[test]
fn derivative_helpers_cover_exact_method_samples_and_keep_ring_compact() {
    for (method, first) in [("trap", 0), ("be", 1)] {
        let source = format!(".mode tran dt=1n steps=2 method={method}\nR1 x 0 1000\nC1 x 0 1n\n.init v(x) = 1\n.unsafe v(x)>2\n");
        let output = compile_str(&source, Dialect::Smt2Exp, None, None).unwrap();
        for k in 0..=2 {
            let declaration = format!("(declare-fun dx_0_s{k} () Real)");
            assert_eq!(output.matches(&declaration).count(), usize::from(k >= first));
        }
    }
    let source = fs::read_to_string(repo_root().join("benchmarks/sp/08_gt2n_gaa_ring_oscillator_3stage_ode.sp")).unwrap();
    let output = compile_str(&source, Dialect::Smt2Exp, None, None).unwrap();
    assert!(output.lines().count() < 900, "coupled Miller stamp expanded again");
    assert!(output.len() < 1_000_000, "coupled Miller stamp duplicated expressions");
}

#[test]
fn bipolar_reverse_bc_transport_and_base_injection() {
    for (kind, polarity) in [("NPN", 1.0), ("PNP", -1.0)] {
        let source = format!(".mode dc\n.model TEST {kind} IS=1e-16 BF=45 BR=2\nQ1 c b 0 TEST area=2 vt=0.025\n.unsafe v(c)>2\n");
        let sys = stamp::stamp_deck(&parser::parse_deck(&source).unwrap()).unwrap();
        let StampedBody::Algebraic { constraints, .. } = sys.body else { panic!("expected DC") };
        let env = BTreeMap::from([("v_b".into(), polarity * 0.7), ("v_c".into(), -polarity * 0.1)]);
        let forward = 2e-16 * (28.0_f64.exp() - 1.0);
        let reverse = 2e-16 * (32.0_f64.exp() - 1.0);
        for (name, expected) in [("ic_Q1", polarity * (forward - 1.5 * reverse)), ("ib_Q1", polarity * (forward / 45.0 + reverse / 2.0))] {
            let rhs = constraints.iter().find_map(|c| match &c.formula {
                Formula::Cmp { op: CmpOp::Eq, lhs: Expr::Var(n), rhs } if n == name => Some(rhs),
                _ => None,
            }).expect("BJT constitutive equation");
            let actual = rhs.eval_f64(&env, 0.0).unwrap();
            assert!((actual - expected).abs() < 1e-12 * expected.abs(), "{kind} {name}: {actual} != {expected}");
        }
    }
}
