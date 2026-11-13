//! Exact Modified Nodal Analysis (MNA), Multi-PDK FinFET / GAA Nanosheet / SiGe HBT / GaN HEMT,
//! continuous-defect PCB transmission-line electromagnetics, and 2D/electro-thermal TCAD stamping.

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::{
    is_ground_node, sanitize_ident, AnalysisMode, CmpOp, Deck, Element, ExpectedStatus, Expr,
    Formula, InitSpec, ModelDecl, ModelKind, ParamDecl, TranMethod,
};
use crate::pdk::PdkId;

/// Boltzmann constant over elementary charge `k_B / q` in `V / K`.
pub const KB_OVER_Q: f64 = 8.617_333_262e-5;

/// Speed of light in vacuum `c_0` in `m / s`.
pub const C0_M_PER_S: f64 = 2.997_924_58e8;

/// A declared real solver variable with search interval `[lo, hi]` and descriptive comment.
#[derive(Debug, Clone)]
pub struct StampedVar {
    pub name: String,
    pub lo: f64,
    pub hi: f64,
    pub comment: String,
}

/// A differential state variable `d(name)/dt = rhs` for `.mode tran`.
#[derive(Debug, Clone)]
pub struct OdeState {
    pub name: String,
    pub lo: f64,
    pub hi: f64,
    pub init: InitSpec,
    pub rhs: Expr,
    pub comment: String,
}

/// Tagged mathematical constraint (`Formula` + human-readable physics origin).
#[derive(Debug, Clone)]
pub struct TaggedConstraint {
    pub comment: String,
    pub formula: Formula,
}

/// Lowered mathematical representation ready for SMT-LIB2 or Lean 4 emission.
#[derive(Debug, Clone)]
pub enum StampedBody {
    Algebraic {
        vars: Vec<StampedVar>,
        constraints: Vec<TaggedConstraint>,
    },
    Ode {
        static_vars: Vec<StampedVar>,
        static_constraints: Vec<TaggedConstraint>,
        states: Vec<OdeState>,
        dt: f64,
        steps: usize,
        method: TranMethod,
    },
}

/// Complete stamped verification problem.
#[derive(Debug, Clone)]
pub struct StampedSystem {
    pub title: String,
    pub pdk: Option<PdkId>,
    pub expected: Option<ExpectedStatus>,
    pub params: Vec<ParamDecl>,
    pub body: StampedBody,
    pub unsafe_formula: Formula,
}

/// Helper builder for algebraic variables, KCL accumulators, and `exp`-lowered softplus terms.
struct AlgebraicBuilder {
    default_vbound: (f64, f64),
    explicit_bounds: BTreeMap<String, (f64, f64)>,
    vars: Vec<StampedVar>,
    seen_vars: BTreeSet<String>,
    constraints: Vec<TaggedConstraint>,
    kcl_outflow: BTreeMap<String, Expr>,
    softplus_counter: usize,
}

impl AlgebraicBuilder {
    fn new(default_vbound: (f64, f64), explicit_bounds: BTreeMap<String, (f64, f64)>) -> Self {
        Self {
            default_vbound,
            explicit_bounds,
            vars: Vec::new(),
            seen_vars: BTreeSet::new(),
            constraints: Vec::new(),
            kcl_outflow: BTreeMap::new(),
            softplus_counter: 0,
        }
    }

    fn ensure_var(&mut self, name: &str, fallback_bounds: (f64, f64), comment: impl Into<String>) {
        if self.seen_vars.contains(name) {
            return;
        }
        let (lo, hi) = self
            .explicit_bounds
            .get(name)
            .copied()
            .unwrap_or(fallback_bounds);
        self.seen_vars.insert(name.to_string());
        self.vars.push(StampedVar {
            name: name.to_string(),
            lo,
            hi,
            comment: comment.into(),
        });
    }

    fn touch_node(&mut self, node: &str) -> Expr {
        if is_ground_node(node) {
            Expr::num(0.0)
        } else {
            let vname = format!("v_{}", sanitize_ident(node));
            self.ensure_var(
                &vname,
                self.default_vbound,
                format!("Node voltage v({node}) [V]"),
            );
            self.kcl_outflow
                .entry(node.to_string())
                .or_insert_with(|| Expr::num(0.0));
            Expr::var(vname)
        }
    }

    fn add_branch_current(&mut self, n_from: &str, n_to: &str, current: Expr) {
        if !is_ground_node(n_from) {
            self.touch_node(n_from);
            let prev = self
                .kcl_outflow
                .remove(n_from)
                .unwrap_or_else(|| Expr::num(0.0));
            self.kcl_outflow
                .insert(n_from.to_string(), Expr::add(prev, current.clone()));
        }
        if !is_ground_node(n_to) {
            self.touch_node(n_to);
            let prev = self
                .kcl_outflow
                .remove(n_to)
                .unwrap_or_else(|| Expr::num(0.0));
            self.kcl_outflow
                .insert(n_to.to_string(), Expr::sub(prev, current));
        }
    }

    fn add_eq(&mut self, comment: impl Into<String>, lhs: Expr, rhs: Expr) {
        self.constraints.push(TaggedConstraint {
            comment: comment.into(),
            formula: Formula::Cmp {
                op: CmpOp::Eq,
                lhs,
                rhs,
            },
        });
    }

    fn add_cmp(&mut self, comment: impl Into<String>, op: CmpOp, lhs: Expr, rhs: Expr) {
        self.constraints.push(TaggedConstraint {
            comment: comment.into(),
            formula: Formula::Cmp { op, lhs, rhs },
        });
    }

    /// Lower `ln(1 + exp(z))` purely to `exp` via fresh `y >= 0` with `exp(y) = 1 + exp(z)`.
    /// Note: `exp(z) > 0` automatically implies `exp(y) > 1 => y > 0` without clipping deep reverse bias!
    fn lower_softplus(&mut self, tag: &str, z: Expr) -> Expr {
        self.softplus_counter += 1;
        let y_name = format!("y_sp_{}_{}", sanitize_ident(tag), self.softplus_counter);
        self.ensure_var(
            &y_name,
            (0.0, 2000.0),
            format!("Softplus auxiliary y = ln(1 + exp(z)) for {tag}"),
        );
        let y_var = Expr::var(y_name);
        self.add_eq(
            format!("Pure-exp softplus link exp(y) = 1 + exp(z) ({tag})"),
            Expr::exp(y_var.clone()),
            Expr::add(Expr::num(1.0), Expr::exp(z)),
        );
        y_var
    }

    /// Lower `Expr` recursively, replacing any `NodeVolt(n)` with `v_<n>` and any `Ln1pExp` with pure-`exp` auxiliary variables.
    fn lower_expr(&mut self, e: &Expr, tag: &str) -> Expr {
        match e {
            Expr::Num(v) => Expr::Num(*v),
            Expr::Var(name) => Expr::Var(name.clone()),
            Expr::NodeVolt(n) => self.touch_node(n),
            Expr::Time => Expr::num(0.0),
            Expr::Neg(a) => Expr::neg(self.lower_expr(a, tag)),
            Expr::Add(a, b) => Expr::add(self.lower_expr(a, tag), self.lower_expr(b, tag)),
            Expr::Sub(a, b) => Expr::sub(self.lower_expr(a, tag), self.lower_expr(b, tag)),
            Expr::Mul(a, b) => Expr::mul(self.lower_expr(a, tag), self.lower_expr(b, tag)),
            Expr::Div(a, b) => Expr::div(self.lower_expr(a, tag), self.lower_expr(b, tag)),
            Expr::Exp(a) => Expr::exp(self.lower_expr(a, tag)),
            Expr::Ln1pExp(a) => {
                let z = self.lower_expr(a, tag);
                self.lower_softplus(tag, z)
            }
        }
    }

    fn lower_formula(&mut self, f: &Formula, tag: &str) -> Formula {
        match f {
            Formula::Cmp { op, lhs, rhs } => Formula::Cmp {
                op: *op,
                lhs: self.lower_expr(lhs, tag),
                rhs: self.lower_expr(rhs, tag),
            },
            Formula::And(items) => Formula::And(
                items
                    .iter()
                    .map(|it| self.lower_formula(it, tag))
                    .collect(),
            ),
            Formula::Or(items) => Formula::Or(
                items
                    .iter()
                    .map(|it| self.lower_formula(it, tag))
                    .collect(),
            ),
            Formula::Not(inner) => Formula::Not(Box::new(self.lower_formula(inner, tag))),
        }
    }

    /// Introduce strictly positive algebraic square-root variable `s = sqrt(radicand)`.
    fn positive_sqrt(
        &mut self,
        var_name: &str,
        bounds: (f64, f64),
        radicand: Expr,
        desc: &str,
    ) -> Expr {
        if self.seen_vars.contains(var_name) {
            return Expr::var(var_name);
        }
        self.ensure_var(var_name, bounds, desc.to_string());
        let s = Expr::var(var_name);
        self.add_eq(
            format!("Algebraic sqrt constraint {var_name}^2 = radicand ({desc})"),
            Expr::sq(s.clone()),
            radicand,
        );
        s
    }

    /// Introduce positive logarithm variable `l = ln(arg)` via pure `exp(l) = arg`.
    fn positive_ln(&mut self, var_name: &str, bounds: (f64, f64), arg: Expr, desc: &str) -> Expr {
        self.ensure_var(var_name, bounds, desc.to_string());
        let l = Expr::var(var_name);
        self.add_eq(
            format!("Pure-exp logarithm constraint exp({var_name}) = arg ({desc})"),
            Expr::exp(l.clone()),
            arg,
        );
        l
    }
}

fn model_param(m: &ModelDecl, key: &str, default: f64) -> Expr {
    m.params
        .get(key)
        .cloned()
        .unwrap_or_else(|| Expr::num(default))
}

/// Resolve thermal voltage `V_t` from explicit override, temperature, or nominal 300 K (`25.852 mV`).
fn resolve_vt(vt_override: &Option<Expr>, temp_k: &Option<Expr>, model: &ModelDecl) -> Expr {
    if let Some(vt) = vt_override {
        vt.clone()
    } else if let Some(tk) = temp_k {
        Expr::mul(Expr::num(KB_OVER_Q), tk.clone())
    } else if let Some(vt_m) = model.params.get("vt") {
        vt_m.clone()
    } else {
        Expr::num(0.025_852)
    }
}

/// Stamp Hammerstad-Jensen + Bahl-Garg PCB microstrip equations into an `AlgebraicBuilder`,
/// returning `(z0_var, eeff_var, l_tot_var, c_tot_var, r_dc_var)`.
#[allow(clippy::too_many_arguments)]
fn stamp_pcb_microstrip_geom(
    b: &mut AlgebraicBuilder,
    name: &str,
    len: &Expr,
    w0: &Expr,
    dw: &Expr,
    h0: &Expr,
    dh: &Expr,
    t_cu: &Expr,
    er: &Expr,
    sigma_cu: &Expr,
) -> (Expr, Expr, Expr, Expr, Expr) {
    let sid = sanitize_ident(name);
    let len_e = b.lower_expr(len, &sid);
    let w0_e = b.lower_expr(w0, &sid);
    let dw_e = b.lower_expr(dw, &sid);
    let h0_e = b.lower_expr(h0, &sid);
    let dh_e = b.lower_expr(dh, &sid);
    let tcu_e = b.lower_expr(t_cu, &sid);
    let er_e = b.lower_expr(er, &sid);
    let sig_e = b.lower_expr(sigma_cu, &sid);

    // Effective copper trace width with trapezoidal etch undercut + Bahl-Garg thickness term
    let w_metal = Expr::add(w0_e, dw_e);
    let w_eff = Expr::add(w_metal.clone(), Expr::mul(Expr::num(0.48), tcu_e.clone()));
    let h_eff = Expr::add(h0_e, dh_e);
    let u = Expr::div(w_eff, h_eff);

    // s_u = sqrt(1 + 12 / u)
    let su = b.positive_sqrt(
        &format!("su_{sid}"),
        (1.0, 20.0),
        Expr::add(Expr::num(1.0), Expr::div(Expr::num(12.0), u.clone())),
        &format!("Hammerstad-Jensen sqrt(1 + 12/u) for {name}"),
    );

    // eeff = (er + 1)/2 + (er - 1)/(2 * s_u)
    let eeff_name = format!("eeff_{sid}");
    b.ensure_var(
        &eeff_name,
        (1.0, 15.0),
        format!("Effective microstrip permittivity e_eff ({name})"),
    );
    let eeff = Expr::var(&eeff_name);
    let eeff_rhs = Expr::add(
        Expr::div(Expr::add(er_e.clone(), Expr::num(1.0)), Expr::num(2.0)),
        Expr::div(
            Expr::sub(er_e, Expr::num(1.0)),
            Expr::mul(Expr::num(2.0), su),
        ),
    );
    b.add_eq(
        format!("Hammerstad-Jensen effective permittivity ({name})"),
        eeff.clone(),
        eeff_rhs,
    );

    let seeff = b.positive_sqrt(
        &format!("seeff_{sid}"),
        (1.0, 4.0),
        eeff.clone(),
        &format!("sqrt(e_eff) for {name}"),
    );

    // ln_z = ln(8/u + u/4) via exp(ln_z) = 8/u + u/4
    let lnz = b.positive_ln(
        &format!("lnz_{sid}"),
        (0.05, 6.0),
        Expr::add(
            Expr::div(Expr::num(8.0), u.clone()),
            Expr::div(u, Expr::num(4.0)),
        ),
        &format!("Wheeler-Hammerstad log geometry factor ({name})"),
    );

    // Z0 * sqrt(eeff) = 60 * ln_z
    let z0_name = format!("Z0_{sid}");
    b.ensure_var(
        &z0_name,
        (10.0, 200.0),
        format!("Characteristic impedance Z0 [Ohm] ({name})"),
    );
    let z0 = Expr::var(&z0_name);
    b.add_eq(
        format!("Characteristic impedance Z0 * sqrt(e_eff) = 60 * ln(8/u + u/4) ({name})"),
        Expr::mul(z0.clone(), seeff.clone()),
        Expr::mul(Expr::num(60.0), lnz),
    );

    // Total line L_tot, C_tot, R_dc
    let ltot_name = format!("Ltot_{sid}");
    let ctot_name = format!("Ctot_{sid}");
    let rdc_name = format!("Rdc_{sid}");
    b.ensure_var(
        &ltot_name,
        (1.0e-13, 1.0e-5),
        format!("Total microstrip inductance [H] ({name})"),
    );
    b.ensure_var(
        &ctot_name,
        (1.0e-15, 1.0e-8),
        format!("Total microstrip capacitance [F] ({name})"),
    );
    b.ensure_var(
        &rdc_name,
        (1.0e-5, 100.0),
        format!(" Copper trace DC resistance [Ohm] ({name})"),
    );
    let ltot = Expr::var(&ltot_name);
    let ctot = Expr::var(&ctot_name);
    let rdc = Expr::var(&rdc_name);

    b.add_eq(
        format!("Microstrip total inductance L_tot ({name})"),
        ltot.clone(),
        Expr::div(
            Expr::mul(len_e.clone(), Expr::mul(z0.clone(), seeff.clone())),
            Expr::num(C0_M_PER_S),
        ),
    );
    b.add_eq(
        format!("Microstrip total capacitance C_tot ({name})"),
        Expr::mul(ctot.clone(), z0.clone()),
        Expr::div(Expr::mul(len_e.clone(), seeff), Expr::num(C0_M_PER_S)),
    );
    b.add_eq(
        format!("Trapezoidal-etched copper DC resistance R_dc ({name})"),
        Expr::mul(rdc.clone(), Expr::mul(sig_e, Expr::mul(w_metal, tcu_e))),
        len_e,
    );

    (z0, eeff, ltot, ctot, rdc)
}

/// Stamp a coupled PCB differential / aggressor-victim microstrip pair geometry,
/// returning `(zdiff, kc, l_p, l_n, c_p, c_n, cm, lm, rdc)`.
#[allow(clippy::too_many_arguments)]
fn stamp_pcb_diffpair_geom(
    b: &mut AlgebraicBuilder,
    name: &str,
    len: &Expr,
    w0: &Expr,
    dw: &Expr,
    s0: &Expr,
    ds: &Expr,
    h0: &Expr,
    dh: &Expr,
    t_cu: &Expr,
    er_p: &Expr,
    er_n: &Expr,
) -> (Expr, Expr, Expr, Expr, Expr, Expr, Expr, Expr, Expr) {
    let sid = sanitize_ident(name);
    let (z0_p, _eeff_p, l_p, c_p, rdc_p) = stamp_pcb_microstrip_geom(
        b,
        &format!("{sid}_p"),
        len,
        w0,
        dw,
        h0,
        dh,
        t_cu,
        er_p,
        &Expr::num(5.8e7),
    );
    let (z0_n, _eeff_n, l_n, c_n, _rdc_n) = stamp_pcb_microstrip_geom(
        b,
        &format!("{sid}_n"),
        len,
        w0,
        dw,
        h0,
        dh,
        t_cu,
        er_n,
        &Expr::num(5.8e7),
    );

    let s_eff = Expr::add(b.lower_expr(s0, &sid), b.lower_expr(ds, &sid));
    let h_eff = Expr::add(b.lower_expr(h0, &sid), b.lower_expr(dh, &sid));

    // Garg-Bahl exponential edge-coupling coefficient kc = exp(-1.9 * s_eff / h_eff)
    let kc_name = format!("kc_{sid}");
    b.ensure_var(
        &kc_name,
        (1.0e-4, 0.95),
        format!("Edge-coupled microstrip coupling factor kc ({name})"),
    );
    let kc = Expr::var(&kc_name);
    b.add_eq(
        format!("Exponential edge-coupling law kc = exp(-1.9 * s_eff / h_eff) ({name})"),
        kc.clone(),
        Expr::exp(Expr::neg(Expr::div(
            Expr::mul(Expr::num(1.9), s_eff),
            h_eff,
        ))),
    );

    let zdiff_name = format!("Zdiff_{sid}");
    b.ensure_var(
        &zdiff_name,
        (20.0, 300.0),
        format!("Differential impedance Z_diff [Ohm] ({name})"),
    );
    let zdiff = Expr::var(&zdiff_name);
    let z0_sum = Expr::add(z0_p, z0_n);
    b.add_eq(
        format!("Coupled differential impedance Z_diff = (Z0_p + Z0_n)*(1 - 0.48*kc) ({name})"),
        zdiff.clone(),
        Expr::mul(
            z0_sum,
            Expr::sub(Expr::num(1.0), Expr::mul(Expr::num(0.48), kc.clone())),
        ),
    );

    let cm_name = format!("Cm_{sid}");
    let lm_name = format!("Lm_{sid}");
    b.ensure_var(
        &cm_name,
        (0.0, 1.0e-9),
        format!("Mutual trace capacitance C_m [F] ({name})"),
    );
    b.ensure_var(
        &lm_name,
        (0.0, 1.0e-6),
        format!("Mutual trace inductance L_m [H] ({name})"),
    );
    let cm = Expr::var(&cm_name);
    let lm = Expr::var(&lm_name);
    b.add_eq(
        format!("Mutual capacitance C_m = 0.5 * kc * (C_p + C_n) ({name})"),
        cm.clone(),
        Expr::mul(
            Expr::num(0.5),
            Expr::mul(kc.clone(), Expr::add(c_p.clone(), c_n.clone())),
        ),
    );
    b.add_eq(
        format!("Mutual inductance L_m = 0.5 * kc * (L_p + L_n) ({name})"),
        lm.clone(),
        Expr::mul(
            Expr::num(0.5),
            Expr::mul(kc.clone(), Expr::add(l_p.clone(), l_n.clone())),
        ),
    );

    (zdiff, kc, l_p, l_n, c_p, c_n, cm, lm, rdc_p)
}

/// Build transistor drain-to-source current expression across Planar EKV, `asap7` FinFET,
/// `gt2n` GAA Nanosheet (including optional electro-thermal self-heating), and `gan_sic` HEMT.
/// When `use_pure_exp_aux` is true (Algebraic / `smt2-exp`), softplus `ln(1 + exp(z))` and
/// natural scaling lengths `sqrt(...)` are stamped via `b`; when false (`Ode` vector field),
/// static geometry variables are stamped in `b` while voltage-dependent softplus uses `Expr::Ln1pExp`.
#[allow(clippy::too_many_arguments)]
fn build_mos_current(
    b: &mut AlgebraicBuilder,
    elem_name: &str,
    model: &ModelDecl,
    vd: Expr,
    vg: Expr,
    vs: Expr,
    vb: Expr,
    w: &Expr,
    l: &Expr,
    nfin: &Expr,
    dtfin_nm: &Expr,
    dvth: &Expr,
    rth: &Option<Expr>,
    vt_override: &Option<Expr>,
    tamb_k: &Option<Expr>,
    use_pure_exp_aux: bool,
) -> Result<Expr, String> {
    let sid = sanitize_ident(elem_name);
    let is0 = model_param(model, "is0", 1.0e-6);
    let vt0 = model_param(model, "vt0", 0.40);
    let kappa = model_param(model, "kappa", 0.80);

    let dvth_e = b.lower_expr(dvth, &sid);
    let mut vt_local = b.lower_expr(&resolve_vt(vt_override, tamb_k, model), &sid);
    let mut t_ch_var: Option<(Expr, Expr, Expr)> = None;

    if let Some(rth_expr) = rth {
        if !use_pure_exp_aux {
            return Err(format!(
                "electro-thermal `Rth` on `{elem_name}` requires DC or `.tcad_gaa_electrothermal` mode"
            ));
        }
        let rth_e = b.lower_expr(rth_expr, &sid);
        let tamb_e = b.lower_expr(
            tamb_k.as_ref().unwrap_or(&Expr::num(300.0)),
            &sid,
        );
        let tch_name = format!("T_ch_{sid}");
        b.ensure_var(
            &tch_name,
            (240.0, 600.0),
            format!("Self-heated channel temperature [K] ({elem_name})"),
        );
        let tch = Expr::var(&tch_name);
        vt_local = Expr::mul(Expr::num(KB_OVER_Q), tch.clone());
        t_ch_var = Some((tch, tamb_e, rth_e));
    }

    match model.kind {
        ModelKind::EkvNmos | ModelKind::EkvPmos => {
            let is_pmos = model.kind == ModelKind::EkvPmos;
            let w_e = b.lower_expr(w, &sid);
            let l_e = b.lower_expr(l, &sid);
            let scale = Expr::mul(is0, Expr::div(w_e, l_e));
            let (vgb, vsb, vdb) = if !is_pmos {
                (
                    Expr::sub(vg, vb.clone()),
                    Expr::sub(vs, vb.clone()),
                    Expr::sub(vd, vb),
                )
            } else {
                (
                    Expr::sub(vb.clone(), vg),
                    Expr::sub(vb.clone(), vs),
                    Expr::sub(vb, vd),
                )
            };
            let vth_eff = Expr::add(vt0, dvth_e);
            let denom = Expr::mul(Expr::num(2.0), Expr::mul(kappa.clone(), vt_local));
            let zf = Expr::div(
                Expr::sub(
                    Expr::sub(vgb.clone(), vth_eff.clone()),
                    Expr::mul(kappa.clone(), vsb),
                ),
                denom.clone(),
            );
            let zr = Expr::div(
                Expr::sub(Expr::sub(vgb, vth_eff), Expr::mul(kappa, vdb)),
                denom,
            );
            let (yf, yr) = if use_pure_exp_aux {
                (
                    b.lower_softplus(&format!("{sid}_f"), zf),
                    b.lower_softplus(&format!("{sid}_r"), zr),
                )
            } else {
                (Expr::ln1p_exp(zf), Expr::ln1p_exp(zr))
            };
            let id_mag = Expr::mul(scale, Expr::sub(Expr::sq(yf), Expr::sq(yr)));
            Ok(if !is_pmos {
                id_mag
            } else {
                Expr::neg(id_mag)
            })
        }
        ModelKind::FinFetN | ModelKind::FinFetP | ModelKind::GaaNmos | ModelKind::GaaPmos => {
            let is_pmos = matches!(model.kind, ModelKind::FinFetP | ModelKind::GaaPmos);
            let is_gaa = matches!(model.kind, ModelKind::GaaNmos | ModelKind::GaaPmos);

            let lg0_nm = model_param(model, "lg_nm", if is_gaa { 12.0 } else { 21.0 });
            let lg_nm = if matches!(l, Expr::Num(v) if (*v - 1.0e-6).abs() < 1e-15) {
                lg0_nm
            } else {
                // Allow L given either in nm (> 1.0) or meters (< 1e-4)
                match l {
                    Expr::Num(v) if *v < 1.0e-4 => Expr::num(*v * 1.0e9),
                    _ => b.lower_expr(l, &sid),
                }
            };
            let tbody0_nm = model_param(
                model,
                if is_gaa { "tns_nm" } else { "tfin_nm" },
                if is_gaa { 5.0 } else { 6.5 },
            );
            let dt_nm = b.lower_expr(dtfin_nm, &sid);
            let tbody_nm = Expr::add(tbody0_nm.clone(), dt_nm);
            let eot_nm = model_param(model, "eot_nm", if is_gaa { 0.85 } else { 1.0 });
            let alpha_qm = model_param(model, "alpha_qm", 1.71);
            let eta_dibl0 = model_param(model, "eta_dibl0", 3.1);

            // Multi-gate natural length lambda_nm:
            // Tri-gate FinFET: eps_Si/(3*eps_ox) * Tfin * EOT = 1.0 * Tfin * EOT
            // 4-sided GAA:     eps_Si/(4*eps_ox) * Tns  * EOT = 0.75 * Tns  * EOT
            let geom_factor = if is_gaa { 0.75 } else { 1.0 };
            let lam_nm = b.positive_sqrt(
                &format!("lam_{sid}"),
                (0.5, 15.0),
                Expr::mul(
                    Expr::num(geom_factor),
                    Expr::mul(tbody_nm.clone(), eot_nm),
                ),
                &format!("Multi-gate natural scaling length lambda [nm] ({elem_name})"),
            );

            // Quantum-confinement shift dVth_QM = alpha_QM * (1/T_body^2 - 1/T_body0^2)
            let dvth_qm = Expr::mul(
                alpha_qm,
                Expr::sub(
                    Expr::div(Expr::num(1.0), Expr::sq(tbody_nm.clone())),
                    Expr::div(Expr::num(1.0), Expr::sq(tbody0_nm)),
                ),
            );

            // DIBL coefficient eta_dibl = eta0 * exp(-Lg / (2 * lambda))
            let eta_dibl = Expr::mul(
                eta_dibl0,
                Expr::exp(Expr::neg(Expr::div(
                    lg_nm.clone(),
                    Expr::mul(Expr::num(2.0), lam_nm),
                ))),
            );

            // Effective multi-gate width / aspect ratio
            let nmult = b.lower_expr(nfin, &sid);
            let w_perim_nm = if is_gaa {
                let wns = model_param(model, "wns_nm", 18.0);
                Expr::mul(Expr::num(2.0), Expr::add(wns, tbody_nm))
            } else {
                let hfin = model_param(model, "hfin_nm", 32.0);
                Expr::add(Expr::mul(Expr::num(2.0), hfin), tbody_nm)
            };
            let drive_scale = Expr::mul(is0, Expr::mul(nmult, Expr::div(w_perim_nm, lg_nm)));

            let (vgs_int, vds_pos) = if !is_pmos {
                (Expr::sub(vg, vs.clone()), Expr::sub(vd.clone(), vs.clone()))
            } else {
                (Expr::sub(vs.clone(), vg), Expr::sub(vs.clone(), vd.clone()))
            };

            let mut vth_eff = Expr::sub(
                Expr::add(Expr::add(vt0, dvth_e), dvth_qm),
                Expr::mul(eta_dibl, vds_pos.clone()),
            );
            if let Some((ref tch, _, _)) = t_ch_var {
                let kt = model_param(model, "kt_vth", 0.00085);
                vth_eff = Expr::sub(vth_eff, Expr::mul(kt, Expr::sub(tch.clone(), Expr::num(300.0))));
            }

            let denom = Expr::mul(Expr::num(2.0), Expr::mul(kappa.clone(), vt_local));
            let zf = Expr::div(Expr::sub(vgs_int.clone(), vth_eff.clone()), denom.clone());
            let zr = Expr::div(
                Expr::sub(
                    Expr::sub(vgs_int, vth_eff),
                    Expr::mul(kappa, vds_pos.clone()),
                ),
                denom,
            );
            let (yf, yr) = if use_pure_exp_aux {
                (
                    b.lower_softplus(&format!("{sid}_f"), zf),
                    b.lower_softplus(&format!("{sid}_r"), zr),
                )
            } else {
                (Expr::ln1p_exp(zf), Expr::ln1p_exp(zr))
            };
            let id_mag = Expr::mul(drive_scale, Expr::sub(Expr::sq(yf), Expr::sq(yr)));
            let id_signed = if !is_pmos {
                id_mag.clone()
            } else {
                Expr::neg(id_mag.clone())
            };

            if let Some((tch, tamb_e, rth_e)) = t_ch_var {
                let pdiss = Expr::mul(vds_pos, id_mag);
                b.add_eq(
                    format!("Coupled electro-thermal self-heating T_ch = T_amb + R_th * P_diss ({elem_name})"),
                    tch,
                    Expr::add(tamb_e, Expr::mul(rth_e, pdiss)),
                );
            }

            Ok(id_signed)
        }
        ModelKind::GanHemt => {
            // ASM-HEMT 2DEG polarization channel current
            let w_e = b.lower_expr(w, &sid);
            let l_e = b.lower_expr(l, &sid);
            let vtheta = model_param(model, "vtheta", 0.12);
            let vgs = Expr::sub(vg, vs.clone());
            let vds = Expr::sub(vd, vs);
            let vth_eff = Expr::add(vt0, dvth_e);
            let denom = Expr::mul(Expr::num(2.0), Expr::mul(kappa.clone(), vt_local));
            let zf = Expr::div(Expr::sub(vgs.clone(), vth_eff.clone()), denom.clone());
            let zr = Expr::div(
                Expr::sub(Expr::sub(vgs, vth_eff), Expr::mul(kappa, vds)),
                denom,
            );
            let (yf, yr) = if use_pure_exp_aux {
                (
                    b.lower_softplus(&format!("{sid}_f"), zf),
                    b.lower_softplus(&format!("{sid}_r"), zr),
                )
            } else {
                (Expr::ln1p_exp(zf), Expr::ln1p_exp(zr))
            };
            let mob_deg = Expr::add(Expr::num(1.0), Expr::mul(vtheta, yf.clone()));
            let scale = Expr::div(Expr::mul(is0, Expr::div(w_e, l_e)), mob_deg);
            Ok(Expr::mul(scale, Expr::sub(Expr::sq(yf), Expr::sq(yr))))
        }
        other => Err(format!(
            "model `{}` on MOSFET `{elem_name}` has incompatible kind `{other:?}`",
            model.name
        )),
    }
}

/// Stamp 2D `(nx x ny)` Multi-Gate FinFET (`asap7`) cross-section Poisson + Quantum Confinement + SG Continuity.
#[allow(clippy::too_many_arguments)]
fn stamp_tcad_finfet_2d(
    b: &mut AlgebraicBuilder,
    name: &str,
    nx: usize,
    ny: usize,
    lg_nm: &Expr,
    tfin_nm: &Expr,
    eot_nm: &Expr,
    vgs: &Expr,
    vds: &Expr,
    phim_shift: &Expr,
    temp_k: &Expr,
    nbody_cm3: &Expr,
) -> Result<(), String> {
    if nx < 3 || ny < 1 {
        return Err(format!(
            ".tcad_finfet_2d `{name}` requires nx >= 3 and ny >= 1"
        ));
    }
    let sid = sanitize_ident(name);
    let lg_e = b.lower_expr(lg_nm, &sid);
    let tfin_e = b.lower_expr(tfin_nm, &sid);
    let eot_e = b.lower_expr(eot_nm, &sid);
    let vgs_e = b.lower_expr(vgs, &sid);
    let vds_e = b.lower_expr(vds, &sid);
    let dphim_e = b.lower_expr(phim_shift, &sid);
    let temp_e = b.lower_expr(temp_k, &sid);
    let nbody_e = b.lower_expr(nbody_cm3, &sid);
    let nbody_scaled = Expr::div(nbody_e, Expr::num(1.0e16));

    let vt = Expr::mul(Expr::num(KB_OVER_Q), temp_e);
    let dx_nm = Expr::div(lg_e, Expr::num((nx - 1) as f64));
    let dy_nm = Expr::div(tfin_e.clone(), Expr::num((ny + 1) as f64));

    // Effective gate surface drive (workfunction-referenced, flatband Vfb_eff = 0.14 V + dPhi_m)
    let vg_eff = Expr::sub(vgs_e, Expr::add(Expr::num(0.14), dphim_e));
    // Source/drain extension contact potential referenced to undoped fin channel (~0.26 V)
    let psi_bi = 0.26;

    // Quantum-confinement ground-subband energy dV_QM = 1.71 / T_fin^2 [V]
    let dv_qm_base = Expr::div(Expr::num(1.71), Expr::sq(tfin_e));

    // Grid potentials psi_{i, j} for i in 0..nx, j in 0..ny
    let mut psi_grid: Vec<Vec<Expr>> = vec![Vec::new(); nx];
    for (i, row) in psi_grid.iter_mut().enumerate() {
        for j in 0..ny {
            if i == 0 {
                row.push(Expr::num(psi_bi));
            } else if i == nx - 1 {
                row.push(Expr::add(Expr::num(psi_bi), vds_e.clone()));
            } else {
                let vname = format!("psi_{sid}_{i}_{j}");
                b.ensure_var(
                    &vname,
                    (-0.5, 2.5),
                    format!("2D FinFET electrostatic potential psi({i},{j}) [V] ({name})"),
                );
                row.push(Expr::var(vname));
            }
        }
    }

    // Oxide coupling eps_ox / eps_Si = 3.9 / 11.7 = 1/3 across EOT
    let eps_ratio = 1.0 / 3.0;
    // Scaled space-charge prefactor q * n_ref / eps_Si in [V / nm^2] for n_ref = 1e16 cm^-3:
    // q / eps_Si = 1.602e-19 / (11.7 * 8.854e-14 F/cm) = 1.546e-7 V*cm;
    // multiplying by 1e16 cm^-3 * (1e-7 cm/nm)^2 = 100 cm^-1*nm^-2 => 1.546e-5 V/nm^2.
    let q_nref_over_eps = 1.546e-5;

    // Interior 2D finite-volume Poisson + quantum-confined Quasi-Fermi electron density
    let mid_j = ny / 2;
    let mut phin_center: Vec<Expr> = Vec::with_capacity(nx);
    for i in 0..nx {
        if i == 0 {
            phin_center.push(Expr::num(0.0));
        } else if i == nx - 1 {
            phin_center.push(vds_e.clone());
        } else {
            let ph_name = format!("phin_{sid}_{i}");
            b.ensure_var(
                &ph_name,
                (-0.2, 2.0),
                format!("Channel axial electron quasi-Fermi potential phi_n({i}) [V] ({name})"),
            );
            phin_center.push(Expr::var(ph_name));
        }
    }

    for i in 1..(nx - 1) {
        for j in 0..ny {
            let psi_ij = psi_grid[i][j].clone();
            let psi_xm = psi_grid[i - 1][j].clone();
            let psi_xp = psi_grid[i + 1][j].clone();

            let lap_x = Expr::div(
                Expr::sub(
                    Expr::add(psi_xm, psi_xp),
                    Expr::mul(Expr::num(2.0), psi_ij.clone()),
                ),
                Expr::sq(dx_nm.clone()),
            );

            // Sidewall high-k HfO2 Robin gate boundary at j == 0 and j == ny - 1
            let flux_ym = if j == 0 {
                Expr::div(
                    Expr::mul(
                        Expr::num(eps_ratio),
                        Expr::sub(vg_eff.clone(), psi_ij.clone()),
                    ),
                    Expr::mul(eot_e.clone(), dy_nm.clone()),
                )
            } else {
                Expr::div(
                    Expr::sub(psi_grid[i][j - 1].clone(), psi_ij.clone()),
                    Expr::sq(dy_nm.clone()),
                )
            };
            let flux_yp = if j + 1 == ny {
                Expr::div(
                    Expr::mul(
                        Expr::num(eps_ratio),
                        Expr::sub(vg_eff.clone(), psi_ij.clone()),
                    ),
                    Expr::mul(eot_e.clone(), dy_nm.clone()),
                )
            } else {
                Expr::div(
                    Expr::sub(psi_grid[i][j + 1].clone(), psi_ij.clone()),
                    Expr::sq(dy_nm.clone()),
                )
            };

            // Top-gate wrap coupling (tri-gate H_fin = 32 nm wrap factor)
            let top_wrap = Expr::div(
                Expr::mul(Expr::num(0.012), Expr::sub(vg_eff.clone(), psi_ij.clone())),
                eot_e.clone(),
            );

            // Transverse confinement profile weight (1.35 near oxide walls, 1.0 at fin center)
            let wall_weight = if j == 0 || j + 1 == ny { 1.35 } else { 1.0 };
            let dv_qm_j = Expr::mul(Expr::num(wall_weight), dv_qm_base.clone());

            // Quantum-corrected electron concentration n_{i,j} (in units of 1e16 cm^-3)
            let n_scaled = Expr::mul(
                Expr::num(1.0e-6),
                Expr::exp(Expr::div(
                    Expr::sub(Expr::sub(psi_ij, dv_qm_j), phin_center[i].clone()),
                    vt.clone(),
                )),
            );

            let charge_rhs = Expr::mul(
                Expr::num(q_nref_over_eps),
                Expr::add(n_scaled, nbody_scaled.clone()),
            );
            b.add_eq(
                format!("2D FinFET Poisson + quantum-confined charge at ({i},{j}) ({name})"),
                Expr::add(Expr::add(lap_x, Expr::add(flux_ym, flux_yp)), top_wrap),
                charge_rhs,
            );
        }
    }

    // Scharfetter-Gummel axial electron continuity along fin center j = mid_j
    let mut edge_currents = Vec::with_capacity(nx - 1);
    for e in 0..(nx - 1) {
        let psi_l = psi_grid[e][mid_j].clone();
        let psi_r = psi_grid[e + 1][mid_j].clone();
        let delta = Expr::div(Expr::sub(psi_r.clone(), psi_l.clone()), vt.clone());

        let ee_name = format!("E_sg_{sid}_{e}");
        let bp_name = format!("Bp_sg_{sid}_{e}");
        b.ensure_var(
            &ee_name,
            (0.0, 1.0e24),
            format!("SG edge exponential exp(Delta_{e}) ({name})"),
        );
        b.ensure_var(
            &bp_name,
            (0.0, 60.0),
            format!("SG edge Bernoulli B(Delta_{e}) ({name})"),
        );
        let ee = Expr::var(&ee_name);
        let bp = Expr::var(&bp_name);
        // Cancellation-free & interval-tight identity: B(-Delta) = B(Delta) * exp(Delta) = Bp * E
        let bm = Expr::mul(bp.clone(), ee.clone());

        b.add_eq(
            format!("SG exponential link E_{e} = exp(Delta_{e}) ({name})"),
            ee.clone(),
            Expr::exp(delta.clone()),
        );
        b.add_eq(
            format!("Singularity-free Bernoulli identity Bp_{e}*(E_{e} - 1) = Delta_{e} ({name})"),
            Expr::mul(bp.clone(), Expr::sub(ee, Expr::num(1.0))),
            delta.clone(),
        );

        // Global Euler-coth polynomial bracket valid for ALL real Delta:
        // 1 - d/2 + d^2/12 - d^4/720 <= B(d) <= 1 - d/2 + d^2/12
        let d2 = Expr::sq(delta.clone());
        let d4 = Expr::sq(d2.clone());
        let upper = Expr::add(
            Expr::sub(Expr::num(1.0), Expr::div(delta, Expr::num(2.0))),
            Expr::div(d2, Expr::num(12.0)),
        );
        let lower = Expr::sub(upper.clone(), Expr::div(d4, Expr::num(720.0)));
        b.add_cmp(
            format!("Global Bernoulli lower bracket at edge {e} ({name})"),
            CmpOp::Ge,
            bp.clone(),
            lower,
        );
        b.add_cmp(
            format!("Global Bernoulli upper bracket at edge {e} ({name})"),
            CmpOp::Le,
            bp.clone(),
            upper,
        );

        let n_l = Expr::exp(Expr::div(
            Expr::sub(
                Expr::sub(psi_l, dv_qm_base.clone()),
                phin_center[e].clone(),
            ),
            vt.clone(),
        ));
        let n_r = Expr::exp(Expr::div(
            Expr::sub(
                Expr::sub(psi_r, dv_qm_base.clone()),
                phin_center[e + 1].clone(),
            ),
            vt.clone(),
        ));
        // Positive terminal drain-to-source current density J_e [uA/um] when V_DS > 0 (phi_n,R > phi_n,L)
        let j_edge = Expr::div(
            Expr::mul(
                Expr::num(2.4e-5),
                Expr::mul(
                    vt.clone(),
                    Expr::sub(Expr::mul(bm, n_l), Expr::mul(bp, n_r)),
                ),
            ),
            dx_nm.clone(),
        );
        edge_currents.push(j_edge);
    }

    for i in 1..(nx - 1) {
        b.add_eq(
            format!("Axial Scharfetter-Gummel current continuity at slice {i} ({name})"),
            edge_currents[i].clone(),
            edge_currents[i - 1].clone(),
        );
    }

    // Expose observable drain leakage current `id_leak_ua_<name>` and center barrier `psi_mid_<name>`
    let id_name = format!("id_leak_ua_{sid}");
    b.ensure_var(
        &id_name,
        (-10.0, 500.0),
        format!("2D FinFET terminal drain current [uA/um] ({name})"),
    );
    b.add_eq(
        format!("Drain terminal current observable ({name})"),
        Expr::var(&id_name),
        edge_currents[nx - 2].clone(),
    );

    let pmid_name = format!("psi_mid_{sid}");
    b.ensure_var(
        &pmid_name,
        (-0.5, 2.5),
        format!("Mid-channel center potential [V] ({name})"),
    );
    b.add_eq(
        format!("Mid-channel center potential observable ({name})"),
        Expr::var(&pmid_name),
        psi_grid[nx / 2][mid_j].clone(),
    );

    Ok(())
}

/// Stamp 2nm Gate-All-Around (`gt2n`) Stacked Nanosheet Coupled Electro-Thermal + Quantum-Confinement TCAD.
#[allow(clippy::too_many_arguments)]
fn stamp_tcad_gaa_electrothermal(
    b: &mut AlgebraicBuilder,
    name: &str,
    nx: usize,
    nsheets: usize,
    lg_nm: &Expr,
    wns_nm: &Expr,
    tns_nm: &Expr,
    eot_nm: &Expr,
    lisp_nm: &Expr,
    vgs: &Expr,
    vds: &Expr,
    tamb_k: &Expr,
    rth_kw: &Expr,
) -> Result<(), String> {
    if nx < 3 || nsheets < 1 {
        return Err(format!(
            ".tcad_gaa_electrothermal `{name}` requires nx >= 3 and nsheets >= 1"
        ));
    }
    let sid = sanitize_ident(name);
    let lg_e = b.lower_expr(lg_nm, &sid);
    let wns_e = b.lower_expr(wns_nm, &sid);
    let tns_e = b.lower_expr(tns_nm, &sid);
    let eot_e = b.lower_expr(eot_nm, &sid);
    let lisp_e = b.lower_expr(lisp_nm, &sid);
    let vgs_e = b.lower_expr(vgs, &sid);
    let vds_e = b.lower_expr(vds, &sid);
    let tamb_e = b.lower_expr(tamb_k, &sid);
    let rth_e = b.lower_expr(rth_kw, &sid);

    // Self-consistent channel temperature T_ch_<name> [K]
    let tch_name = format!("T_ch_{sid}");
    b.ensure_var(
        &tch_name,
        (250.0, 650.0),
        format!("2nm GAA stacked-nanosheet lattice temperature [K] ({name})"),
    );
    let tch = Expr::var(&tch_name);
    let vt = Expr::mul(Expr::num(KB_OVER_Q), tch.clone());

    let dx_nm = Expr::div(lg_e, Expr::num((nx - 1) as f64));
    // 4-sided GAA natural scaling length squared: lam_gaa^2 = 0.75 * T_ns * EOT
    let lam2 = Expr::mul(Expr::num(0.75), Expr::mul(tns_e.clone(), eot_e));
    // Quantum confinement ground subband shift in ultra-thin 5nm nanosheet: 1.71 / T_ns^2 [V]
    let dv_qm = Expr::div(Expr::num(1.71), Expr::sq(tns_e.clone()));
    // Bandgap narrowing / intrinsic carrier thermal activation shift with T_ch:
    let dphi_thermal = Expr::mul(
        Expr::num(0.00095),
        Expr::sub(tch.clone(), Expr::num(300.0)),
    );

    let vg_eff = Expr::sub(vgs_e, Expr::num(0.14));
    let psi_bi = 0.26;

    let mut psi: Vec<Expr> = Vec::with_capacity(nx);
    let mut phin: Vec<Expr> = Vec::with_capacity(nx);
    for i in 0..nx {
        if i == 0 {
            psi.push(Expr::num(psi_bi));
            phin.push(Expr::num(0.0));
        } else if i == nx - 1 {
            psi.push(Expr::add(Expr::num(psi_bi), vds_e.clone()));
            phin.push(vds_e.clone());
        } else {
            let p_name = format!("psi_{sid}_{i}");
            let f_name = format!("phin_{sid}_{i}");
            b.ensure_var(
                &p_name,
                (-0.4, 2.2),
                format!("GAA nanosheet surface/center potential psi({i}) [V] ({name})"),
            );
            b.ensure_var(
                &f_name,
                (-0.2, 2.0),
                format!("GAA nanosheet quasi-Fermi potential phi_n({i}) [V] ({name})"),
            );
            psi.push(Expr::var(p_name));
            phin.push(Expr::var(f_name));
        }
    }

    // 4-sided GAA Poisson with inner-spacer fringing at slice 1 and slice nx - 2
    for i in 1..(nx - 1) {
        let lap_x = Expr::div(
            Expr::sub(
                Expr::add(psi[i - 1].clone(), psi[i + 1].clone()),
                Expr::mul(Expr::num(2.0), psi[i].clone()),
            ),
            Expr::sq(dx_nm.clone()),
        );
        let gate_wrap = Expr::div(Expr::sub(vg_eff.clone(), psi[i].clone()), lam2.clone());
        let isp_fringe = if i == 1 || i == nx - 2 {
            let v_ext = if i == 1 {
                Expr::num(psi_bi)
            } else {
                Expr::add(Expr::num(psi_bi), vds_e.clone())
            };
            Expr::div(
                Expr::mul(Expr::num(0.18), Expr::sub(v_ext, psi[i].clone())),
                Expr::mul(lisp_e.clone(), dx_nm.clone()),
            )
        } else {
            Expr::num(0.0)
        };
        let n_sheet = Expr::mul(
            Expr::num(1.0e-6),
            Expr::exp(Expr::div(
                Expr::add(
                    Expr::sub(Expr::sub(psi[i].clone(), dv_qm.clone()), phin[i].clone()),
                    dphi_thermal.clone(),
                ),
                vt.clone(),
            )),
        );
        b.add_eq(
            format!("4-sided GAA nanosheet Poisson + inner-spacer fringe at slice {i} ({name})"),
            Expr::add(lap_x, Expr::add(gate_wrap, isp_fringe)),
            Expr::mul(Expr::num(1.546e-5), Expr::add(n_sheet, Expr::num(1.0))),
        );
    }

    // Axial Scharfetter-Gummel continuity + stack current
    let perim_um = Expr::mul(
        Expr::num(0.002 * (nsheets as f64)),
        Expr::add(wns_e, tns_e),
    );
    let mut j_edges = Vec::with_capacity(nx - 1);
    for e in 0..(nx - 1) {
        let delta = Expr::div(Expr::sub(psi[e + 1].clone(), psi[e].clone()), vt.clone());
        let ee_name = format!("E_gaa_{sid}_{e}");
        let bp_name = format!("Bp_gaa_{sid}_{e}");
        b.ensure_var(
            &ee_name,
            (0.0, 1.0e24),
            format!("GAA SG edge exp(Delta_{e}) ({name})"),
        );
        b.ensure_var(
            &bp_name,
            (0.0, 60.0),
            format!("GAA SG edge Bernoulli B(Delta_{e}) ({name})"),
        );
        let ee = Expr::var(&ee_name);
        let bp = Expr::var(&bp_name);
        // Cancellation-free & interval-tight identity: B(-Delta) = B(Delta) * exp(Delta) = Bp * E
        let bm = Expr::mul(bp.clone(), ee.clone());

        b.add_eq(
            format!("GAA SG exponential E_{e} = exp(Delta_{e}) ({name})"),
            ee.clone(),
            Expr::exp(delta.clone()),
        );
        b.add_eq(
            format!("GAA SG Bernoulli Bp_{e}*(E_{e}-1) = Delta_{e} ({name})"),
            Expr::mul(bp.clone(), Expr::sub(ee, Expr::num(1.0))),
            delta.clone(),
        );
        let d2 = Expr::sq(delta.clone());
        let d4 = Expr::sq(d2.clone());
        let upper = Expr::add(
            Expr::sub(Expr::num(1.0), Expr::div(delta, Expr::num(2.0))),
            Expr::div(d2, Expr::num(12.0)),
        );
        let lower = Expr::sub(upper.clone(), Expr::div(d4, Expr::num(720.0)));
        b.add_cmp(
            format!("GAA Bernoulli lower bracket edge {e} ({name})"),
            CmpOp::Ge,
            bp.clone(),
            lower,
        );
        b.add_cmp(
            format!("GAA Bernoulli upper bracket edge {e} ({name})"),
            CmpOp::Le,
            bp.clone(),
            upper,
        );

        let n_l = Expr::exp(Expr::div(
            Expr::add(
                Expr::sub(Expr::sub(psi[e].clone(), dv_qm.clone()), phin[e].clone()),
                dphi_thermal.clone(),
            ),
            vt.clone(),
        ));
        let n_r = Expr::exp(Expr::div(
            Expr::add(
                Expr::sub(
                    Expr::sub(psi[e + 1].clone(), dv_qm.clone()),
                    phin[e + 1].clone(),
                ),
                dphi_thermal.clone(),
            ),
            vt.clone(),
        ));
        // Positive drain-to-source stack current in microamperes [uA] when V_DS > 0 (phi_n,R > phi_n,L)
        let i_edge_ua = Expr::div(
            Expr::mul(
                Expr::num(1.28),
                Expr::mul(
                    perim_um.clone(),
                    Expr::mul(
                        vt.clone(),
                        Expr::sub(Expr::mul(bm, n_l), Expr::mul(bp, n_r)),
                    ),
                ),
            ),
            dx_nm.clone(),
        );
        j_edges.push(i_edge_ua);
    }

    for i in 1..(nx - 1) {
        b.add_eq(
            format!("GAA axial current continuity [uA] at slice {i} ({name})"),
            j_edges[i].clone(),
            j_edges[i - 1].clone(),
        );
    }

    let istack_ua = j_edges[nx - 2].clone();
    let istack_ua_name = format!("I_stack_ua_{sid}");
    b.ensure_var(
        &istack_ua_name,
        (-10.0, 2000.0),
        format!("Total stacked-nanosheet current [uA] ({name})"),
    );
    b.add_eq(
        format!("Total nanosheet stack current observable [uA] ({name})"),
        Expr::var(&istack_ua_name),
        istack_ua.clone(),
    );

    // Self-heating energy balance: T_ch = T_amb + (R_th * 1e-6 W/uW) * V_ds * I_stack_ua
    b.add_eq(
        format!("Coupled GAA electro-thermal balance T_ch = T_amb + R_th * V_ds * I_stack ({name})"),
        tch,
        Expr::add(
            tamb_e,
            Expr::mul(
                Expr::mul(Expr::num(1.0e-6), rth_e),
                Expr::mul(vds_e, Expr::var(&istack_ua_name)),
            ),
        ),
    );

    Ok(())
}

/// Stamp baseline 1D semiconductor p-n junction in Quasi-Fermi + global-bracketed SG form.
#[allow(clippy::too_many_arguments)]
fn stamp_tcad_pn_1d(
    b: &mut AlgebraicBuilder,
    name: &str,
    nodes: usize,
    length_um: f64,
    junction_um: f64,
    q_dope: &Expr,
    nd_plus: &Expr,
    temp: &Expr,
    v_bias: &Expr,
) -> Result<(), String> {
    if nodes < 5 {
        return Err(format!(".tcad_pn_1d `{name}` requires nodes >= 5"));
    }
    let sid = sanitize_ident(name);
    let q_e = b.lower_expr(q_dope, &sid);
    let nd_e = b.lower_expr(nd_plus, &sid);
    let temp_e = b.lower_expr(temp, &sid);
    let vb_e = b.lower_expr(v_bias, &sid);
    let vt = Expr::mul(Expr::num(KB_OVER_Q), temp_e);

    let dx_um = length_um / ((nodes - 1) as f64);
    let mut psi = Vec::with_capacity(nodes);
    for i in 0..nodes {
        if i == 0 {
            psi.push(Expr::num(-0.35));
        } else if i == nodes - 1 {
            psi.push(Expr::add(Expr::num(0.45), vb_e.clone()));
        } else {
            let pname = format!("psi_{sid}_{i}");
            b.ensure_var(
                &pname,
                (-2.0, 5.0),
                format!("1D junction potential psi({i}) [V] ({name})"),
            );
            psi.push(Expr::var(pname));
        }
    }

    // De Mari scaled Poisson equation across p-region and n+ region
    let mut max_field_terms = Vec::new();
    for i in 1..(nodes - 1) {
        let x_um = (i as f64) * dx_um;
        let net_doping = if x_um < junction_um {
            Expr::neg(q_e.clone())
        } else {
            nd_e.clone()
        };
        let n_eq = Expr::mul(
            Expr::num(1.0e-4),
            Expr::exp(Expr::div(
                Expr::sub(psi[i].clone(), vb_e.clone()),
                vt.clone(),
            )),
        );
        let p_eq = Expr::mul(
            Expr::num(1.0e-4),
            Expr::exp(Expr::div(Expr::neg(psi[i].clone()), vt.clone())),
        );
        let lap = Expr::div(
            Expr::sub(
                Expr::add(psi[i - 1].clone(), psi[i + 1].clone()),
                Expr::mul(Expr::num(2.0), psi[i].clone()),
            ),
            Expr::num(dx_um * dx_um),
        );
        b.add_eq(
            format!("1D semiconductor Poisson equation at node {i} ({name})"),
            lap,
            Expr::mul(
                Expr::num(1.546),
                Expr::sub(Expr::sub(n_eq, p_eq), net_doping),
            ),
        );
        max_field_terms.push((
            i,
            Expr::div(
                Expr::sub(psi[i + 1].clone(), psi[i].clone()),
                Expr::num(dx_um),
            ),
        ));
    }

    let j_idx = ((junction_um / dx_um).round() as usize).clamp(1, nodes - 2);
    let ej_name = format!("E_junc_v_per_um_{sid}");
    b.ensure_var(
        &ej_name,
        (-200.0, 200.0),
        format!("Peak metallurgical junction electric field [V/um] ({name})"),
    );
    b.add_eq(
        format!("Metallurgical junction electric field observable ({name})"),
        Expr::var(&ej_name),
        Expr::div(
            Expr::sub(psi[j_idx + 1].clone(), psi[j_idx].clone()),
            Expr::num(dx_um),
        ),
    );
    Ok(())
}

/// Compile a parsed `Deck` into a `StampedSystem`.
pub fn stamp_deck(deck: &Deck) -> Result<StampedSystem, String> {
    let unsafe_raw = deck
        .unsafe_formula
        .clone()
        .ok_or_else(|| "deck is missing a `.unsafe <formula>` specification".to_string())?;

    // Expand `.const` bindings in declaration order
    let mut const_map: BTreeMap<String, Expr> = BTreeMap::new();
    let empty_nodes: BTreeMap<String, Expr> = BTreeMap::new();
    for (cname, cexpr) in &deck.consts {
        let expanded = cexpr.substitute(&const_map, &empty_nodes, None);
        const_map.insert(cname.clone(), expanded);
    }

    let mut explicit_bounds = BTreeMap::new();
    for bd in &deck.bounds {
        explicit_bounds.insert(bd.target.clone(), (bd.lo, bd.hi));
    }

    match deck.mode {
        AnalysisMode::Dc => stamp_dc_deck(deck, &const_map, explicit_bounds, &unsafe_raw),
        AnalysisMode::Tran { dt, steps, method } => {
            stamp_tran_deck(deck, &const_map, explicit_bounds, &unsafe_raw, dt, steps, method)
        }
    }
}

fn stamp_dc_deck(
    deck: &Deck,
    const_map: &BTreeMap<String, Expr>,
    explicit_bounds: BTreeMap<String, (f64, f64)>,
    unsafe_raw: &Formula,
) -> Result<StampedSystem, String> {
    let empty_nodes = BTreeMap::new();
    let mut b = AlgebraicBuilder::new(deck.default_vbound, explicit_bounds);

    for elem in &deck.elements {
        match elem {
            Element::Resistor {
                name,
                n_pos,
                n_neg,
                r,
            } => {
                let vp = b.touch_node(n_pos);
                let vn = b.touch_node(n_neg);
                let r_e = b.lower_expr(&r.substitute(const_map, &empty_nodes, None), name);
                let i_r = Expr::div(Expr::sub(vp, vn), r_e);
                b.add_branch_current(n_pos, n_neg, i_r);
            }
            Element::Capacitor { n_pos, n_neg, .. } | Element::MlccCap { n_pos, n_neg, .. } => {
                // Open circuit in DC equilibrium; still register nodes if referenced
                b.touch_node(n_pos);
                b.touch_node(n_neg);
            }
            Element::Inductor {
                name,
                n_pos,
                n_neg,
                r_ser,
                ..
            } => {
                let vp = b.touch_node(n_pos);
                let vn = b.touch_node(n_neg);
                let iname = format!("i_{}", sanitize_ident(name));
                b.ensure_var(&iname, (-50.0, 50.0), format!("Inductor DC current ({name})"));
                let il = Expr::var(&iname);
                let rs = b.lower_expr(&r_ser.substitute(const_map, &empty_nodes, None), name);
                b.add_eq(
                    format!("Inductor DC branch voltage ({name})"),
                    Expr::sub(vp, vn),
                    Expr::mul(rs, il.clone()),
                );
                b.add_branch_current(n_pos, n_neg, il);
            }
            Element::CoupledInductors { .. } => {}
            Element::VoltageSource {
                name,
                n_pos,
                n_neg,
                wave,
            } => {
                let vp = b.touch_node(n_pos);
                let vn = b.touch_node(n_neg);
                let iname = format!("i_{}", sanitize_ident(name));
                b.ensure_var(
                    &iname,
                    (-50.0, 50.0),
                    format!("Voltage source branch current ({name})"),
                );
                let iv = Expr::var(&iname);
                let vsrc = b.lower_expr(
                    &wave.expr_at(false).substitute(const_map, &empty_nodes, None),
                    name,
                );
                b.add_eq(
                    format!("Voltage source constitutive equation ({name})"),
                    Expr::sub(vp, vn),
                    vsrc,
                );
                b.add_branch_current(n_pos, n_neg, iv);
            }
            Element::CurrentSource {
                name,
                n_pos,
                n_neg,
                wave,
            } => {
                let isrc = b.lower_expr(
                    &wave.expr_at(false).substitute(const_map, &empty_nodes, None),
                    name,
                );
                b.add_branch_current(n_pos, n_neg, isrc);
            }
            Element::Diode {
                name,
                n_anode,
                n_cathode,
                model,
                area,
                vt_override,
            } => {
                let m = deck
                    .models
                    .get(model)
                    .ok_or_else(|| format!("unknown diode model `{model}` on `{name}`"))?;
                let va = b.touch_node(n_anode);
                let vk = b.touch_node(n_cathode);
                let is_val = model_param(m, "is", 1.0e-14);
                let n_id = model_param(m, "n", 1.0);
                let vt_raw = resolve_vt(vt_override, &None, m);
                let vt_e = b.lower_expr(&vt_raw.substitute(const_map, &empty_nodes, None), name);
                let area_e =
                    b.lower_expr(&area.substitute(const_map, &empty_nodes, None), name);
                let id_name = format!("i_{}", sanitize_ident(name));
                b.ensure_var(
                    &id_name,
                    (-1.0, 10.0),
                    format!("Shockley diode current ({name})"),
                );
                let id_var = Expr::var(&id_name);
                let id_rhs = Expr::mul(
                    Expr::mul(area_e, is_val),
                    Expr::sub(
                        Expr::exp(Expr::div(Expr::sub(va, vk), Expr::mul(n_id, vt_e))),
                        Expr::num(1.0),
                    ),
                );
                b.add_eq(
                    format!("Shockley diode law ({name})"),
                    id_var.clone(),
                    id_rhs,
                );
                b.add_branch_current(n_anode, n_cathode, id_var);
            }
            Element::Mosfet {
                name,
                n_drain,
                n_gate,
                n_source,
                n_bulk,
                model,
                w,
                l,
                nfin,
                dtfin_nm,
                dvth,
                rth,
                vt_override,
                tamb_k,
                ..
            } => {
                let m = deck
                    .models
                    .get(model)
                    .ok_or_else(|| format!("unknown MOSFET/FinFET/GAA model `{model}` on `{name}`"))?;
                let vd = b.touch_node(n_drain);
                let vg = b.touch_node(n_gate);
                let vs = b.touch_node(n_source);
                let vb = b.touch_node(n_bulk);

                let w_s = w.substitute(const_map, &empty_nodes, None);
                let l_s = l.substitute(const_map, &empty_nodes, None);
                let nfin_s = nfin.substitute(const_map, &empty_nodes, None);
                let dtfin_s = dtfin_nm.substitute(const_map, &empty_nodes, None);
                let dvth_s = dvth.substitute(const_map, &empty_nodes, None);
                let rth_s = rth.as_ref().map(|e| e.substitute(const_map, &empty_nodes, None));
                let vt_s = vt_override
                    .as_ref()
                    .map(|e| e.substitute(const_map, &empty_nodes, None));
                let tamb_s = tamb_k
                    .as_ref()
                    .map(|e| e.substitute(const_map, &empty_nodes, None));

                let ids = build_mos_current(
                    &mut b, name, m, vd, vg, vs, vb, &w_s, &l_s, &nfin_s, &dtfin_s, &dvth_s,
                    &rth_s, &vt_s, &tamb_s, true,
                )?;
                let id_name = format!("i_{}", sanitize_ident(name));
                b.ensure_var(
                    &id_name,
                    (-5.0, 5.0),
                    format!("Transistor channel current ({name})"),
                );
                let id_var = Expr::var(&id_name);
                b.add_eq(
                    format!("Transistor constitutive current ({name}, model {model})"),
                    id_var.clone(),
                    ids,
                );
                b.add_branch_current(n_drain, n_source, id_var);
            }
            Element::Bjt {
                name,
                n_col,
                n_base,
                n_emit,
                model,
                area,
                deg_ev,
                vt_override,
                temp_k,
            } => {
                let m = deck
                    .models
                    .get(model)
                    .ok_or_else(|| format!("unknown BJT/HBT model `{model}` on `{name}`"))?;
                let vc = b.touch_node(n_col);
                let vb = b.touch_node(n_base);
                let ve = b.touch_node(n_emit);

                let is_pnp = m.kind == ModelKind::Pnp;
                let is_hbt = m.kind == ModelKind::SiGeHbt;
                let is0 = model_param(m, "is", 1.0e-16);
                let bf = model_param(m, "bf", 100.0);
                let br = model_param(m, "br", 2.0);
                let area_e =
                    b.lower_expr(&area.substitute(const_map, &empty_nodes, None), name);
                let temp_sub = temp_k
                    .as_ref()
                    .map(|e| e.substitute(const_map, &empty_nodes, None));
                let vt_sub = vt_override
                    .as_ref()
                    .map(|e| e.substitute(const_map, &empty_nodes, None));
                let vt_e = b.lower_expr(&resolve_vt(&vt_sub, &temp_sub, m), name);

                let mut is_eff = Expr::mul(area_e, is0);
                if is_hbt {
                    let deg = deg_ev
                        .as_ref()
                        .map(|e| b.lower_expr(&e.substitute(const_map, &empty_nodes, None), name))
                        .unwrap_or_else(|| model_param(m, "deg_ev", 0.085));
                    // SiGe heterojunction collector enhancement exp(dEg_Ge / V_t)
                    is_eff = Expr::mul(is_eff, Expr::exp(Expr::div(deg, vt_e.clone())));
                }

                let (vbe, vbc) = if !is_pnp {
                    (Expr::sub(vb.clone(), ve), Expr::sub(vb, vc))
                } else {
                    (Expr::sub(ve, vb.clone()), Expr::sub(vc, vb))
                };

                let sid = sanitize_ident(name);
                let ifwd_ideal = Expr::mul(
                    is_eff.clone(),
                    Expr::sub(Expr::exp(Expr::div(vbe, vt_e.clone())), Expr::num(1.0)),
                );
                // Kirk base push-out monotonically saturates collector gain at high injection,
                // while base injection `ifwd_ideal / bf` remains un-collapsed!
                let ifwd_col = if is_hbt {
                    let ikirk = model_param(m, "ikirk", 0.012);
                    let skirk = b.positive_sqrt(
                        &format!("skirk_{sid}"),
                        (1.0, 1.0e4),
                        Expr::add(
                            Expr::num(1.0),
                            Expr::div(Expr::sq(ifwd_ideal.clone()), Expr::sq(ikirk)),
                        ),
                        &format!("Monotone Kirk high-injection collector roll-off factor ({name})"),
                    );
                    Expr::div(ifwd_ideal.clone(), skirk)
                } else {
                    ifwd_ideal.clone()
                };
                let irev = Expr::mul(
                    is_eff,
                    Expr::sub(Expr::exp(Expr::div(vbc, vt_e)), Expr::num(1.0)),
                );

                let ic_mag = Expr::sub(
                    Expr::sub(ifwd_col, irev.clone()),
                    Expr::div(irev.clone(), br.clone()),
                );
                let ib_mag = Expr::add(Expr::div(ifwd_ideal, bf), Expr::div(irev, br));
                let ic_name = format!("ic_{sid}");
                let ib_name = format!("ib_{sid}");
                b.ensure_var(&ic_name, (-2.0, 2.0), format!("BJT/HBT collector current ({name})"));
                b.ensure_var(&ib_name, (-1.0, 1.0), format!("BJT/HBT base current ({name})"));
                let ic_var = Expr::var(&ic_name);
                let ib_var = Expr::var(&ib_name);

                b.add_eq(
                    format!("BJT/SiGe-HBT collector transport current ({name})"),
                    ic_var.clone(),
                    if !is_pnp { ic_mag } else { Expr::neg(ic_mag) },
                );
                b.add_eq(
                    format!("BJT/SiGe-HBT base recombination current ({name})"),
                    ib_var.clone(),
                    if !is_pnp { ib_mag } else { Expr::neg(ib_mag) },
                );
                b.add_branch_current(n_col, n_emit, ic_var);
                b.add_branch_current(n_base, n_emit, ib_var);
            }
            Element::PcbMicrostrip {
                name,
                n_in,
                n_out,
                n_ref,
                len,
                w0,
                dw,
                h0,
                dh,
                t_cu,
                er,
                sigma_cu,
            } => {
                b.touch_node(n_ref);
                let vin = b.touch_node(n_in);
                let vout = b.touch_node(n_out);
                let (_, _, _, _, rdc) = stamp_pcb_microstrip_geom(
                    &mut b,
                    name,
                    &len.substitute(const_map, &empty_nodes, None),
                    &w0.substitute(const_map, &empty_nodes, None),
                    &dw.substitute(const_map, &empty_nodes, None),
                    &h0.substitute(const_map, &empty_nodes, None),
                    &dh.substitute(const_map, &empty_nodes, None),
                    &t_cu.substitute(const_map, &empty_nodes, None),
                    &er.substitute(const_map, &empty_nodes, None),
                    &sigma_cu.substitute(const_map, &empty_nodes, None),
                );
                b.add_branch_current(n_in, n_out, Expr::div(Expr::sub(vin, vout), rdc));
            }
            Element::PcbCoupledDiffpair {
                name,
                in_p,
                in_n,
                out_p,
                out_n,
                ref_in,
                ref_out,
                len,
                w0,
                dw,
                s0,
                ds,
                h0,
                dh,
                t_cu,
                er_p,
                er_n,
                r_ret,
                ..
            } => {
                let vip = b.touch_node(in_p);
                let vin = b.touch_node(in_n);
                let vop = b.touch_node(out_p);
                let von = b.touch_node(out_n);
                let vri = b.touch_node(ref_in);
                let vro = b.touch_node(ref_out);
                let (_, _, _, _, _, _, _, _, rdc) = stamp_pcb_diffpair_geom(
                    &mut b,
                    name,
                    &len.substitute(const_map, &empty_nodes, None),
                    &w0.substitute(const_map, &empty_nodes, None),
                    &dw.substitute(const_map, &empty_nodes, None),
                    &s0.substitute(const_map, &empty_nodes, None),
                    &ds.substitute(const_map, &empty_nodes, None),
                    &h0.substitute(const_map, &empty_nodes, None),
                    &dh.substitute(const_map, &empty_nodes, None),
                    &t_cu.substitute(const_map, &empty_nodes, None),
                    &er_p.substitute(const_map, &empty_nodes, None),
                    &er_n.substitute(const_map, &empty_nodes, None),
                );
                b.add_branch_current(in_p, out_p, Expr::div(Expr::sub(vip, vop), rdc.clone()));
                b.add_branch_current(in_n, out_n, Expr::div(Expr::sub(vin, von), rdc));
                if ref_in != ref_out {
                    let rr = b.lower_expr(&r_ret.substitute(const_map, &empty_nodes, None), name);
                    b.add_branch_current(ref_in, ref_out, Expr::div(Expr::sub(vri, vro), rr));
                }
            }
            Element::TcadFinFet2D {
                name,
                nx,
                ny,
                lg_nm,
                tfin_nm,
                eot_nm,
                vgs,
                vds,
                phim_shift,
                temp_k,
                nbody_cm3,
            } => {
                stamp_tcad_finfet_2d(
                    &mut b,
                    name,
                    *nx,
                    *ny,
                    &lg_nm.substitute(const_map, &empty_nodes, None),
                    &tfin_nm.substitute(const_map, &empty_nodes, None),
                    &eot_nm.substitute(const_map, &empty_nodes, None),
                    &vgs.substitute(const_map, &empty_nodes, None),
                    &vds.substitute(const_map, &empty_nodes, None),
                    &phim_shift.substitute(const_map, &empty_nodes, None),
                    &temp_k.substitute(const_map, &empty_nodes, None),
                    &nbody_cm3.substitute(const_map, &empty_nodes, None),
                )?;
            }
            Element::TcadGaaElectroThermal {
                name,
                nx,
                nsheets,
                lg_nm,
                wns_nm,
                tns_nm,
                eot_nm,
                lisp_nm,
                vgs,
                vds,
                tamb_k,
                rth_kw,
            } => {
                stamp_tcad_gaa_electrothermal(
                    &mut b,
                    name,
                    *nx,
                    *nsheets,
                    &lg_nm.substitute(const_map, &empty_nodes, None),
                    &wns_nm.substitute(const_map, &empty_nodes, None),
                    &tns_nm.substitute(const_map, &empty_nodes, None),
                    &eot_nm.substitute(const_map, &empty_nodes, None),
                    &lisp_nm.substitute(const_map, &empty_nodes, None),
                    &vgs.substitute(const_map, &empty_nodes, None),
                    &vds.substitute(const_map, &empty_nodes, None),
                    &tamb_k.substitute(const_map, &empty_nodes, None),
                    &rth_kw.substitute(const_map, &empty_nodes, None),
                )?;
            }
            Element::TcadDiode1D {
                name,
                nodes,
                length_um,
                junction_um,
                q_dope,
                nd_plus,
                temp,
                v_bias,
            } => {
                stamp_tcad_pn_1d(
                    &mut b,
                    name,
                    *nodes,
                    *length_um,
                    *junction_um,
                    &q_dope.substitute(const_map, &empty_nodes, None),
                    &nd_plus.substitute(const_map, &empty_nodes, None),
                    &temp.substitute(const_map, &empty_nodes, None),
                    &v_bias.substitute(const_map, &empty_nodes, None),
                )?;
            }
        }
    }

    // Emit KCL conservation at every non-ground circuit node
    let kcl_entries: Vec<(String, Expr)> = b.kcl_outflow.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
    for (node, sum_out) in kcl_entries {
        if !matches!(sum_out, Expr::Num(v) if v == 0.0) {
            b.add_eq(
                format!("MNA Kirchhoff Current Law at node `{node}`"),
                sum_out,
                Expr::num(0.0),
            );
        }
    }

    let unsafe_sub = unsafe_raw.substitute(const_map, &empty_nodes, None);
    let unsafe_lowered = b.lower_formula(&unsafe_sub, "unsafe");

    Ok(StampedSystem {
        title: deck.title.clone(),
        pdk: deck.pdk,
        expected: deck.expected,
        params: deck.params.clone(),
        body: StampedBody::Algebraic {
            vars: b.vars,
            constraints: b.constraints,
        },
        unsafe_formula: unsafe_lowered,
    })
}

/// Stamp `.mode tran` into explicit ODE system `dx/dt = f(x, p, t)` plus static geometry invariants.
fn stamp_tran_deck(
    deck: &Deck,
    const_map: &BTreeMap<String, Expr>,
    explicit_bounds: BTreeMap<String, (f64, f64)>,
    unsafe_raw: &Formula,
    dt: f64,
    steps: usize,
    method: TranMethod,
) -> Result<StampedSystem, String> {
    let empty_nodes = BTreeMap::new();
    let mut static_b = AlgebraicBuilder::new(deck.default_vbound, explicit_bounds.clone());

    // 1. Identify grounded voltage sources `V<name> <node> 0 <wave>` so their nodes become exact explicit expressions
    let mut fixed_nodes: BTreeMap<String, Expr> = BTreeMap::new();
    for elem in &deck.elements {
        if let Element::VoltageSource {
            n_pos,
            n_neg,
            wave,
            ..
        } = elem
        {
            if is_ground_node(n_neg) && !is_ground_node(n_pos) {
                fixed_nodes.insert(
                    n_pos.clone(),
                    wave.expr_at(true).substitute(const_map, &empty_nodes, None),
                );
            } else if is_ground_node(n_pos) && !is_ground_node(n_neg) {
                fixed_nodes.insert(
                    n_neg.clone(),
                    Expr::neg(wave.expr_at(true).substitute(const_map, &empty_nodes, None)),
                );
            } else {
                return Err(format!(
                    "floating voltage source between `{n_pos}` and `{n_neg}` in `.mode tran`; ground-reference sources for explicit ODE extraction"
                ));
            }
        }
    }

    // Helper returning expression for any node voltage (0 for ground, source expr for driven nodes, `v_<node>` state otherwise)
    let node_expr = |n: &str, dyn_nodes: &mut BTreeSet<String>| -> Expr {
        if is_ground_node(n) {
            Expr::num(0.0)
        } else if let Some(src) = fixed_nodes.get(n) {
            src.clone()
        } else {
            dyn_nodes.insert(n.to_string());
            Expr::var(format!("v_{}", sanitize_ident(n)))
        }
    };

    let mut dyn_nodes: BTreeSet<String> = BTreeSet::new();
    // Grounded capacitances per dynamic node `C_gnd[node]` and floating 2-node coupling capacitors `(n1, n2, c_expr)`
    let mut node_cap_gnd: BTreeMap<String, Expr> = BTreeMap::new();
    let mut floating_caps: Vec<(String, String, Expr)> = Vec::new();
    // Net conductive / nonlinear current flowing INTO each dynamic node `i_into[node]`
    let mut node_i_into: BTreeMap<String, Expr> = BTreeMap::new();
    // Inductor / MLCC / PCB branch ODE states
    #[derive(Clone)]
    struct IndBranch {
        state_name: String,
        elem_name: String,
        v_across: Expr,
        l_expr: Expr,
        r_ser: Expr,
        bounds: (f64, f64),
    }
    let mut ind_branches: Vec<IndBranch> = Vec::new();
    let mut extra_states: Vec<(String, (f64, f64), Expr, String)> = Vec::new();
    let mut couplings: Vec<(String, String, Expr)> = Vec::new();

    let mut add_cap = |n1: &str,
                       n2: &str,
                       c_val: Expr,
                       dyn_nodes: &mut BTreeSet<String>,
                       node_i_into: &mut BTreeMap<String, Expr>| {
        let fixed_1 = is_ground_node(n1) || fixed_nodes.contains_key(n1);
        let fixed_2 = is_ground_node(n2) || fixed_nodes.contains_key(n2);
        match (fixed_1, fixed_2) {
            (true, true) => {}
            (false, true) => {
                dyn_nodes.insert(n1.to_string());
                let prev = node_cap_gnd
                    .remove(n1)
                    .unwrap_or_else(|| Expr::num(0.0));
                node_cap_gnd.insert(n1.to_string(), Expr::add(prev, c_val.clone()));
                // If n2 is a time-varying driven voltage source `V(t)` (STEP/GAUSS), add `C * dV/dt`!
                if !is_ground_node(n2) {
                    if let Some(v_drv) = fixed_nodes.get(n2) {
                        let dv_dt = symbolic_time_deriv(v_drv);
                        if !matches!(dv_dt, Expr::Num(v) if v == 0.0) {
                            let prev_i = node_i_into
                                .remove(n1)
                                .unwrap_or_else(|| Expr::num(0.0));
                            node_i_into
                                .insert(n1.to_string(), Expr::add(prev_i, Expr::mul(c_val, dv_dt)));
                        }
                    }
                }
            }
            (true, false) => {
                dyn_nodes.insert(n2.to_string());
                let prev = node_cap_gnd
                    .remove(n2)
                    .unwrap_or_else(|| Expr::num(0.0));
                node_cap_gnd.insert(n2.to_string(), Expr::add(prev, c_val.clone()));
                if !is_ground_node(n1) {
                    if let Some(v_drv) = fixed_nodes.get(n1) {
                        let dv_dt = symbolic_time_deriv(v_drv);
                        if !matches!(dv_dt, Expr::Num(v) if v == 0.0) {
                            let prev_i = node_i_into
                                .remove(n2)
                                .unwrap_or_else(|| Expr::num(0.0));
                            node_i_into
                                .insert(n2.to_string(), Expr::add(prev_i, Expr::mul(c_val, dv_dt)));
                        }
                    }
                }
            }
            (false, false) => {
                dyn_nodes.insert(n1.to_string());
                dyn_nodes.insert(n2.to_string());
                floating_caps.push((n1.to_string(), n2.to_string(), c_val));
            }
        }
    };

    let add_current_into =
        |n_from: &str,
         n_to: &str,
         i_expr: Expr,
         dyn_nodes: &mut BTreeSet<String>,
         node_i_into: &mut BTreeMap<String, Expr>| {
            if !is_ground_node(n_from) && !fixed_nodes.contains_key(n_from) {
                dyn_nodes.insert(n_from.to_string());
                let prev = node_i_into
                    .remove(n_from)
                    .unwrap_or_else(|| Expr::num(0.0));
                node_i_into.insert(n_from.to_string(), Expr::sub(prev, i_expr.clone()));
            }
            if !is_ground_node(n_to) && !fixed_nodes.contains_key(n_to) {
                dyn_nodes.insert(n_to.to_string());
                let prev = node_i_into
                    .remove(n_to)
                    .unwrap_or_else(|| Expr::num(0.0));
                node_i_into.insert(n_to.to_string(), Expr::add(prev, i_expr));
            }
        };

    for elem in &deck.elements {
        match elem {
            Element::VoltageSource { .. } => {}
            Element::Resistor {
                name,
                n_pos,
                n_neg,
                r,
            } => {
                let vp = node_expr(n_pos, &mut dyn_nodes);
                let vn = node_expr(n_neg, &mut dyn_nodes);
                let r_e = static_b.lower_expr(&r.substitute(const_map, &fixed_nodes, None), name);
                add_current_into(
                    n_pos,
                    n_neg,
                    Expr::div(Expr::sub(vp, vn), r_e),
                    &mut dyn_nodes,
                    &mut node_i_into,
                );
            }
            Element::Capacitor {
                name,
                n_pos,
                n_neg,
                c,
            } => {
                let c_e = static_b.lower_expr(&c.substitute(const_map, &fixed_nodes, None), name);
                add_cap(n_pos, n_neg, c_e, &mut dyn_nodes, &mut node_i_into);
            }
            Element::MlccCap {
                name,
                n_pos,
                n_neg,
                c0,
                c_min,
                vsat,
                esr,
                esl,
                ..
            } => {
                let sid = sanitize_ident(name);
                let c0_e = static_b.lower_expr(&c0.substitute(const_map, &fixed_nodes, None), name);
                let cmin_e =
                    static_b.lower_expr(&c_min.substitute(const_map, &fixed_nodes, None), name);
                let vsat_e =
                    static_b.lower_expr(&vsat.substitute(const_map, &fixed_nodes, None), name);
                let esr_e =
                    static_b.lower_expr(&esr.substitute(const_map, &fixed_nodes, None), name);
                let esl_e =
                    static_b.lower_expr(&esl.substitute(const_map, &fixed_nodes, None), name);

                let has_esl = !matches!(esl_e, Expr::Num(v) if v == 0.0);
                if has_esl {
                    // Full parasitic series R_esr + L_esl + nonlinear C_eff(vc) branch!
                    let vp = node_expr(n_pos, &mut dyn_nodes);
                    let vn = node_expr(n_neg, &mut dyn_nodes);
                    let vc_name = format!("vc_{sid}");
                    let im_name = format!("i_{sid}");
                    let vc_var = Expr::var(&vc_name);
                    let im_var = Expr::var(&im_name);

                    let ratio2 = Expr::sq(Expr::div(vc_var.clone(), vsat_e));
                    let ceff = Expr::add(
                        cmin_e,
                        Expr::div(c0_e, Expr::add(Expr::num(1.0), ratio2)),
                    );
                    let dvc_dt = Expr::div(im_var.clone(), ceff);
                    extra_states.push((
                        vc_name,
                        explicit_bounds
                            .get(&format!("vc_{sid}"))
                            .copied()
                            .unwrap_or(deck.default_vbound),
                        dvc_dt,
                        format!("Nonlinear voltage-derated MLCC internal voltage [V] ({name})"),
                    ));
                    ind_branches.push(IndBranch {
                        state_name: im_name,
                        elem_name: name.clone(),
                        v_across: Expr::sub(Expr::sub(vp, vn), vc_var),
                        l_expr: esl_e,
                        r_ser: esr_e,
                        bounds: explicit_bounds
                            .get(&format!("i_{sid}"))
                            .copied()
                            .unwrap_or((-25.0, 25.0)),
                    });
                    add_current_into(n_pos, n_neg, im_var, &mut dyn_nodes, &mut node_i_into);
                } else {
                    // Pure voltage-dependent nonlinear capacitance C(v) = C_min + C0 / (1 + (v/Vsat)^2)
                    // (e.g., GaN HEMT depletion Miller C_gd(v_ds)!)
                    let vp = node_expr(n_pos, &mut dyn_nodes);
                    let vn = node_expr(n_neg, &mut dyn_nodes);
                    let v_diff = Expr::sub(vp, vn);
                    let ratio2 = Expr::sq(Expr::div(v_diff, vsat_e));
                    let ceff = Expr::add(
                        cmin_e,
                        Expr::div(c0_e, Expr::add(Expr::num(1.0), ratio2)),
                    );
                    add_cap(n_pos, n_neg, ceff, &mut dyn_nodes, &mut node_i_into);
                }
            }
            Element::Inductor {
                name,
                n_pos,
                n_neg,
                l,
                r_ser,
            } => {
                let sid = sanitize_ident(name);
                let vp = node_expr(n_pos, &mut dyn_nodes);
                let vn = node_expr(n_neg, &mut dyn_nodes);
                let l_e = static_b.lower_expr(&l.substitute(const_map, &fixed_nodes, None), name);
                let rs_e =
                    static_b.lower_expr(&r_ser.substitute(const_map, &fixed_nodes, None), name);
                let iname = format!("i_{sid}");
                let ivar = Expr::var(&iname);
                ind_branches.push(IndBranch {
                    state_name: iname.clone(),
                    elem_name: name.clone(),
                    v_across: Expr::sub(vp, vn),
                    l_expr: l_e,
                    r_ser: rs_e,
                    bounds: explicit_bounds.get(&iname).copied().unwrap_or((-25.0, 25.0)),
                });
                add_current_into(n_pos, n_neg, ivar, &mut dyn_nodes, &mut node_i_into);
            }
            Element::CoupledInductors {
                name,
                l1_name,
                l2_name,
                k,
            } => {
                let k_e = static_b.lower_expr(&k.substitute(const_map, &fixed_nodes, None), name);
                couplings.push((l1_name.clone(), l2_name.clone(), k_e));
            }
            Element::CurrentSource {
                n_pos,
                n_neg,
                wave,
                ..
            } => {
                let isrc = wave.expr_at(true).substitute(const_map, &fixed_nodes, None);
                add_current_into(n_pos, n_neg, isrc, &mut dyn_nodes, &mut node_i_into);
            }
            Element::Diode {
                name,
                n_anode,
                n_cathode,
                model,
                area,
                vt_override,
            } => {
                let m = deck
                    .models
                    .get(model)
                    .ok_or_else(|| format!("unknown diode model `{model}` on `{name}`"))?;
                let va = node_expr(n_anode, &mut dyn_nodes);
                let vk = node_expr(n_cathode, &mut dyn_nodes);
                let is_val = model_param(m, "is", 1.0e-14);
                let n_id = model_param(m, "n", 1.0);
                let vt_e = static_b.lower_expr(
                    &resolve_vt(vt_override, &None, m).substitute(const_map, &fixed_nodes, None),
                    name,
                );
                let area_e =
                    static_b.lower_expr(&area.substitute(const_map, &fixed_nodes, None), name);
                let id_expr = Expr::mul(
                    Expr::mul(area_e, is_val),
                    Expr::sub(
                        Expr::exp(Expr::div(Expr::sub(va, vk), Expr::mul(n_id, vt_e))),
                        Expr::num(1.0),
                    ),
                );
                add_current_into(n_anode, n_cathode, id_expr, &mut dyn_nodes, &mut node_i_into);
            }
            Element::Mosfet {
                name,
                n_drain,
                n_gate,
                n_source,
                n_bulk,
                model,
                w,
                l,
                nfin,
                dtfin_nm,
                dvth,
                dlisp_nm,
                rth,
                vt_override,
                tamb_k,
            } => {
                let m = deck
                    .models
                    .get(model)
                    .ok_or_else(|| format!("unknown MOSFET model `{model}` on `{name}`"))?;
                let vd = node_expr(n_drain, &mut dyn_nodes);
                let vg = node_expr(n_gate, &mut dyn_nodes);
                let vs = node_expr(n_source, &mut dyn_nodes);
                let vb = node_expr(n_bulk, &mut dyn_nodes);

                let w_s = w.substitute(const_map, &fixed_nodes, None);
                let l_s = l.substitute(const_map, &fixed_nodes, None);
                let nfin_s = nfin.substitute(const_map, &fixed_nodes, None);
                let dtfin_s = dtfin_nm.substitute(const_map, &fixed_nodes, None);
                let dvth_s = dvth.substitute(const_map, &fixed_nodes, None);
                let rth_s = rth.as_ref().map(|e| e.substitute(const_map, &fixed_nodes, None));
                let vt_s = vt_override
                    .as_ref()
                    .map(|e| e.substitute(const_map, &fixed_nodes, None));
                let tamb_s = tamb_k
                    .as_ref()
                    .map(|e| e.substitute(const_map, &fixed_nodes, None));

                let ids = build_mos_current(
                    &mut static_b,
                    name,
                    m,
                    vd,
                    vg,
                    vs,
                    vb,
                    &w_s,
                    &l_s,
                    &nfin_s,
                    &dtfin_s,
                    &dvth_s,
                    &rth_s,
                    &vt_s,
                    &tamb_s,
                    false,
                )?;
                add_current_into(n_drain, n_source, ids, &mut dyn_nodes, &mut node_i_into);

                // For 2nm GAA nanosheet (`gt2n`), stamp inner-spacer fringing capacitance C_isp(dL_isp)
                // across gate-to-source/rail (Miller-equivalent 2*C_isp) and drain-to-source/rail (C_isp).
                if matches!(m.kind, ModelKind::GaaNmos | ModelKind::GaaPmos) {
                    let lisp0 = model_param(m, "lisp_nm", 5.5);
                    let dlisp = static_b
                        .lower_expr(&dlisp_nm.substitute(const_map, &fixed_nodes, None), name);
                    let nsh = static_b.lower_expr(&nfin_s, name);
                    // ~0.18 fF*nm / (L_isp0 + dL_isp) per stacked sheet
                    let c_isp = Expr::div(
                        Expr::mul(Expr::num(1.8e-16), nsh),
                        Expr::add(lisp0, dlisp),
                    );
                    add_cap(
                        n_gate,
                        n_source,
                        Expr::mul(Expr::num(2.0), c_isp.clone()),
                        &mut dyn_nodes,
                        &mut node_i_into,
                    );
                    add_cap(n_drain, n_source, c_isp, &mut dyn_nodes, &mut node_i_into);
                }
            }
            Element::PcbMicrostrip {
                name,
                n_in,
                n_out,
                n_ref,
                len,
                w0,
                dw,
                h0,
                dh,
                t_cu,
                er,
                sigma_cu,
            } => {
                let (_, _, ltot, ctot, rdc) = stamp_pcb_microstrip_geom(
                    &mut static_b,
                    name,
                    &len.substitute(const_map, &fixed_nodes, None),
                    &w0.substitute(const_map, &fixed_nodes, None),
                    &dw.substitute(const_map, &fixed_nodes, None),
                    &h0.substitute(const_map, &fixed_nodes, None),
                    &dh.substitute(const_map, &fixed_nodes, None),
                    &t_cu.substitute(const_map, &fixed_nodes, None),
                    &er.substitute(const_map, &fixed_nodes, None),
                    &sigma_cu.substitute(const_map, &fixed_nodes, None),
                );
                let c_half = Expr::mul(Expr::num(0.5), ctot);
                add_cap(n_in, n_ref, c_half.clone(), &mut dyn_nodes, &mut node_i_into);
                add_cap(n_out, n_ref, c_half, &mut dyn_nodes, &mut node_i_into);

                let sid = sanitize_ident(name);
                let iname = format!("i_tl_{sid}");
                let ivar = Expr::var(&iname);
                let vin = node_expr(n_in, &mut dyn_nodes);
                let vout = node_expr(n_out, &mut dyn_nodes);
                ind_branches.push(IndBranch {
                    state_name: iname.clone(),
                    elem_name: name.clone(),
                    v_across: Expr::sub(vin, vout),
                    l_expr: ltot,
                    r_ser: rdc,
                    bounds: explicit_bounds.get(&iname).copied().unwrap_or((-5.0, 5.0)),
                });
                add_current_into(n_in, n_out, ivar, &mut dyn_nodes, &mut node_i_into);
            }
            Element::PcbCoupledDiffpair {
                name,
                in_p,
                in_n,
                out_p,
                out_n,
                ref_in,
                ref_out,
                len,
                w0,
                dw,
                s0,
                ds,
                h0,
                dh,
                t_cu,
                er_p,
                er_n,
                l_via,
                l_slot,
                r_ret,
            } => {
                let (_, kc, l_p, l_n, c_p, c_n, cm, _lm, rdc) = stamp_pcb_diffpair_geom(
                    &mut static_b,
                    name,
                    &len.substitute(const_map, &fixed_nodes, None),
                    &w0.substitute(const_map, &fixed_nodes, None),
                    &dw.substitute(const_map, &fixed_nodes, None),
                    &s0.substitute(const_map, &fixed_nodes, None),
                    &ds.substitute(const_map, &fixed_nodes, None),
                    &h0.substitute(const_map, &fixed_nodes, None),
                    &dh.substitute(const_map, &fixed_nodes, None),
                    &t_cu.substitute(const_map, &fixed_nodes, None),
                    &er_p.substitute(const_map, &fixed_nodes, None),
                    &er_n.substitute(const_map, &fixed_nodes, None),
                );
                let lvia_e = static_b
                    .lower_expr(&l_via.substitute(const_map, &fixed_nodes, None), name);
                let lslot_e = static_b
                    .lower_expr(&l_slot.substitute(const_map, &fixed_nodes, None), name);
                let rret_e = static_b
                    .lower_expr(&r_ret.substitute(const_map, &fixed_nodes, None), name);

                // Pi-section self & mutual capacitances at launch and receiver ends
                let cp_half = Expr::mul(Expr::num(0.5), c_p);
                let cn_half = Expr::mul(Expr::num(0.5), c_n);
                let cm_half = Expr::mul(Expr::num(0.5), cm);
                add_cap(in_p, ref_in, cp_half.clone(), &mut dyn_nodes, &mut node_i_into);
                add_cap(out_p, ref_out, cp_half, &mut dyn_nodes, &mut node_i_into);
                add_cap(in_n, ref_in, cn_half.clone(), &mut dyn_nodes, &mut node_i_into);
                add_cap(out_n, ref_out, cn_half, &mut dyn_nodes, &mut node_i_into);
                add_cap(in_p, in_n, cm_half.clone(), &mut dyn_nodes, &mut node_i_into);
                add_cap(out_p, out_n, cm_half, &mut dyn_nodes, &mut node_i_into);

                // Coupled p/n trace series inductances (including via backdrill stub inductance L_via)
                let sid = sanitize_ident(name);
                let lp_tot = Expr::add(l_p, lvia_e.clone());
                let ln_tot = Expr::add(l_n, lvia_e);
                let ip_name = format!("i_{sid}_p");
                let in_name = format!("i_{sid}_n");
                let vip = node_expr(in_p, &mut dyn_nodes);
                let vop = node_expr(out_p, &mut dyn_nodes);
                let vin = node_expr(in_n, &mut dyn_nodes);
                let von = node_expr(out_n, &mut dyn_nodes);

                ind_branches.push(IndBranch {
                    state_name: ip_name.clone(),
                    elem_name: format!("{name}_p"),
                    v_across: Expr::sub(vip, vop),
                    l_expr: lp_tot,
                    r_ser: rdc.clone(),
                    bounds: explicit_bounds.get(&ip_name).copied().unwrap_or((-5.0, 5.0)),
                });
                ind_branches.push(IndBranch {
                    state_name: in_name.clone(),
                    elem_name: format!("{name}_n"),
                    v_across: Expr::sub(vin, von),
                    l_expr: ln_tot,
                    r_ser: rdc,
                    bounds: explicit_bounds.get(&in_name).copied().unwrap_or((-5.0, 5.0)),
                });
                couplings.push((format!("{name}_p"), format!("{name}_n"), kc));
                add_current_into(
                    in_p,
                    out_p,
                    Expr::var(&ip_name),
                    &mut dyn_nodes,
                    &mut node_i_into,
                );
                add_current_into(
                    in_n,
                    out_n,
                    Expr::var(&in_name),
                    &mut dyn_nodes,
                    &mut node_i_into,
                );

                // Return-plane reference path between ref_in and ref_out (split-plane slot L_slot + R_ret, or resistive R_ret)
                if ref_in != ref_out {
                    let vri = node_expr(ref_in, &mut dyn_nodes);
                    let vro = node_expr(ref_out, &mut dyn_nodes);
                    if !matches!(lslot_e, Expr::Num(v) if v == 0.0) {
                        let islot_name = format!("i_slot_{sid}");
                        ind_branches.push(IndBranch {
                            state_name: islot_name.clone(),
                            elem_name: format!("{name}_slot"),
                            v_across: Expr::sub(vri, vro),
                            l_expr: lslot_e,
                            r_ser: rret_e,
                            bounds: explicit_bounds
                                .get(&islot_name)
                                .copied()
                                .unwrap_or((-5.0, 5.0)),
                        });
                        add_current_into(
                            ref_in,
                            ref_out,
                            Expr::var(&islot_name),
                            &mut dyn_nodes,
                            &mut node_i_into,
                        );
                    } else {
                        add_current_into(
                            ref_in,
                            ref_out,
                            Expr::div(Expr::sub(vri, vro), rret_e),
                            &mut dyn_nodes,
                            &mut node_i_into,
                        );
                    }
                }
            }
            other => {
                return Err(format!(
                    "element `{other:?}` is only supported in `.mode dc`"
                ));
            }
        }
    }

    // Solve capacitance matrix for dynamic node voltage derivatives `dv/dt`!
    // Partition dynamic nodes into connected floating-capacitor components (size 1, 2, or 3)
    // and invert each component's symmetric positive-definite nodal capacitance matrix C * dv/dt = I exactly!
    let mut adj: BTreeMap<String, BTreeMap<String, Expr>> = BTreeMap::new();
    for (n1, n2, cm) in &floating_caps {
        let e12 = adj
            .entry(n1.clone())
            .or_default()
            .remove(n2)
            .unwrap_or_else(|| Expr::num(0.0));
        adj.entry(n1.clone())
            .or_default()
            .insert(n2.clone(), Expr::add(e12, cm.clone()));

        let e21 = adj
            .entry(n2.clone())
            .or_default()
            .remove(n1)
            .unwrap_or_else(|| Expr::num(0.0));
        adj.entry(n2.clone())
            .or_default()
            .insert(n1.clone(), Expr::add(e21, cm.clone()));
    }

    let mut init_map: BTreeMap<String, InitSpec> = BTreeMap::new();
    for id in &deck.inits {
        let spec = match &id.spec {
            InitSpec::Interval(lo, hi) => InitSpec::Interval(*lo, *hi),
            InitSpec::Exact(e) => {
                InitSpec::Exact(e.substitute(const_map, &fixed_nodes, Some(&Expr::num(0.0))))
            }
        };
        init_map.insert(id.target.clone(), spec);
    }

    let mut dv_dt_by_node: BTreeMap<String, Expr> = BTreeMap::new();
    let mut visited_cap: BTreeSet<String> = BTreeSet::new();
    for start_node in &dyn_nodes {
        if visited_cap.contains(start_node) {
            continue;
        }
        let mut comp = Vec::new();
        let mut stack = vec![start_node.clone()];
        visited_cap.insert(start_node.clone());
        while let Some(u) = stack.pop() {
            comp.push(u.clone());
            if let Some(nbrs) = adj.get(&u) {
                for v in nbrs.keys() {
                    if visited_cap.insert(v.clone()) {
                        stack.push(v.clone());
                    }
                }
            }
        }
        comp.sort();

        match comp.len() {
            1 => {
                let n0 = &comp[0];
                let i0 = node_i_into
                    .get(n0)
                    .cloned()
                    .unwrap_or_else(|| Expr::num(0.0));
                let c0 = node_cap_gnd.get(n0).cloned().ok_or_else(|| {
                    format!("dynamic node `{n0}` in `.mode tran` has no capacitance to ground/rail")
                })?;
                dv_dt_by_node.insert(n0.clone(), Expr::div(i0, c0));
            }
            2 => {
                let (n0, n1) = (&comp[0], &comp[1]);
                let c0 = node_cap_gnd.get(n0).cloned().ok_or_else(|| {
                    format!("coupled dynamic node `{n0}` in `.mode tran` has no ground capacitance")
                })?;
                let c1 = node_cap_gnd.get(n1).cloned().ok_or_else(|| {
                    format!("coupled dynamic node `{n1}` in `.mode tran` has no ground capacitance")
                })?;
                let cm = adj[n0][n1].clone();
                let i0 = node_i_into
                    .get(n0)
                    .cloned()
                    .unwrap_or_else(|| Expr::num(0.0));
                let i1 = node_i_into
                    .get(n1)
                    .cloned()
                    .unwrap_or_else(|| Expr::num(0.0));
                let det = Expr::add(
                    Expr::mul(c0.clone(), c1.clone()),
                    Expr::mul(cm.clone(), Expr::add(c0.clone(), c1.clone())),
                );
                let num0 = Expr::add(
                    Expr::mul(Expr::add(c1, cm.clone()), i0.clone()),
                    Expr::mul(cm.clone(), i1.clone()),
                );
                let num1 = Expr::add(
                    Expr::mul(Expr::add(c0, cm.clone()), i1),
                    Expr::mul(cm, i0),
                );
                dv_dt_by_node.insert(n0.clone(), Expr::div(num0, det.clone()));
                dv_dt_by_node.insert(n1.clone(), Expr::div(num1, det));
            }
            3 => {
                // Exact 3x3 symmetric nodal capacitance matrix C * dv/dt = I (e.g. diffpair + split reference plane!)
                let mut cg = Vec::with_capacity(3);
                let mut iv = Vec::with_capacity(3);
                for nk in &comp {
                    cg.push(
                        node_cap_gnd
                            .get(nk)
                            .cloned()
                            .unwrap_or_else(|| Expr::num(0.0)),
                    );
                    iv.push(
                        node_i_into
                            .get(nk)
                            .cloned()
                            .unwrap_or_else(|| Expr::num(0.0)),
                    );
                }
                let cm01 = adj
                    .get(&comp[0])
                    .and_then(|m| m.get(&comp[1]))
                    .cloned()
                    .unwrap_or_else(|| Expr::num(0.0));
                let cm02 = adj
                    .get(&comp[0])
                    .and_then(|m| m.get(&comp[2]))
                    .cloned()
                    .unwrap_or_else(|| Expr::num(0.0));
                let cm12 = adj
                    .get(&comp[1])
                    .and_then(|m| m.get(&comp[2]))
                    .cloned()
                    .unwrap_or_else(|| Expr::num(0.0));

                let a00 = Expr::add(cg[0].clone(), Expr::add(cm01.clone(), cm02.clone()));
                let a11 = Expr::add(cg[1].clone(), Expr::add(cm01.clone(), cm12.clone()));
                let a22 = Expr::add(cg[2].clone(), Expr::add(cm02.clone(), cm12.clone()));
                let a01 = Expr::neg(cm01);
                let a02 = Expr::neg(cm02);
                let a12 = Expr::neg(cm12);

                // Symmetric cofactors M_ij
                let m00 = Expr::sub(Expr::mul(a11.clone(), a22.clone()), Expr::sq(a12.clone()));
                let m11 = Expr::sub(Expr::mul(a00.clone(), a22.clone()), Expr::sq(a02.clone()));
                let m22 = Expr::sub(Expr::mul(a00.clone(), a11.clone()), Expr::sq(a01.clone()));
                let m01 = Expr::sub(
                    Expr::mul(a02.clone(), a12.clone()),
                    Expr::mul(a01.clone(), a22.clone()),
                );
                let m02 = Expr::sub(
                    Expr::mul(a01.clone(), a12.clone()),
                    Expr::mul(a11.clone(), a02.clone()),
                );
                let m12 = Expr::sub(
                    Expr::mul(a01.clone(), a02.clone()),
                    Expr::mul(a00.clone(), a12),
                );

                let det = Expr::add(
                    Expr::mul(a00, m00.clone()),
                    Expr::add(Expr::mul(a01, m01.clone()), Expr::mul(a02, m02.clone())),
                );

                let num0 = Expr::add(
                    Expr::mul(m00, iv[0].clone()),
                    Expr::add(
                        Expr::mul(m01.clone(), iv[1].clone()),
                        Expr::mul(m02.clone(), iv[2].clone()),
                    ),
                );
                let num1 = Expr::add(
                    Expr::mul(m01, iv[0].clone()),
                    Expr::add(
                        Expr::mul(m11, iv[1].clone()),
                        Expr::mul(m12.clone(), iv[2].clone()),
                    ),
                );
                let num2 = Expr::add(
                    Expr::mul(m02, iv[0].clone()),
                    Expr::add(Expr::mul(m12, iv[1].clone()), Expr::mul(m22, iv[2].clone())),
                );
                dv_dt_by_node.insert(comp[0].clone(), Expr::div(num0, det.clone()));
                dv_dt_by_node.insert(comp[1].clone(), Expr::div(num1, det.clone()));
                dv_dt_by_node.insert(comp[2].clone(), Expr::div(num2, det));
            }
            k => {
                return Err(format!(
                    "floating capacitor cluster of size {k} > 3 at `{}`; split with ground reference",
                    comp[0]
                ));
            }
        }
    }

    let mut states: Vec<OdeState> = Vec::new();
    for node in &dyn_nodes {
        let vname = format!("v_{}", sanitize_ident(node));
        let rhs = dv_dt_by_node[node].clone();
        let (lo, hi) = explicit_bounds
            .get(&vname)
            .copied()
            .unwrap_or(deck.default_vbound);
        let init = init_map
            .get(&vname)
            .cloned()
            .unwrap_or(InitSpec::Exact(Expr::num(0.0)));
        states.push(OdeState {
            name: vname,
            lo,
            hi,
            init,
            rhs,
            comment: format!("Dynamic node voltage v({node}) [V]"),
        });
    }

    // Solve inductor ODEs (including coupled mutual inductor pairs `K`)
    let mut coupled_map: BTreeMap<String, (String, Expr)> = BTreeMap::new();
    for (l1n, l2n, k_e) in &couplings {
        coupled_map.insert(l1n.clone(), (l2n.clone(), k_e.clone()));
        coupled_map.insert(l2n.clone(), (l1n.clone(), k_e.clone()));
    }
    let ind_by_elem: BTreeMap<String, IndBranch> = ind_branches
        .iter()
        .map(|ib| (ib.elem_name.clone(), ib.clone()))
        .collect();

    for ib in &ind_branches {
        let v1_eff = Expr::sub(
            ib.v_across.clone(),
            Expr::mul(ib.r_ser.clone(), Expr::var(&ib.state_name)),
        );
        let rhs = if let Some((partner_name, k_e)) = coupled_map.get(&ib.elem_name) {
            let pb = ind_by_elem
                .get(partner_name)
                .ok_or_else(|| format!("coupled inductor `{partner_name}` not found"))?;
            let v2_eff = Expr::sub(
                pb.v_across.clone(),
                Expr::mul(pb.r_ser.clone(), Expr::var(&pb.state_name)),
            );
            // M^2 = k^2 * L1 * L2; introduce static M >= 0
            let pair_key = if ib.elem_name <= *partner_name {
                format!("M_{}_{}", sanitize_ident(&ib.elem_name), sanitize_ident(partner_name))
            } else {
                format!("M_{}_{}", sanitize_ident(partner_name), sanitize_ident(&ib.elem_name))
            };
            let m_var = static_b.positive_sqrt(
                &pair_key,
                (0.0, 1.0e-3),
                Expr::mul(
                    Expr::sq(k_e.clone()),
                    Expr::mul(ib.l_expr.clone(), pb.l_expr.clone()),
                ),
                &format!("Mutual inductance M between {} and {}", ib.elem_name, partner_name),
            );
            let det = Expr::sub(
                Expr::mul(ib.l_expr.clone(), pb.l_expr.clone()),
                Expr::sq(m_var.clone()),
            );
            Expr::div(
                Expr::sub(
                    Expr::mul(pb.l_expr.clone(), v1_eff),
                    Expr::mul(m_var, v2_eff),
                ),
                det,
            )
        } else {
            Expr::div(v1_eff, ib.l_expr.clone())
        };
        let init = init_map
            .get(&ib.state_name)
            .cloned()
            .unwrap_or(InitSpec::Exact(Expr::num(0.0)));
        states.push(OdeState {
            name: ib.state_name.clone(),
            lo: ib.bounds.0,
            hi: ib.bounds.1,
            init,
            rhs,
            comment: format!("Inductor / interconnect branch current ({}) [A]", ib.elem_name),
        });
    }

    for (sname, (lo, hi), rhs, comment) in extra_states {
        let init = init_map
            .get(&sname)
            .cloned()
            .unwrap_or(InitSpec::Exact(Expr::num(0.0)));
        states.push(OdeState {
            name: sname,
            lo,
            hi,
            init,
            rhs,
            comment,
        });
    }

    // Map `NodeVolt(n)` in `unsafe_formula` to either fixed source expr or `Var("v_<n>")`
    let mut node_to_state = fixed_nodes.clone();
    for dn in &dyn_nodes {
        node_to_state.insert(dn.clone(), Expr::var(format!("v_{}", sanitize_ident(dn))));
    }
    let unsafe_mapped = unsafe_raw.substitute(const_map, &node_to_state, None);

    Ok(StampedSystem {
        title: deck.title.clone(),
        pdk: deck.pdk,
        expected: deck.expected,
        params: deck.params.clone(),
        body: StampedBody::Ode {
            static_vars: static_b.vars,
            static_constraints: static_b.constraints,
            states,
            dt,
            steps,
            method,
        },
        unsafe_formula: unsafe_mapped,
    })
}

/// Symbolic derivative `d(e)/dt` for smooth `GAUSS` / `STEP` voltage-source waveforms coupled through Miller `C_gd`.
fn symbolic_time_deriv(e: &Expr) -> Expr {
    match e {
        Expr::Num(_) | Expr::Var(_) | Expr::NodeVolt(_) => Expr::num(0.0),
        Expr::Time => Expr::num(1.0),
        Expr::Neg(a) => Expr::neg(symbolic_time_deriv(a)),
        Expr::Add(a, b) => Expr::add(symbolic_time_deriv(a), symbolic_time_deriv(b)),
        Expr::Sub(a, b) => Expr::sub(symbolic_time_deriv(a), symbolic_time_deriv(b)),
        Expr::Mul(a, b) => Expr::add(
            Expr::mul(symbolic_time_deriv(a), (**b).clone()),
            Expr::mul((**a).clone(), symbolic_time_deriv(b)),
        ),
        Expr::Div(a, b) => {
            let da = symbolic_time_deriv(a);
            let db = symbolic_time_deriv(b);
            let num = Expr::sub(Expr::mul(da, (**b).clone()), Expr::mul((**a).clone(), db));
            Expr::div(num, Expr::sq((**b).clone()))
        }
        Expr::Exp(a) => Expr::mul(Expr::exp((**a).clone()), symbolic_time_deriv(a)),
        Expr::Ln1pExp(a) => {
            let da = symbolic_time_deriv(a);
            let ez = Expr::exp((**a).clone());
            Expr::div(Expr::mul(ez, da), Expr::add(Expr::num(1.0), Expr::exp((**a).clone())))
        }
    }
}
