//! Core abstract syntax tree and symbolic mathematical expressions for `spice2smt`.

use std::collections::BTreeMap;
use std::fmt;

use crate::pdk::PdkId;

/// Expected solver result metadata for benchmark validation (`(set-info :status ...)`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExpectedStatus {
    Sat,
    Unsat,
}

impl ExpectedStatus {
    pub fn as_smt2_str(self) -> &'static str {
        match self {
            ExpectedStatus::Sat => "sat",
            ExpectedStatus::Unsat => "unsat",
        }
    }
}

/// Time-discretization scheme used when lowering `.mode tran` into `smt2-exp`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TranMethod {
    BackwardEuler,
    Trapezoidal,
}

/// Circuit or multiphysics analysis mode.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum AnalysisMode {
    Dc,
    Tran {
        dt: f64,
        steps: usize,
        method: TranMethod,
    },
}

/// Output target dialect for `spice2smt`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dialect {
    /// Standard SMT-LIB2 `QF_NRA` extended with transcendental `(exp ...)`.
    /// Lowers `ln(1 + exp(z))` and `ln(...)` purely to `exp` via auxiliary variables,
    /// and lowers `.mode tran` to implicit Backward-Euler or Trapezoidal algebraic steps.
    Smt2Exp,
    /// `dReal` continuous ODE + transcendental SMT-LIB2 dialect using `(define-ode ...)`
    /// and `(forall_t ...)` for `.mode tran` decks.
    DrealOde,
    /// Machine-checked Lean 4 `Prop` target specification over `TranscendentalField`.
    Lean4,
}

/// Symbolic real-valued expression over circuit nodes, parameters, and `exp`.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Num(f64),
    Var(String),
    NodeVolt(String),
    Time,
    Neg(Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Exp(Box<Expr>),
    /// Smooth softplus `ln(1 + exp(z))` used in unified surface-potential / EKV / BSIM-CMG / ASM-HEMT cores.
    /// Lowered to pure `exp` auxiliary constraint `exp(y) = 1 + exp(z), y > 0` in `smt2-exp`,
    /// or `(log (+ 1.0 (exp z)))` inside explicit `dreal-ode` vector fields.
    Ln1pExp(Box<Expr>),
}

#[allow(clippy::should_implement_trait)]
impl Expr {
    pub fn num(v: f64) -> Self {
        Expr::Num(v)
    }

    pub fn var(name: impl Into<String>) -> Self {
        Expr::Var(name.into())
    }

    pub fn node(name: impl Into<String>) -> Self {
        let s = name.into();
        if is_ground_node(&s) {
            Expr::Num(0.0)
        } else {
            Expr::NodeVolt(s)
        }
    }

    pub fn add(a: Expr, b: Expr) -> Self {
        match (&a, &b) {
            (Expr::Num(x), _) if *x == 0.0 => b,
            (_, Expr::Num(y)) if *y == 0.0 => a,
            (Expr::Num(x), Expr::Num(y)) => Expr::Num(x + y),
            _ => Expr::Add(Box::new(a), Box::new(b)),
        }
    }

    pub fn sub(a: Expr, b: Expr) -> Self {
        match (&a, &b) {
            (_, Expr::Num(y)) if *y == 0.0 => a,
            (Expr::Num(x), _) if *x == 0.0 => Expr::neg(b),
            (Expr::Num(x), Expr::Num(y)) => Expr::Num(x - y),
            _ => Expr::Sub(Box::new(a), Box::new(b)),
        }
    }

    pub fn mul(a: Expr, b: Expr) -> Self {
        match (&a, &b) {
            (Expr::Num(x), _) if *x == 0.0 => Expr::Num(0.0),
            (_, Expr::Num(y)) if *y == 0.0 => Expr::Num(0.0),
            (Expr::Num(x), _) if *x == 1.0 => b,
            (_, Expr::Num(y)) if *y == 1.0 => a,
            (Expr::Num(x), Expr::Num(y)) => Expr::Num(x * y),
            _ => Expr::Mul(Box::new(a), Box::new(b)),
        }
    }

    pub fn div(a: Expr, b: Expr) -> Self {
        match (&a, &b) {
            (Expr::Num(x), _) if *x == 0.0 => Expr::Num(0.0),
            (_, Expr::Num(y)) if *y == 1.0 => a,
            (Expr::Num(x), Expr::Num(y)) if *y != 0.0 => Expr::Num(x / y),
            _ => Expr::Div(Box::new(a), Box::new(b)),
        }
    }

    pub fn neg(a: Expr) -> Self {
        match a {
            Expr::Num(x) => Expr::Num(-x),
            Expr::Neg(inner) => *inner,
            other => Expr::Neg(Box::new(other)),
        }
    }

    pub fn sq(a: Expr) -> Self {
        Expr::mul(a.clone(), a)
    }

    pub fn exp(a: Expr) -> Self {
        Expr::Exp(Box::new(a))
    }

    pub fn ln1p_exp(a: Expr) -> Self {
        Expr::Ln1pExp(Box::new(a))
    }

    /// Substitute named constants and fixed node voltages recursively.
    pub fn substitute(
        &self,
        var_map: &BTreeMap<String, Expr>,
        node_map: &BTreeMap<String, Expr>,
        time_expr: Option<&Expr>,
    ) -> Expr {
        match self {
            Expr::Num(v) => Expr::Num(*v),
            Expr::Var(name) => {
                if let Some(rep) = var_map.get(name) {
                    rep.substitute(var_map, node_map, time_expr)
                } else {
                    Expr::Var(name.clone())
                }
            }
            Expr::NodeVolt(n) => {
                if is_ground_node(n) {
                    Expr::Num(0.0)
                } else if let Some(rep) = node_map.get(n) {
                    rep.substitute(var_map, node_map, time_expr)
                } else {
                    Expr::NodeVolt(n.clone())
                }
            }
            Expr::Time => time_expr.cloned().unwrap_or(Expr::Time),
            Expr::Neg(e) => Expr::neg(e.substitute(var_map, node_map, time_expr)),
            Expr::Add(a, b) => Expr::add(
                a.substitute(var_map, node_map, time_expr),
                b.substitute(var_map, node_map, time_expr),
            ),
            Expr::Sub(a, b) => Expr::sub(
                a.substitute(var_map, node_map, time_expr),
                b.substitute(var_map, node_map, time_expr),
            ),
            Expr::Mul(a, b) => Expr::mul(
                a.substitute(var_map, node_map, time_expr),
                b.substitute(var_map, node_map, time_expr),
            ),
            Expr::Div(a, b) => Expr::div(
                a.substitute(var_map, node_map, time_expr),
                b.substitute(var_map, node_map, time_expr),
            ),
            Expr::Exp(e) => Expr::exp(e.substitute(var_map, node_map, time_expr)),
            Expr::Ln1pExp(e) => Expr::ln1p_exp(e.substitute(var_map, node_map, time_expr)),
        }
    }

    /// Evaluate a symbolic expression numerically on a point valuation (for tests & witness checks).
    pub fn eval_f64(&self, env: &BTreeMap<String, f64>, t: f64) -> Result<f64, String> {
        match self {
            Expr::Num(v) => Ok(*v),
            Expr::Var(name) => env
                .get(name)
                .copied()
                .ok_or_else(|| format!("unbound variable `{name}`")),
            Expr::NodeVolt(node) => {
                if is_ground_node(node) {
                    Ok(0.0)
                } else {
                    let key = format!("v_{}", sanitize_ident(node));
                    env.get(&key)
                        .or_else(|| env.get(node))
                        .copied()
                        .ok_or_else(|| format!("unbound node voltage `{key}`"))
                }
            }
            Expr::Time => Ok(t),
            Expr::Neg(e) => Ok(-e.eval_f64(env, t)?),
            Expr::Add(a, b) => Ok(a.eval_f64(env, t)? + b.eval_f64(env, t)?),
            Expr::Sub(a, b) => Ok(a.eval_f64(env, t)? - b.eval_f64(env, t)?),
            Expr::Mul(a, b) => Ok(a.eval_f64(env, t)? * b.eval_f64(env, t)?),
            Expr::Div(a, b) => {
                let den = b.eval_f64(env, t)?;
                if den == 0.0 {
                    Err("division by zero in Expr::eval_f64".to_string())
                } else {
                    Ok(a.eval_f64(env, t)? / den)
                }
            }
            Expr::Exp(e) => Ok(e.eval_f64(env, t)?.exp()),
            Expr::Ln1pExp(e) => {
                let z = e.eval_f64(env, t)?;
                if z > 30.0 {
                    Ok(z + (-z).exp().ln_1p())
                } else {
                    Ok(z.exp().ln_1p())
                }
            }
        }
    }
}

/// Comparison operators in `.unsafe` and stamped equations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpOp {
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
}

impl fmt::Display for CmpOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CmpOp::Eq => write!(f, "="),
            CmpOp::Lt => write!(f, "<"),
            CmpOp::Le => write!(f, "<="),
            CmpOp::Gt => write!(f, ">"),
            CmpOp::Ge => write!(f, ">="),
        }
    }
}

/// Quantifier-free boolean formula over real expressions.
#[derive(Debug, Clone, PartialEq)]
pub enum Formula {
    Cmp { op: CmpOp, lhs: Expr, rhs: Expr },
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Not(Box<Formula>),
}

impl Formula {
    pub fn substitute(
        &self,
        var_map: &BTreeMap<String, Expr>,
        node_map: &BTreeMap<String, Expr>,
        time_expr: Option<&Expr>,
    ) -> Formula {
        match self {
            Formula::Cmp { op, lhs, rhs } => Formula::Cmp {
                op: *op,
                lhs: lhs.substitute(var_map, node_map, time_expr),
                rhs: rhs.substitute(var_map, node_map, time_expr),
            },
            Formula::And(items) => Formula::And(
                items
                    .iter()
                    .map(|f| f.substitute(var_map, node_map, time_expr))
                    .collect(),
            ),
            Formula::Or(items) => Formula::Or(
                items
                    .iter()
                    .map(|f| f.substitute(var_map, node_map, time_expr))
                    .collect(),
            ),
            Formula::Not(inner) => {
                Formula::Not(Box::new(inner.substitute(var_map, node_map, time_expr)))
            }
        }
    }

    pub fn eval_f64(&self, env: &BTreeMap<String, f64>, t: f64) -> Result<bool, String> {
        match self {
            Formula::Cmp { op, lhs, rhs } => {
                let l = lhs.eval_f64(env, t)?;
                let r = rhs.eval_f64(env, t)?;
                Ok(match op {
                    CmpOp::Eq => (l - r).abs() <= 1e-12,
                    CmpOp::Lt => l < r,
                    CmpOp::Le => l <= r,
                    CmpOp::Gt => l > r,
                    CmpOp::Ge => l >= r,
                })
            }
            Formula::And(items) => {
                for f in items {
                    if !f.eval_f64(env, t)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Formula::Or(items) => {
                for f in items {
                    if f.eval_f64(env, t)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Formula::Not(inner) => Ok(!inner.eval_f64(env, t)?),
        }
    }
}

/// Uncertain PVT / litho-etch / manufacturing defect parameter interval `.param name [lo, hi]`.
#[derive(Debug, Clone, PartialEq)]
pub struct ParamDecl {
    pub name: String,
    pub lo: f64,
    pub hi: f64,
}

/// State or auxiliary variable search box `.bound target [lo, hi]`.
#[derive(Debug, Clone, PartialEq)]
pub struct BoundDecl {
    pub target: String,
    pub lo: f64,
    pub hi: f64,
}

/// Initial state box or expression `.init target [lo, hi]` or `.init target = expr`.
#[derive(Debug, Clone, PartialEq)]
pub enum InitSpec {
    Interval(f64, f64),
    Exact(Expr),
}

#[derive(Debug, Clone, PartialEq)]
pub struct InitDecl {
    pub target: String,
    pub spec: InitSpec,
}

/// Device `.model` kinds across planar CMOS, multi-gate FinFET, GAA nanosheet, SiGe HBT, GaN HEMT, and passives.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModelKind {
    Diode,
    EkvNmos,
    EkvPmos,
    FinFetN,
    FinFetP,
    GaaNmos,
    GaaPmos,
    Npn,
    Pnp,
    SiGeHbt,
    GanHemt,
    Mlcc,
}

/// Device `.model` card with parameter map.
#[derive(Debug, Clone, PartialEq)]
pub struct ModelDecl {
    pub name: String,
    pub kind: ModelKind,
    pub params: BTreeMap<String, Expr>,
}

/// Time-varying or DC source waveform.
#[derive(Debug, Clone, PartialEq)]
pub enum Waveform {
    Dc(Expr),
    /// Smooth Gaussian pulse `base + amp * exp(-((t - t0) / width)^2)`.
    GaussPulse {
        base: Expr,
        amp: Expr,
        t0: Expr,
        width: Expr,
    },
    /// Smooth logistic step `base + step / (1 + exp(-(t - t0) / tau))`.
    SmoothStep {
        base: Expr,
        step: Expr,
        t0: Expr,
        tau: Expr,
    },
}

impl Waveform {
    pub fn expr_at(&self, is_tran: bool) -> Expr {
        match self {
            Waveform::Dc(e) => e.clone(),
            Waveform::GaussPulse {
                base,
                amp,
                t0,
                width,
            } => {
                if !is_tran {
                    base.clone()
                } else {
                    let u = Expr::div(Expr::sub(Expr::Time, t0.clone()), width.clone());
                    let u2 = Expr::mul(u.clone(), u);
                    Expr::add(base.clone(), Expr::mul(amp.clone(), Expr::exp(Expr::neg(u2))))
                }
            }
            Waveform::SmoothStep {
                base,
                step,
                t0,
                tau,
            } => {
                if !is_tran {
                    base.clone()
                } else {
                    let arg = Expr::neg(Expr::div(Expr::sub(Expr::Time, t0.clone()), tau.clone()));
                    let denom = Expr::add(Expr::num(1.0), Expr::exp(arg));
                    Expr::add(base.clone(), Expr::div(step.clone(), denom))
                }
            }
        }
    }
}

/// Circuit elements, multi-PDK transistors, PCB interconnects, and multi-gate TCAD meshes.
#[derive(Debug, Clone, PartialEq)]
pub enum Element {
    Resistor {
        name: String,
        n_pos: String,
        n_neg: String,
        r: Expr,
    },
    Capacitor {
        name: String,
        n_pos: String,
        n_neg: String,
        c: Expr,
    },
    Inductor {
        name: String,
        n_pos: String,
        n_neg: String,
        l: Expr,
        r_ser: Expr,
    },
    CoupledInductors {
        name: String,
        l1_name: String,
        l2_name: String,
        k: Expr,
    },
    VoltageSource {
        name: String,
        n_pos: String,
        n_neg: String,
        wave: Waveform,
    },
    CurrentSource {
        name: String,
        n_pos: String,
        n_neg: String,
        wave: Waveform,
    },
    Diode {
        name: String,
        n_anode: String,
        n_cathode: String,
        model: String,
        area: Expr,
        vt_override: Option<Expr>,
    },
    /// Unified MOSFET / Multi-Gate FinFET (`asap7`) / Stacked GAA Nanosheet (`gt2n`) / GaN HEMT (`gan_sic`).
    Mosfet {
        name: String,
        n_drain: String,
        n_gate: String,
        n_source: String,
        n_bulk: String,
        model: String,
        /// Width `W` (for planar/HEMT) or Nanosheet width `W_ns` (for `gt2n`).
        w: Expr,
        /// Gate length `L_g` (supports litho uncertainty `{Lg0 + dLg}`).
        l: Expr,
        /// Fin count `N_fin` (`asap7`) or Nanosheet stack count `N_sheet` (`gt2n`).
        nfin: Expr,
        /// Fin or nanosheet thickness delta `dTfin` / `dTns` (nm) for quantum-confinement & DIBL.
        dtfin_nm: Expr,
        /// Workfunction / random-dopant threshold shift `dVth` (V).
        dvth: Expr,
        /// Inner-spacer thickness delta `dLisp` (nm) for GAA parasitic fringing capacitance.
        dlisp_nm: Expr,
        /// Optional self-heating thermal resistance `Rth` (K/W) for coupled electro-thermal fixed point.
        rth: Option<Expr>,
        /// Optional thermal voltage override `Vt` (V) or ambient temperature `Tamb` (K).
        vt_override: Option<Expr>,
        tamb_k: Option<Expr>,
    },
    /// Bipolar Junction Transistor (`NPN`/`PNP`) and Heterojunction `ihp_sg13g2` SiGe HBT (`SiGeHbt`).
    Bjt {
        name: String,
        n_col: String,
        n_base: String,
        n_emit: String,
        model: String,
        area: Expr,
        /// Optional Ge mole-fraction bandgap narrowing override `dEg_eV` for SiGe HBT.
        deg_ev: Option<Expr>,
        vt_override: Option<Expr>,
        temp_k: Option<Expr>,
    },
    /// Nonlinear voltage-derated MLCC or voltage-dependent GaN/SiC depletion Miller capacitance
    /// `C(v) = C_min + C0 / (1 + (v / Vsat)^2)` with optional series `ESR` and `ESL`.
    MlccCap {
        name: String,
        n_pos: String,
        n_neg: String,
        model: Option<String>,
        c0: Expr,
        c_min: Expr,
        vsat: Expr,
        esr: Expr,
        esl: Expr,
    },
    PcbMicrostrip {
        name: String,
        n_in: String,
        n_out: String,
        n_ref: String,
        len: Expr,
        w0: Expr,
        dw: Expr,
        h0: Expr,
        dh: Expr,
        t_cu: Expr,
        er: Expr,
        sigma_cu: Expr,
    },
    PcbCoupledDiffpair {
        name: String,
        in_p: String,
        in_n: String,
        out_p: String,
        out_n: String,
        ref_in: String,
        ref_out: String,
        len: Expr,
        w0: Expr,
        dw: Expr,
        s0: Expr,
        ds: Expr,
        h0: Expr,
        dh: Expr,
        t_cu: Expr,
        er_p: Expr,
        er_n: Expr,
        l_via: Expr,
        l_slot: Expr,
        r_ret: Expr,
    },
    /// 2D Cross-Section Multi-Gate FinFET TCAD (`asap7` class):
    /// Spatial `(nx x ny)` mesh across channel length `x in [0, Lg + dLg]` and fin thickness `y in [-Tfin/2, +Tfin/2]`
    /// with top + dual-sidewall high-k `HfO2` gate wrap, quantum-confinement subband shift, and Quasi-Fermi / SG continuity.
    TcadFinFet2D {
        name: String,
        nx: usize,
        ny: usize,
        lg_nm: Expr,
        tfin_nm: Expr,
        eot_nm: Expr,
        vgs: Expr,
        vds: Expr,
        phim_shift: Expr,
        temp_k: Expr,
        nbody_cm3: Expr,
    },
    /// 2nm Gate-All-Around (`gt2n`) Stacked Nanosheet Coupled Electro-Thermal + Quantum-Confinement TCAD:
    /// `N_sheet` 4-sided gate-all-around nanosheets along `nx` axial channel slices coupled to self-heating
    /// lattice temperature `T_ch = T_amb + R_th * V_ds * I_stack(T_ch)` and inner-spacer fringing electrostatics.
    TcadGaaElectroThermal {
        name: String,
        nx: usize,
        nsheets: usize,
        lg_nm: Expr,
        wns_nm: Expr,
        tns_nm: Expr,
        eot_nm: Expr,
        lisp_nm: Expr,
        vgs: Expr,
        vds: Expr,
        tamb_k: Expr,
        rth_kw: Expr,
    },
    /// Baseline 1D semiconductor p-n junction Quasi-Fermi / Scharfetter-Gummel mesh (PDK-agnostic).
    TcadDiode1D {
        name: String,
        nodes: usize,
        length_um: f64,
        junction_um: f64,
        q_dope: Expr,
        nd_plus: Expr,
        temp: Expr,
        v_bias: Expr,
    },
}

/// Parsed extended SPICE + Multi-PDK + PCB + TCAD verification deck.
#[derive(Debug, Clone, PartialEq)]
pub struct Deck {
    pub title: String,
    pub pdk: Option<PdkId>,
    pub expected: Option<ExpectedStatus>,
    pub mode: AnalysisMode,
    pub default_vbound: (f64, f64),
    pub params: Vec<ParamDecl>,
    pub consts: Vec<(String, Expr)>,
    pub bounds: Vec<BoundDecl>,
    pub inits: Vec<InitDecl>,
    pub models: BTreeMap<String, ModelDecl>,
    pub elements: Vec<Element>,
    pub unsafe_formula: Option<Formula>,
}

impl Deck {
    pub fn new(title: impl Into<String>) -> Self {
        Self {
            title: title.into(),
            pdk: None,
            expected: None,
            mode: AnalysisMode::Dc,
            default_vbound: (-5.0, 20.0),
            params: Vec::new(),
            consts: Vec::new(),
            bounds: Vec::new(),
            inits: Vec::new(),
            models: BTreeMap::new(),
            elements: Vec::new(),
            unsafe_formula: None,
        }
    }
}

/// Returns `true` if the node name represents circuit ground (`0` or `gnd`).
pub fn is_ground_node(name: &str) -> bool {
    name == "0" || name.eq_ignore_ascii_case("gnd")
}

/// Sanitize a SPICE node or element identifier for SMT-LIB2 and Lean 4.
pub fn sanitize_ident(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len());
    for ch in raw.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() {
        "id".to_string()
    } else if out.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        format!("n_{out}")
    } else {
        out
    }
}
