//! Rigorous outward-rounded interval evaluator and branch-and-bound sub-box paving
//! certificate verifier (`spice2smt verify-paving <deck.sp> <paving.json>`).

use std::collections::BTreeMap;

use crate::ast::{CmpOp, Expr, Formula};
use crate::stamp::{StampedBody, StampedSystem};

/// Closed real interval `[lo, hi]` with outward-rounded operations.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Iv {
    pub lo: f64,
    pub hi: f64,
}

fn next_down(x: f64) -> f64 {
    if x.is_nan() || x == f64::NEG_INFINITY {
        return f64::NEG_INFINITY;
    }
    if x == 0.0 {
        return -f64::from_bits(1);
    }
    if x > 0.0 {
        f64::from_bits(x.to_bits() - 1)
    } else {
        f64::from_bits(x.to_bits() + 1)
    }
}

fn next_up(x: f64) -> f64 {
    if x.is_nan() || x == f64::INFINITY {
        return f64::INFINITY;
    }
    if x == 0.0 {
        return f64::from_bits(1);
    }
    if x > 0.0 {
        f64::from_bits(x.to_bits() + 1)
    } else {
        f64::from_bits(x.to_bits() - 1)
    }
}

#[allow(clippy::should_implement_trait)]
impl Iv {
    pub fn exact(v: f64) -> Self {
        Self { lo: v, hi: v }
    }

    pub fn new(lo: f64, hi: f64) -> Result<Self, String> {
        if !lo.is_finite() || !hi.is_finite() || lo > hi {
            return Err(format!("invalid interval [{lo}, {hi}]"));
        }
        Ok(Self { lo, hi })
    }

    pub fn contains_zero(self) -> bool {
        self.lo <= 0.0 && 0.0 <= self.hi
    }

    pub fn neg(self) -> Self {
        Self {
            lo: -self.hi,
            hi: -self.lo,
        }
    }

    pub fn add(self, rhs: Self) -> Self {
        Self {
            lo: next_down(self.lo + rhs.lo),
            hi: next_up(self.hi + rhs.hi),
        }
    }

    pub fn sub(self, rhs: Self) -> Self {
        Self {
            lo: next_down(self.lo - rhs.hi),
            hi: next_up(self.hi - rhs.lo),
        }
    }

    pub fn mul(self, rhs: Self) -> Self {
        let p1 = self.lo * rhs.lo;
        let p2 = self.lo * rhs.hi;
        let p3 = self.hi * rhs.lo;
        let p4 = self.hi * rhs.hi;
        let lo = p1.min(p2).min(p3).min(p4);
        let hi = p1.max(p2).max(p3).max(p4);
        Self {
            lo: next_down(lo),
            hi: next_up(hi),
        }
    }

    pub fn div(self, rhs: Self) -> Option<Self> {
        if rhs.contains_zero() {
            return None;
        }
        let inv = Self {
            lo: next_down(1.0 / rhs.hi),
            hi: next_up(1.0 / rhs.lo),
        };
        Some(self.mul(inv))
    }

    /// Outward-rounded exponential enclosure `[exp_down(lo), exp_up(hi)]`.
    pub fn exp(self) -> Self {
        let lo = if self.lo < -700.0 {
            0.0
        } else {
            next_down(next_down(self.lo.exp()))
        };
        let hi = if self.hi > 700.0 {
            f64::INFINITY
        } else {
            next_up(next_up(self.hi.exp()))
        };
        Self { lo, hi }
    }

    pub fn ln1p_exp(self) -> Self {
        let eval_pt = |z: f64| -> f64 {
            if z > 30.0 {
                z + (-z).exp().ln_1p()
            } else {
                z.exp().ln_1p()
            }
        };
        Self {
            lo: next_down(next_down(eval_pt(self.lo))).max(0.0),
            hi: next_up(next_up(eval_pt(self.hi))),
        }
    }
}

/// Evaluate an `Expr` over an interval box `env`. Returns `None` if a denominator straddles `0`.
pub fn eval_expr_iv(e: &Expr, env: &BTreeMap<String, Iv>) -> Option<Iv> {
    match e {
        Expr::Num(v) => Some(Iv::exact(*v)),
        Expr::Var(name) => env.get(name).copied(),
        Expr::NodeVolt(n) => env
            .get(&format!("v_{}", crate::ast::sanitize_ident(n)))
            .copied(),
        Expr::Time => Some(Iv::exact(0.0)),
        Expr::Neg(a) => Some(eval_expr_iv(a, env)?.neg()),
        Expr::Add(a, b) => Some(eval_expr_iv(a, env)?.add(eval_expr_iv(b, env)?)),
        Expr::Sub(a, b) => Some(eval_expr_iv(a, env)?.sub(eval_expr_iv(b, env)?)),
        Expr::Mul(a, b) => Some(eval_expr_iv(a, env)?.mul(eval_expr_iv(b, env)?)),
        Expr::Div(a, b) => eval_expr_iv(a, env)?.div(eval_expr_iv(b, env)?),
        Expr::Exp(a) => Some(eval_expr_iv(a, env)?.exp()),
        Expr::Ln1pExp(a) => Some(eval_expr_iv(a, env)?.ln1p_exp()),
    }
}

/// Returns `true` if `Formula` is **provably `False`** for every real point in `env`.
pub fn formula_refuted_on_box(f: &Formula, env: &BTreeMap<String, Iv>) -> bool {
    match f {
        Formula::Cmp { op, lhs, rhs } => {
            let Some(l) = eval_expr_iv(lhs, env) else {
                return false;
            };
            let Some(r) = eval_expr_iv(rhs, env) else {
                return false;
            };
            let diff = l.sub(r);
            match op {
                CmpOp::Eq => !diff.contains_zero(),
                CmpOp::Lt => diff.lo >= 0.0,
                CmpOp::Le => diff.lo > 0.0,
                CmpOp::Gt => diff.hi <= 0.0,
                CmpOp::Ge => diff.hi < 0.0,
            }
        }
        Formula::And(items) => items.iter().any(|it| formula_refuted_on_box(it, env)),
        Formula::Or(items) => items.iter().all(|it| formula_refuted_on_box(it, env)),
        Formula::Not(inner) => formula_entailed_on_box(inner, env),
    }
}

fn formula_entailed_on_box(f: &Formula, env: &BTreeMap<String, Iv>) -> bool {
    match f {
        Formula::Cmp { op, lhs, rhs } => {
            let Some(l) = eval_expr_iv(lhs, env) else {
                return false;
            };
            let Some(r) = eval_expr_iv(rhs, env) else {
                return false;
            };
            let diff = l.sub(r);
            match op {
                CmpOp::Eq => diff.lo == 0.0 && diff.hi == 0.0,
                CmpOp::Lt => diff.hi < 0.0,
                CmpOp::Le => diff.hi <= 0.0,
                CmpOp::Gt => diff.lo > 0.0,
                CmpOp::Ge => diff.lo >= 0.0,
            }
        }
        Formula::And(items) => items.iter().all(|it| formula_entailed_on_box(it, env)),
        Formula::Or(items) => items.iter().any(|it| formula_entailed_on_box(it, env)),
        Formula::Not(inner) => formula_refuted_on_box(inner, env),
    }
}

/// How a leaf sub-box in a branch-and-bound paving is refuted.
#[derive(Debug, Clone, PartialEq)]
pub enum LeafReason {
    /// `.unsafe` evaluates strictly to `False` across the entire sub-box.
    UnsafeFalse,
    /// The `index`-th stamped physics constraint is violated (`0 ∉ residual`) across the entire sub-box.
    ConstraintViolated(usize),
}

/// Recursive binary space-partitioning certificate covering the root domain box.
#[derive(Debug, Clone, PartialEq)]
pub enum PavingNode {
    Split {
        var: String,
        mid: f64,
        left: Box<PavingNode>,
        right: Box<PavingNode>,
    },
    Leaf {
        reason: LeafReason,
    },
}

/// Summary statistics returned by `verify_paving`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PavingReport {
    pub total_leaves: usize,
    pub unsafe_refuted_leaves: usize,
    pub physics_refuted_leaves: usize,
    pub max_depth: usize,
}

/// Verify that `paving` partitions the entire parameter + state box of `sys` and that every
/// leaf soundly refutes either `.unsafe` or at least one stamped physics constraint.
pub fn verify_paving(sys: &StampedSystem, paving: &PavingNode) -> Result<PavingReport, String> {
    let StampedBody::Algebraic { vars, constraints } = &sys.body else {
        return Err(
            "verify-paving currently targets algebraic / DC / TCAD / PCB systems".to_string(),
        );
    };

    let mut root_box: BTreeMap<String, Iv> = BTreeMap::new();
    for p in &sys.params {
        root_box.insert(p.name.clone(), Iv::new(p.lo, p.hi)?);
    }
    for v in vars {
        root_box.insert(v.name.clone(), Iv::new(v.lo, v.hi)?);
    }

    let mut report = PavingReport {
        total_leaves: 0,
        unsafe_refuted_leaves: 0,
        physics_refuted_leaves: 0,
        max_depth: 0,
    };

    check_node(
        paving,
        &mut root_box,
        constraints,
        &sys.unsafe_formula,
        0,
        &mut report,
    )?;

    Ok(report)
}

fn check_node(
    node: &PavingNode,
    cur_box: &mut BTreeMap<String, Iv>,
    constraints: &[crate::stamp::TaggedConstraint],
    unsafe_formula: &Formula,
    depth: usize,
    report: &mut PavingReport,
) -> Result<(), String> {
    if depth > report.max_depth {
        report.max_depth = depth;
    }
    match node {
        PavingNode::Split {
            var,
            mid,
            left,
            right,
        } => {
            let orig = cur_box
                .get(var)
                .copied()
                .ok_or_else(|| format!("split references unknown variable `{var}`"))?;
            if *mid < orig.lo || *mid > orig.hi {
                return Err(format!(
                    "split point {mid} on `{var}` lies outside current sub-box [{}, {}]",
                    orig.lo, orig.hi
                ));
            }
            cur_box.insert(var.clone(), Iv { lo: orig.lo, hi: *mid });
            check_node(left, cur_box, constraints, unsafe_formula, depth + 1, report)?;

            cur_box.insert(var.clone(), Iv { lo: *mid, hi: orig.hi });
            check_node(
                right,
                cur_box,
                constraints,
                unsafe_formula,
                depth + 1,
                report,
            )?;

            cur_box.insert(var.clone(), orig);
            Ok(())
        }
        PavingNode::Leaf { reason } => {
            report.total_leaves += 1;
            match reason {
                LeafReason::UnsafeFalse => {
                    if formula_refuted_on_box(unsafe_formula, cur_box) {
                        report.unsafe_refuted_leaves += 1;
                        Ok(())
                    } else {
                        Err("leaf claims `unsafe_false`, but `.unsafe` is not refuted on sub-box".to_string())
                    }
                }
                LeafReason::ConstraintViolated(idx) => {
                    let c = constraints.get(*idx).ok_or_else(|| {
                        format!(
                            "leaf references out-of-range constraint index {idx} (total {})",
                            constraints.len()
                        )
                    })?;
                    if formula_refuted_on_box(&c.formula, cur_box) {
                        report.physics_refuted_leaves += 1;
                        Ok(())
                    } else {
                        Err(format!(
                            "leaf claims constraint #{idx} (`{}`) is violated, but 0 remains inside interval enclosure on sub-box {:?}",
                            c.comment, cur_box
                        ))
                    }
                }
            }
        }
    }
}

// --- Minimal zero-dependency JSON parser for `PavingNode` ---

#[derive(Debug, Clone, PartialEq)]
enum JsonVal {
    Object(BTreeMap<String, JsonVal>),
    Str(String),
    Num(f64),
}

struct JsonParser<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> JsonParser<'a> {
    fn new(src: &'a str) -> Self {
        Self {
            bytes: src.as_bytes(),
            pos: 0,
        }
    }

    fn skip_ws(&mut self) {
        while self.pos < self.bytes.len() && self.bytes[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
    }

    fn parse_val(&mut self) -> Result<JsonVal, String> {
        self.skip_ws();
        let Some(&b) = self.bytes.get(self.pos) else {
            return Err("unexpected EOF in JSON".to_string());
        };
        match b {
            b'{' => self.parse_obj(),
            b'"' => Ok(JsonVal::Str(self.parse_str()?)),
            b'-' | b'0'..=b'9' => Ok(JsonVal::Num(self.parse_num()?)),
            other => Err(format!(
                "unexpected JSON byte `{}` at offset {}",
                other as char, self.pos
            )),
        }
    }

    fn parse_str(&mut self) -> Result<String, String> {
        self.skip_ws();
        if self.bytes.get(self.pos) != Some(&b'"') {
            return Err("expected `\"`".to_string());
        }
        self.pos += 1;
        let mut s = String::new();
        while self.pos < self.bytes.len() {
            let c = self.bytes[self.pos];
            self.pos += 1;
            if c == b'"' {
                return Ok(s);
            }
            if c == b'\\' {
                let esc = *self
                    .bytes
                    .get(self.pos)
                    .ok_or_else(|| "unterminated escape in JSON string".to_string())?;
                self.pos += 1;
                s.push(esc as char);
            } else {
                s.push(c as char);
            }
        }
        Err("unterminated JSON string".to_string())
    }

    fn parse_num(&mut self) -> Result<f64, String> {
        let start = self.pos;
        while self.pos < self.bytes.len() {
            let c = self.bytes[self.pos];
            if c.is_ascii_digit() || matches!(c, b'-' | b'+' | b'.' | b'e' | b'E') {
                self.pos += 1;
            } else {
                break;
            }
        }
        let lit = std::str::from_utf8(&self.bytes[start..self.pos])
            .map_err(|_| "invalid UTF-8 in number".to_string())?;
        lit.parse::<f64>()
            .map_err(|_| format!("invalid JSON number `{lit}`"))
    }

    fn parse_obj(&mut self) -> Result<JsonVal, String> {
        self.pos += 1; // '{'
        let mut map = BTreeMap::new();
        loop {
            self.skip_ws();
            if self.bytes.get(self.pos) == Some(&b'}') {
                self.pos += 1;
                return Ok(JsonVal::Object(map));
            }
            let key = self.parse_str()?;
            self.skip_ws();
            if self.bytes.get(self.pos) != Some(&b':') {
                return Err("expected `:` after JSON object key".to_string());
            }
            self.pos += 1;
            let val = self.parse_val()?;
            map.insert(key, val);
            self.skip_ws();
            match self.bytes.get(self.pos) {
                Some(&b',') => {
                    self.pos += 1;
                }
                Some(&b'}') => {
                    self.pos += 1;
                    return Ok(JsonVal::Object(map));
                }
                _ => return Err("expected `,` or `}` in JSON object".to_string()),
            }
        }
    }
}

fn json_to_paving(v: &JsonVal) -> Result<PavingNode, String> {
    let JsonVal::Object(obj) = v else {
        return Err("paving node must be a JSON object".to_string());
    };
    let Some(JsonVal::Str(kind)) = obj.get("type") else {
        return Err("paving node missing string field `\"type\"`".to_string());
    };
    match kind.as_str() {
        "split" => {
            let Some(JsonVal::Str(var)) = obj.get("var") else {
                return Err("`split` node missing `\"var\"`".to_string());
            };
            let Some(JsonVal::Num(mid)) = obj.get("mid") else {
                return Err("`split` node missing numeric `\"mid\"`".to_string());
            };
            let left_j = obj
                .get("left")
                .ok_or_else(|| "`split` node missing `\"left\"`".to_string())?;
            let right_j = obj
                .get("right")
                .ok_or_else(|| "`split` node missing `\"right\"`".to_string())?;
            Ok(PavingNode::Split {
                var: var.clone(),
                mid: *mid,
                left: Box::new(json_to_paving(left_j)?),
                right: Box::new(json_to_paving(right_j)?),
            })
        }
        "leaf" => {
            let Some(JsonVal::Str(reason_s)) = obj.get("reason") else {
                return Err("`leaf` node missing `\"reason\"`".to_string());
            };
            let reason = match reason_s.as_str() {
                "unsafe_false" => LeafReason::UnsafeFalse,
                "constraint_violated" => {
                    let Some(JsonVal::Num(idx)) = obj.get("constraint_index") else {
                        return Err(
                            "`constraint_violated` leaf requires `\"constraint_index\"`"
                                .to_string(),
                        );
                    };
                    LeafReason::ConstraintViolated(*idx as usize)
                }
                other => return Err(format!("unknown leaf reason `{other}`")),
            };
            Ok(PavingNode::Leaf { reason })
        }
        other => Err(format!("unknown paving node type `{other}`")),
    }
}

/// Parse a `PavingNode` tree from a JSON string.
pub fn parse_paving_json(src: &str) -> Result<PavingNode, String> {
    let mut p = JsonParser::new(src);
    let val = p.parse_val()?;
    p.skip_ws();
    if p.pos != p.bytes.len() {
        return Err("trailing characters after JSON root object".to_string());
    }
    json_to_paving(&val)
}
