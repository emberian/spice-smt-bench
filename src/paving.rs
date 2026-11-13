//! Rigorous outward-rounded interval evaluator and branch-and-bound sub-box paving
//! certificate verifier (`spice2smt verify-paving <deck.sp> <paving.json>`).

use std::collections::BTreeMap;

use crate::ast::{CmpOp, Expr, Formula};
use crate::stamp::{StampedBody, StampedSystem, TaggedConstraint};

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
        if [p1, p2, p3, p4].iter().any(|x| x.is_nan()) {
            return Self { lo: f64::NEG_INFINITY, hi: f64::INFINITY };
        }
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

    /// Enclose exp without relying on platform transcendental implementations.
    /// Reduce by exact powers of two to |r| <= 1/2, sum the degree-12
    /// Taylor polynomial, then square. The tail is at most
    /// 2 * |r|^13 / 13!, since exp(|r|) < 2 on this interval.
    /// Every arithmetic operation is rounded outward by one adjacent float.
    pub fn exp(self) -> Self {
        fn point(x: f64) -> Iv {
            if x == f64::NEG_INFINITY { return Iv::exact(0.0); }
            if x == f64::INFINITY { return Iv { lo: f64::MAX, hi: f64::INFINITY }; }
            if !x.is_finite() { return Iv { lo: 0.0, hi: f64::INFINITY }; }
            if x < -1024.0 { return Iv { lo: 0.0, hi: f64::MIN_POSITIVE }; }
            if x > 1024.0 { return Iv { lo: f64::MAX, hi: f64::INFINITY }; }
            let mut r = Iv::exact(x);
            let mut squares = 0;
            while r.lo.abs().max(r.hi.abs()) > 0.5 {
                r = r.mul(Iv::exact(0.5));
                squares += 1;
            }
            let mut term = Iv::exact(1.0);
            let mut sum = term;
            for n in 1..=12 {
                term = term.mul(r).div(Iv::exact(n as f64)).expect("positive divisor");
                sum = sum.add(term);
            }
            let radius = r.lo.abs().max(r.hi.abs());
            let mut tail = Iv::exact(2.0);
            for n in 1..=13 {
                tail = tail.mul(Iv::exact(radius)).div(Iv::exact(n as f64)).expect("positive divisor");
            }
            sum = sum.add(Iv { lo: -tail.hi, hi: tail.hi });
            sum.lo = sum.lo.max(0.0);
            for _ in 0..squares {
                sum = sum.mul(sum);
                sum.lo = sum.lo.max(0.0);
            }
            sum
        }
        Self { lo: point(self.lo).lo, hi: point(self.hi).hi }
    }

    /// Invert the certified monotone exponential enclosure by bisection.
    /// log(1+exp(z)) lies in [max(0,z), max(0,z)+1], since log(2)<1.
    pub fn ln1p_exp(self) -> Self {
        fn point(z: f64) -> Iv {
            if !z.is_finite() {
                return if z == f64::NEG_INFINITY { Iv::exact(0.0) }
                    else { Iv { lo: z.max(0.0), hi: f64::INFINITY } };
            }
            // softplus(z) = max(0,z) + log(1 + exp(-|z|)).
            let target = Iv::exact(1.0).add(Iv::exact(-z.abs()).exp());
            let mut lo = 0.0;
            let mut hi = 1.0;
            for _ in 0..60 {
                let mid = lo + (hi - lo) * 0.5;
                let e = Iv::exact(mid).exp();
                if e.hi < target.lo { lo = mid; }
                else if e.lo > target.hi { hi = mid; }
                else { break; }
            }
            Iv::exact(z.max(0.0)).add(Iv { lo, hi })
        }
        Self { lo: point(self.lo).lo.max(0.0), hi: point(self.hi).hi }
    }

}

/// Evaluate an `Expr` over an interval box `env`. Returns `None` if a denominator straddles `0`.
fn decimal_interval(value: f64) -> Option<Iv> {
    let (negative, num, den) = crate::numeral::exact_f64_to_rat(value).ok()?;
    fn integer(s: &str) -> Iv {
        s.bytes().fold(Iv::exact(0.0), |a, d| a.mul(Iv::exact(10.0)).add(Iv::exact((d-b'0') as f64)))
    }
    let result = integer(&num).div(integer(&den))?;
    Some(if negative { result.neg() } else { result })
}

fn domain_interval(lo: f64, hi: f64) -> Result<Iv, String> {
    let lower = decimal_interval(lo).ok_or("invalid lower domain endpoint")?;
    let upper = decimal_interval(hi).ok_or("invalid upper domain endpoint")?;
    Iv::new(lower.lo, upper.hi)
}

pub fn eval_expr_iv(e: &Expr, env: &BTreeMap<String, Iv>) -> Option<Iv> {
    match e {
        Expr::Num(v) => decimal_interval(*v),
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
        Expr::Sqrt(a) => { let x = eval_expr_iv(a, env)?; if x.lo < 0.0 { None } else { Some(Iv { lo: next_down(x.lo.sqrt()).max(0.0), hi: next_up(x.hi.sqrt()) }) } },
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
    if sys.expected != Some(crate::ast::ExpectedStatus::Unsat) {
        return Err("verify-paving requires .expected unsat".to_string());
    }
    let StampedBody::Algebraic { vars, constraints } = &sys.body else {
        return Err(
            "verify-paving currently targets algebraic / DC / TCAD / PCB systems".to_string(),
        );
    };

    let mut root_box: BTreeMap<String, Iv> = BTreeMap::new();
    for p in &sys.params {
        root_box.insert(p.name.clone(), domain_interval(p.lo, p.hi)?);
    }
    for v in vars {
        if let Some((lo, hi)) = v.bounds { root_box.insert(v.name.clone(), domain_interval(lo, hi)?); }
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
            if !mid.is_finite() || *mid <= orig.lo || *mid >= orig.hi {
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
        let value = lit.parse::<f64>().map_err(|_| format!("invalid JSON number `{lit}`"))?;
        if !value.is_finite() { return Err(format!("non-finite JSON number `{lit}`")); }
        Ok(value)
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
            if map.insert(key.clone(), val).is_some() { return Err(format!("duplicate JSON key `{key}`")); }
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
                    if *idx < 0.0 || idx.fract() != 0.0 || *idx >= usize::MAX as f64 {
                        return Err("constraint_index must be a nonnegative representable integer".to_string());
                    }
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

/// Construct a certificate from an ordered list of proposed bisections.
/// Every leaf must be refuted by the same evaluator used for replay; exhausted
/// hints return an error rather than classifying an unresolved box as safe.
pub fn generate_paving(sys: &StampedSystem, splits: &[(String, f64)]) -> Result<PavingNode, String> {
    let StampedBody::Algebraic { vars, constraints } = &sys.body else {
        return Err("paving generation requires an algebraic system".to_string());
    };
    let mut domain = BTreeMap::new();
    for p in &sys.params { domain.insert(p.name.clone(), domain_interval(p.lo, p.hi)?); }
    for v in vars { if let Some((lo, hi)) = v.bounds { domain.insert(v.name.clone(), domain_interval(lo, hi)?); } }
    fn search(domain: &mut BTreeMap<String, Iv>, constraints: &[TaggedConstraint], unsafe_formula: &Formula,
        splits: &[(String, f64)]) -> Result<PavingNode, String> {
        if formula_refuted_on_box(unsafe_formula, domain) {
            return Ok(PavingNode::Leaf { reason: LeafReason::UnsafeFalse });
        }
        for (index, c) in constraints.iter().enumerate() {
            if formula_refuted_on_box(&c.formula, domain) {
                return Ok(PavingNode::Leaf { reason: LeafReason::ConstraintViolated(index) });
            }
        }
        let ((var, mid), remaining) = splits.split_first().ok_or("unresolved box: supply additional split hints")?;
        let original = *domain.get(var).ok_or_else(|| format!("unknown split variable `{var}`"))?;
        if !mid.is_finite() || *mid <= original.lo || *mid >= original.hi {
            return Err(format!("split for `{var}` must be strictly inside its interval"));
        }
        domain.insert(var.clone(), Iv { lo: original.lo, hi: *mid });
        let left = search(domain, constraints, unsafe_formula, remaining)?;
        domain.insert(var.clone(), Iv { lo: *mid, hi: original.hi });
        let right = search(domain, constraints, unsafe_formula, remaining)?;
        domain.insert(var.clone(), original);
        Ok(PavingNode::Split { var: var.clone(), mid: *mid, left: Box::new(left), right: Box::new(right) })
    }
    let result = search(&mut domain, constraints, &sys.unsafe_formula, splits)?;
    verify_paving(sys, &result)?;
    Ok(result)
}

impl PavingNode {
    pub fn to_json(&self) -> String {
        match self {
            Self::Leaf { reason: LeafReason::UnsafeFalse } => "{\"type\":\"leaf\",\"reason\":\"unsafe_false\"}".to_string(),
            Self::Leaf { reason: LeafReason::ConstraintViolated(index) } =>
                format!("{{\"type\":\"leaf\",\"reason\":\"constraint_violated\",\"constraint_index\":{index}}}"),
            Self::Split { var, mid, left, right } => {
                let escaped = var.replace('\\', "\\\\").replace('"', "\\\"");
                format!("{{\"type\":\"split\",\"var\":\"{escaped}\",\"mid\":{mid},\"left\":{},\"right\":{}}}", left.to_json(), right.to_json())
            }
        }
    }
}

/// Enclose the logarithm by inverting certified exponential bounds. The search
/// retains both endpoints when a rounded exponential overlaps the target.
fn log_enclosure(x: Iv) -> Option<Iv> {
    if x.lo <= 0.0 || !x.hi.is_finite() { return None; }
    fn endpoint(x: f64, lower: bool) -> f64 {
        let (mut lo, mut hi) = (-1024.0, 1024.0);
        for _ in 0..64 {
            let mid = lo + (hi - lo) * 0.5;
            let exp = Iv::exact(mid).exp();
            if exp.hi < x { lo = mid; }
            else if exp.lo > x { hi = mid; }
            else { break; }
        }
        if lower { lo } else { hi }
    }
    Some(Iv { lo: endpoint(x.lo, true), hi: endpoint(x.hi, false) })
}

/// Forward equality contraction. Every retained box contains all solutions of
/// the original equations; positivity guards justify choosing the positive root.
fn contract_definitions(env: &mut BTreeMap<String, Iv>, constraints: &[TaggedConstraint]) {
    for _ in 0..12 {
        let mut changed = false;
        for c in constraints {
            let Formula::Cmp { op: CmpOp::Eq, lhs, rhs } = &c.formula else { continue; };
            let candidate = match lhs {
                Expr::Var(name) => eval_expr_iv(rhs, env).map(|iv| (name, iv)),
                Expr::Exp(arg) => if let Expr::Var(name) = arg.as_ref() {
                    eval_expr_iv(rhs, env).and_then(log_enclosure).map(|iv| (name, iv))
                } else { None },
                Expr::Mul(a, b) if a == b => if let Expr::Var(name) = a.as_ref() {
                    let positive = env.get(name).is_some_and(|iv| iv.lo >= 0.0) || constraints.iter().any(|c| {
                        matches!(&c.formula, Formula::Cmp { op: CmpOp::Ge | CmpOp::Gt, lhs: Expr::Var(n), rhs: Expr::Num(z) } if n == name && *z == 0.0)
                    });
                    if positive { eval_expr_iv(&Expr::sqrt(rhs.clone()), env).map(|iv| (name, iv)) } else { None }
                } else { None },
                _ => None,
            };
            if let Some((name, mut iv)) = candidate {
                if let Some(old) = env.get(name) {
                    iv.lo = iv.lo.max(old.lo); iv.hi = iv.hi.min(old.hi);
                    // Leave contradictory boxes for the constraint evaluator.
                    if iv.lo > iv.hi { continue; }
                    if iv == *old { continue; }
                }
                if iv.lo.is_nan() || iv.hi.is_nan() { continue; }
                env.insert(name.clone(), iv);
                changed = true;
            }
        }
        if !changed { break; }
    }
}

/// Exhaustive branch-and-bound over the complete stamped domain. A resource
/// limit or an unresolved box is an error, never an UNSAT result. `split_vars`
/// controls the search strategy only; all other variables retain their full box.
pub fn prove_unsat(sys: &StampedSystem, split_vars: &[String], max_boxes: usize) -> Result<usize, String> {
    if sys.expected != Some(crate::ast::ExpectedStatus::Unsat) { return Err("requires .expected unsat".into()); }
    let StampedBody::Algebraic { vars, constraints } = &sys.body else { return Err("requires algebraic system".into()); };
    let mut root = BTreeMap::new();
    for p in &sys.params { root.insert(p.name.clone(), domain_interval(p.lo, p.hi)?); }
    for v in vars { if let Some((lo, hi)) = v.bounds { root.insert(v.name.clone(), domain_interval(lo, hi)?); } }
    for name in split_vars { if !root.contains_key(name) { return Err(format!("unknown split variable {name}")); } }
    let mut pending = vec![(root, 0usize)];
    let mut visited = 0;
    while let Some((mut env, depth)) = pending.pop() {
        visited += 1;
        if visited > max_boxes { return Err(format!("unresolved after {max_boxes} boxes")); }
        for _ in 0..3 {
            contract_formula(&sys.unsafe_formula, &mut env);
            contract_definitions(&mut env, constraints);
            for c in constraints { contract_formula(&c.formula, &mut env); }
        }
        if formula_refuted_on_box(&sys.unsafe_formula, &env) || constraints.iter().any(|c| formula_refuted_on_box(&c.formula, &env)) { continue; }
        if split_vars.is_empty() { return Err("unresolved box without split variables".into()); }
        let name = &split_vars[depth % split_vars.len()];
        let iv = env[name];
        let mid = iv.lo + (iv.hi - iv.lo) * 0.5;
        if !mid.is_finite() || mid <= iv.lo || mid >= iv.hi { return Err(format!("unresolved degenerate interval for {name}")); }
        let mut right = env.clone();
        env.insert(name.clone(), Iv { lo: iv.lo, hi: mid });
        right.insert(name.clone(), Iv { lo: mid, hi: iv.hi });
        pending.push((right, depth+1)); pending.push((env, depth+1));
    }
    Ok(visited)
}

/// Backward arithmetic propagation for an equality or inequality. Intersections
/// only discard values excluded by a necessary interval condition.
fn contract_expr(e: &Expr, target: Iv, env: &mut BTreeMap<String,Iv>) {
    match e {
        Expr::Var(name) => {
            let old = env.get(name).copied().unwrap_or(Iv {lo:f64::NEG_INFINITY,hi:f64::INFINITY});
            let iv = Iv {lo:old.lo.max(target.lo),hi:old.hi.min(target.hi)};
            if iv.lo <= iv.hi && !iv.lo.is_nan() && !iv.hi.is_nan() { env.insert(name.clone(),iv); }
        }
        Expr::Neg(a) => contract_expr(a,target.neg(),env),
        Expr::Add(a,b) | Expr::Sub(a,b) | Expr::Mul(a,b) | Expr::Div(a,b) => {
            let left = eval_expr_iv(a,env); let right = eval_expr_iv(b,env);
            match e {
                Expr::Add(..) => {
                    if let Some(r) = right { contract_expr(a,target.sub(r),env); }
                    if let Some(l) = left { contract_expr(b,target.sub(l),env); }
                }
                Expr::Sub(..) => {
                    if let Some(r) = right { contract_expr(a,target.add(r),env); }
                    if let Some(l) = left { contract_expr(b,l.sub(target),env); }
                }
                Expr::Mul(..) => {
                    if let Some(iv) = right.and_then(|r| target.div(r)) { contract_expr(a,iv,env); }
                    if let Some(iv) = left.and_then(|l| target.div(l)) { contract_expr(b,iv,env); }
                }
                Expr::Div(..) => {
                    if let Some(r) = right { if !r.contains_zero() { contract_expr(a,target.mul(r),env); } }
                    if let Some(iv) = left.and_then(|l| l.div(target)) { contract_expr(b,iv,env); }
                }
                _ => {}
            }
        }
        Expr::Exp(a) => if let Some(iv) = log_enclosure(target) { contract_expr(a,iv,env); },
        _ => {}
    }
}

fn contract_formula(f: &Formula, env: &mut BTreeMap<String,Iv>) {
    match f {
        Formula::Cmp {op,lhs,rhs} => {
            let l = eval_expr_iv(lhs,env); let r = eval_expr_iv(rhs,env);
            match op {
                CmpOp::Eq => {
                    if let Some(r) = r { contract_expr(lhs,r,env); }
                    if let Some(l) = l { contract_expr(rhs,l,env); }
                }
                CmpOp::Le | CmpOp::Lt => {
                    if let Some(r) = r { contract_expr(lhs,Iv {lo:f64::NEG_INFINITY,hi:r.hi},env); }
                    if let Some(l) = l { contract_expr(rhs,Iv {lo:l.lo,hi:f64::INFINITY},env); }
                }
                CmpOp::Ge | CmpOp::Gt => {
                    if let Some(r) = r { contract_expr(lhs,Iv {lo:r.lo,hi:f64::INFINITY},env); }
                    if let Some(l) = l { contract_expr(rhs,Iv {lo:f64::NEG_INFINITY,hi:l.hi},env); }
                }
            }
        }
        Formula::And(fs) => for f in fs { contract_formula(f,env); },
        _ => {}
    }
}
