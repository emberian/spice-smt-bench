//! Emit kernel-replayed certificates for algebraic decks. Stamp literals use
//! the same decimal rationals as emit_lean; binary split hints retain every bit.
mod root;
pub use root::emit_root_box;

use super::{verify_paving, LeafReason, PavingNode};
use crate::ast::{CmpOp, ExpectedStatus, Expr, Formula};
use crate::emit_lean::emit_lean_def;
use crate::stamp::{StampedBody, StampedSystem};
use std::collections::BTreeMap;

fn endpoint(v: f64) -> Result<String, String> {
    let (negative, num, den) = crate::numeral::exact_f64_to_rat(v)?;
    let sign = if negative { "-" } else { "" };
    Ok(format!("⟨{sign}{num}, {den}, by decide⟩"))
}

fn dyadic(v: f64) -> Result<String, String> {
    if !v.is_finite() {
        return Err("non-finite split".into());
    }
    if v == 0.0 {
        return endpoint(0.0);
    }
    let bits = v.abs().to_bits();
    let exponent = (bits >> 52) as i32;
    let mut mantissa = bits & ((1 << 52) - 1);
    if exponent != 0 {
        mantissa |= 1 << 52;
    }
    let shift = mantissa.trailing_zeros();
    mantissa >>= shift;
    let power = exponent.max(1) - 1075 + shift as i32;
    let sign = if v < 0.0 { "-" } else { "" };
    Ok(if power <= 0 {
        format!("⟨{sign}{mantissa}, 2^{}, by decide⟩", -power)
    } else {
        format!("⟨{sign}{mantissa} * 2^{power}, 1, by decide⟩")
    })
}

type Indices<'a> = BTreeMap<&'a str, usize>;

fn index(indices: &Indices<'_>, name: &str) -> Result<usize, String> {
    indices
        .get(name)
        .copied()
        .ok_or_else(|| format!("no indexed binding for {name}"))
}

fn expr(e: &Expr, indices: &Indices<'_>) -> Result<String, String> {
    expression(e, &|name| Ok(format!("(.var {})", index(indices, name)?)))
}

fn expression(
    e: &Expr,
    variable: &impl Fn(&str) -> Result<String, String>,
) -> Result<String, String> {
    let (op, a, b) = match e {
        Expr::Num(v) => return Ok(format!("(.const {})", endpoint(*v)?)),
        Expr::Var(v) => return variable(v),
        Expr::Neg(a) => return Ok(format!("(.neg {})", expression(a, variable)?)),
        Expr::Exp(a) => return Ok(format!("(.exp {})", expression(a, variable)?)),
        Expr::Ln1pExp(a) => return Ok(format!("(.softplus {})", expression(a, variable)?)),
        Expr::Add(a, b) => ("add", a, b),
        Expr::Sub(a, b) => ("sub", a, b),
        Expr::Mul(a, b) => ("mul", a, b),
        Expr::Div(a, b) => ("div", a, b),
        _ => return Err("leaf expression is outside the Lean PExpr language".into()),
    };
    Ok(format!(
        "(.{op} {} {})",
        expression(a, variable)?,
        expression(b, variable)?
    ))
}

fn constraint(f: &Formula, indices: &Indices<'_>) -> Result<String, String> {
    let (op, lhs, rhs) = match f {
        Formula::Cmp { op, lhs, rhs } => (op, lhs, rhs),
        Formula::Not(x) => return Ok(format!("(.neg {})", constraint(x, indices)?)),
        Formula::And(xs) | Formula::Or(xs) => {
            let conj = matches!(f, Formula::And(_));
            let op = if conj { "conj" } else { "disj" };
            let mut items = xs.iter().rev();
            let Some(last) = items.next() else {
                return Ok(format!("(.lit {conj})"));
            };
            let mut term = constraint(last, indices)?;
            for x in items {
                term = format!("(.{op} {} {term})", constraint(x, indices)?);
            }
            return Ok(term);
        }
    };
    let (kind, a, b) = match op {
        CmpOp::Eq => ("eqZero", lhs, rhs),
        CmpOp::Lt => ("gtZero", rhs, lhs),
        CmpOp::Gt => ("gtZero", lhs, rhs),
        CmpOp::Le => ("geZero", rhs, lhs),
        CmpOp::Ge => ("geZero", lhs, rhs),
    };
    Ok(format!(
        "(.atom .{kind} (.sub {} {}))",
        expr(a, indices)?,
        expr(b, indices)?
    ))
}

fn tree(node: &PavingNode, indices: &Indices<'_>) -> Result<String, String> {
    match node {
        PavingNode::Leaf { reason } => Ok(format!(
            "(.leaf {})",
            match reason {
                LeafReason::UnsafeFalse => 0,
                LeafReason::ConstraintViolated(i) => i + 1,
            }
        )),
        PavingNode::Split {
            var,
            mid,
            left,
            right,
        } => Ok(format!(
            "(.split {} {} {} {})",
            index(indices, var)?,
            dyadic(*mid)?,
            tree(left, indices)?,
            tree(right, indices)?
        )),
    }
}

fn stamp_text(sys: &StampedSystem) -> String {
    let mut deck = sys.clone();
    deck.title = "Stamped circuit target".into();
    format!(
        "namespace SpiceSmtBench.Certificate\n\n{}",
        emit_lean_def(&deck, "Target", false)
    )
}

/// The emitted proof applies the real semantics of the verified checker to
/// the actual stamped proposition. A floating-point verdict supplies no proof.
pub fn emit_paving(sys: &StampedSystem, node: &PavingNode) -> Result<String, String> {
    verify_paving(sys, node)?;
    let StampedBody::Algebraic { vars, constraints } = &sys.body else {
        return Err("requires DC stamp".into());
    };
    let bindings: Vec<_> = sys
        .params
        .iter()
        .map(|p| (p.name.as_str(), Some((p.lo, p.hi))))
        .chain(vars.iter().map(|v| (v.name.as_str(), v.bounds)))
        .collect();
    // memBox constrains a prefix. Auxiliary variables follow it and retain their full domain.
    let mut order: Vec<_> = (0..bindings.len()).collect();
    order.sort_by_key(|&i| bindings[i].1.is_none());
    let indices = order
        .iter()
        .enumerate()
        .map(|(j, &i)| (bindings[i].0, j))
        .collect::<Indices>();
    if indices.len() != bindings.len() {
        return Err("duplicate variable binding".into());
    }
    let root = order
        .iter()
        .filter_map(|&i| bindings[i].1)
        .map(|(lo, hi)| Ok(format!("⟨{}, {}⟩", endpoint(lo)?, endpoint(hi)?)))
        .collect::<Result<Vec<_>, String>>()?;
    let cs = std::iter::once(&sys.unsafe_formula)
        .chain(constraints.iter().map(|c| &c.formula))
        .map(|f| constraint(f, &indices))
        .collect::<Result<Vec<_>, _>>()?;
    let args = (0..bindings.len())
        .map(|i| format!("x{i}"))
        .collect::<Vec<_>>()
        .join(" ");
    let env = order
        .iter()
        .map(|i| format!("x{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let branches = (0..cs.len()).map(|_| "rfl").collect::<Vec<_>>().join(" | ");
    let unpack = if constraints.len() > 1 {
        let names = (0..constraints.len())
            .map(|i| format!("h{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let flatten = if constraints.len() > 16 {
            "simp only [and_assoc] at phys\n    "
        } else {
            ""
        };
        format!("{flatten}obtain ⟨{names}⟩ := phys")
    } else {
        String::new()
    };
    Ok(format!("import SpiceSmtBench.PavingFormula\n\n{}\nopen IntervalCheck\n\nprivate def rootBox : List QInterval := [{}]\nprivate def cs : List PFormula := [{}]\nprivate def paving : PavingTree := {}\n
set_option maxRecDepth 20000 in
private theorem replay : verifyPaving (checkFormulaLeaf cs) paving rootBox = true := by decide +kernel

theorem certified : Target realTF := by
  intro {args} box phys bad
  let env (i : Nat) : ℝ := ([{env}] : List ℝ)[i]?.getD 0
  apply paving_unsat_sound realTF _ _ (checkFormulaLeaf_sound cs) paving rootBox env replay
  · simpa [memBox, memInterval, rootBox, QRat.eval, env, realTF, and_assoc] using box
  · intro c hc
    simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hc
    {unpack}
    rcases hc with {branches}
    all_goals simp_all [PFormula.holds, PCmp.holds, PExpr.eval, QRat.eval, env, realTF]

end SpiceSmtBench.Certificate\n",stamp_text(sys),root.join(", "),cs.join(",\n  "),tree(node,&indices)?))
}

fn rational(raw: &str) -> Result<String, String> {
    let (n, d) = raw.split_once('/').unwrap_or((raw, "1"));
    let abs = n.strip_prefix('-').unwrap_or(n);
    if abs.is_empty()
        || !abs.bytes().all(|c| c.is_ascii_digit())
        || d.is_empty()
        || !d.bytes().all(|c| c.is_ascii_digit())
        || d.bytes().all(|c| c == b'0')
    {
        return Err(format!("invalid rational {raw:?}"));
    }
    Ok(format!("{n}/{d}"))
}

/// Check a candidate 03b trajectory at the damaged-fin corner. Four rationals
/// per row bound q and qb in volts. Lean proves both implicit equations at
/// every step and checks that the specified sample violates the stamped deck.
pub fn emit_sram_boxes(sys: &StampedSystem, boxes: &str, failure: usize) -> Result<String, String> {
    if failure > 20 {
        return Err("failure sample must be in 0..=20".into());
    }
    let canonical = crate::stamp::stamp_deck(&crate::parser::parse_deck(include_str!(
        "../../benchmarks/sp/03b_asap7_sram_6t_fin_collapse_sat.sp"
    ))?)?;
    let stamp = stamp_text(sys);
    if stamp != stamp_text(&canonical) {
        return Err("the SRAM box checker requires the 03b circuit stamp".into());
    }
    let mut rows = Vec::new();
    for line in boxes.lines() {
        let data = line.split('#').next().unwrap_or("").trim();
        if data.is_empty() {
            continue;
        }
        let row = data
            .split_whitespace()
            .map(rational)
            .collect::<Result<Vec<_>, _>>()?;
        let [ql, qh, bl, bh] = row.as_slice() else {
            return Err("expected q.lo q.hi qb.lo qb.hi".into());
        };
        rows.push(format!(
            "⟨⟨{ql},{qh},by decide +kernel⟩, ⟨{bl},{bh},by decide +kernel⟩⟩"
        ));
    }
    if rows.len() != 21 {
        return Err(format!("expected 21 samples, got {}", rows.len()));
    }
    let mut out = format!(
        "import SpiceSmtBench.SramReplay\n{stamp}\nopen SramTrajectory\n
private def sampleAt (k : Nat) : Sample :=
  ([{}] : List Sample).getD k ⟨.singleton 0, .singleton 0⟩
set_option Elab.async false
set_option maxRecDepth 32000
set_option maxHeartbeats 10000000
private abbrev Row (k : Nat) := ∀ s h : Bool, checkFace (sampleAt k) (sampleAt (k+1)) s h = true
macro \"replay_row \" k:num : tactic =>
  `(tactic| first | exact checkedFaces ⟨$k,by decide⟩ | decide +kernel)
",
        rows.join(",\n    ")
    );
    for k in 0..20 {
        out.push_str(&format!(
            "private theorem row{k} : Row {k} := by replay_row {k}\n"
        ));
    }
    out.push_str(&format!("\ntheorem certified : Target realTF := by
  apply collapse_of_boxes sampleAt (by decide +kernel) (by decide +kernel) ⟨{failure},by decide⟩ (by decide +kernel)
  intro k
  change Row k
  fin_cases k\n"));
    for k in 0..20 {
        out.push_str(&format!("  · exact row{k}\n"));
    }
    out.push_str("\nend SpiceSmtBench.Certificate\n");
    Ok(out)
}

/// Emit exact rational assignments for a SAT stamp in binder order. Lean
/// checks bounds, device equations, KCL, and the unsafe predicate together.
pub fn emit_witness(
    sys: &StampedSystem,
    values: &BTreeMap<String, String>,
) -> Result<String, String> {
    if sys.expected != Some(ExpectedStatus::Sat) {
        return Err("requires .expected sat".into());
    }
    if values.is_empty() {
        let stamp = stamp_text(sys);
        for (source, theorem) in [
            (
                include_str!("../../benchmarks/sp/03b_asap7_sram_6t_fin_collapse_sat.sp"),
                "bench03b_asap7_sram_fin_collapse_proved",
            ),
            (
                include_str!("../../benchmarks/sp/04a_ihp_sige_bandgap_trojan_sat.sp"),
                "bench04a_sige_bandgap_trojan_proved",
            ),
            (
                include_str!("../../benchmarks/sp/09b_pcb_microstrip_overetch_sat.sp"),
                "bench09b_pcb_microstrip_overetch_proved",
            ),
            (
                include_str!("../../benchmarks/sp/14b_gt2n_gaa_nanosheet_thermal_runaway_sat.sp"),
                "bench14b_gaa_thermal_excursion_proved",
            ),
        ] {
            let deck = crate::parser::parse_deck(source)?;
            if stamp == stamp_text(&crate::stamp::stamp_deck(&deck)?) {
                return Ok(format!("import SpiceSmtBench.Targets\n{stamp}\n\ntheorem certified : Target realTF :=\n  Targets.{theorem}\n\nend SpiceSmtBench.Certificate\n"));
            }
        }
    }
    let StampedBody::Algebraic { vars, .. } = &sys.body else {
        return Err("requires an algebraic SAT deck".into());
    };
    let mut terms = Vec::new();
    for name in sys
        .params
        .iter()
        .map(|p| &p.name)
        .chain(vars.iter().map(|v| &v.name))
    {
        let raw = values
            .get(name)
            .ok_or_else(|| format!("missing witness for {name}"))?;
        terms.push(format!(
            "({} : ℝ)",
            rational(raw).map_err(|e| format!("{name}: {e}"))?
        ));
    }
    if terms.len() != values.len() {
        return Err("unknown witness variable".into());
    }
    Ok(format!("import SpiceSmtBench.RealPhysics\n\n{}\ntheorem certified : Target realTF := by\n  refine ⟨{}, ?_⟩\n  norm_num [realTF]\n\nend SpiceSmtBench.Certificate\n",stamp_text(sys),terms.join(", ")))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn archived_diode_paving_maps_names_and_both_leaf_reasons() {
        let deck =
            crate::parser::parse_deck(include_str!("../../benchmarks/sp/01_diode_clipper_pvt.sp"))
                .unwrap();
        let sys = crate::stamp::stamp_deck(&deck).unwrap();
        let tree = super::super::parse_paving_json(include_str!(
            "../../examples/diode_clipper_paving.json"
        ))
        .unwrap();
        let proof = emit_paving(&sys, &tree).unwrap();
        assert!(proof.contains("(.split 4 ⟨7566047373982433, 2^53, by decide⟩ (.leaf 0)"));
        assert!(
            proof.contains("(.split 5 ⟨5764607523034235, 2^60, by decide⟩ (.leaf 2) (.leaf 4))")
        );
    }

    #[test]
    fn rational_witness_uses_stamp_binders_and_requires_total_assignments() {
        let deck = crate::parser::parse_deck(".expected sat\n.mode dc\n.default_vbound [-1,2]\nV1 a 0 DC 1\nR1 a 0 1\n.unsafe v(a)>0.5\n.end").unwrap();
        let sys = crate::stamp::stamp_deck(&deck).unwrap();
        let mut values = BTreeMap::from([("i_V1".into(), "-1".into()), ("v_a".into(), "1".into())]);
        assert!(emit_witness(&sys, &values)
            .unwrap()
            .contains("⟨(1/1 : ℝ), (-1/1 : ℝ)"));
        values.insert("v_a".into(), "1/0".into());
        assert!(emit_witness(&sys, &values).is_err());
        values.remove("v_a");
        assert!(emit_witness(&sys, &values).is_err());
    }

    #[test]
    fn bandgap_root_box_reproduces_the_archived_proof_and_rejects_a_missing_root() {
        let deck = crate::parser::parse_deck(include_str!(
            "../../benchmarks/sp/04a_ihp_sige_bandgap_trojan_sat.sp"
        ))
        .unwrap();
        let sys = crate::stamp::stamp_deck(&deck).unwrap();
        let mut hints: Vec<_> = [
            "vdd=3",
            "temp_k=300",
            "deg_ge=0.085",
            "v_ref=-0.001:0.01",
            "v_vc1=2.995:3.005",
            "v_e0=-0.00009:0.00009",
            "v_ve2=-0.0001:0.0001",
            "skirk_Q1=0.99:1.01",
            "skirk_Q2=0.99:1.01",
            "i_Vsup=-0.001:0.001",
        ]
        .into_iter()
        .map(String::from)
        .collect();
        let proof = emit_root_box(&sys, &hints).unwrap();
        let archived = include_str!("../../lean/SpiceSmtBench/BandgapCertificate.lean");
        // The exported file includes its own copy of the stamped target.
        // Compare the coordinate definitions, certificate data and proof body.
        let body = |s: &str| {
            s.split_once("private def p0")
                .unwrap()
                .1
                .split_once("end SpiceSmtBench.")
                .unwrap()
                .0
                .replace("Targets.Bench_04a_ihp_sige_bandgap_trojan_sat", "Target")
        };
        assert_eq!(body(&proof), body(archived));
        hints[3] = "v_ref=0.5:0.51".into();
        assert!(emit_root_box(&sys, &hints).is_err());
    }

    #[test]
    fn lean_split_points_preserve_binary64_exactly() {
        assert_eq!(
            dyadic(-0.1).unwrap(),
            "⟨-3602879701896397, 2^55, by decide⟩"
        );
        assert_eq!(dyadic(f64::from_bits(1)).unwrap(), "⟨1, 2^1074, by decide⟩");
        assert_eq!(dyadic(8.).unwrap(), "⟨1 * 2^3, 1, by decide⟩");
        assert_eq!(dyadic(-0.).unwrap(), endpoint(0.).unwrap());
        assert!(dyadic(f64::NAN).is_err());
    }
}
