//! Finite-dimensional Poincaré–Miranda certificates for square DC stamps.
//! Floating-point evaluation only selects a row and its orientation. Lean
//! re-evaluates every sign and proves the original existential proposition.
use super::{expression, stamp_text};
use crate::ast::{CmpOp, ExpectedStatus, Expr, Formula};
use crate::paving::{domain_interval, eval_expr_iv, Iv};
use crate::stamp::{StampedBody, StampedSystem};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

fn scalar(q: f64) -> Result<String, String> {
    let (neg, n, d) = crate::numeral::exact_f64_to_rat(q)?;
    Ok(format!("{}{n}/{d}", if neg { "-" } else { "" }))
}

fn difference(a: &Expr, b: &Expr) -> Expr {
    // The folding constructors would round rational arithmetic back to f64.
    Expr::Sub(Box::new(a.clone()), Box::new(b.clone()))
}

fn definition(lhs: &Expr, rhs: &Expr) -> Option<(String, Expr)> {
    if let Expr::Var(v) = lhs {
        return Some((v.clone(), rhs.clone()));
    }
    if let (Expr::Exp(y), Expr::Add(one, exp)) = (lhs, rhs) {
        if let (Expr::Var(v), Expr::Num(1.0), Expr::Exp(z)) = (&**y, &**one, &**exp) {
            return Some((v.clone(), Expr::Ln1pExp(z.clone())));
        }
    }
    None
}

struct Model {
    names: BTreeMap<String, String>,
    defs: Vec<(String, Expr)>,
    coords: Vec<(String, f64, f64)>,
    initial: BTreeMap<String, Iv>,
    source: String,
}

impl Model {
    fn term(&self, e: &Expr) -> Result<String, String> {
        expression(e, &|v| {
            self.names
                .get(v)
                .cloned()
                .ok_or_else(|| format!("unbound {v}"))
        })
    }

    fn bind(&mut self, name: &str, term: &str) -> Result<(), String> {
        let id = format!("p{}", self.names.len());
        if self.names.insert(name.into(), id.clone()).is_some() {
            return Err(format!("duplicate root binding {name}"));
        }
        writeln!(self.source, "private def {id} : PExpr := {term} -- {name}").unwrap();
        Ok(())
    }

    fn face_env(&self, axis: usize, high: bool) -> Result<BTreeMap<String, Iv>, String> {
        let mut env = self.initial.clone();
        let (v, lo, hi) = &self.coords[axis];
        let point = if high { *hi } else { *lo };
        env.insert(v.clone(), domain_interval(point, point)?);
        for (v, e) in &self.defs {
            env.insert(
                v.clone(),
                eval_expr_iv(e, &env).ok_or_else(|| format!("cannot enclose {v}"))?,
            );
        }
        Ok(env)
    }

    // Logical side conditions are checked over the entire root box, including
    // device domains and the specified failure predicate.
    fn inequality(&self, a: &Expr, b: &Expr, strict: bool) -> Result<String, String> {
        let term = self.term(&difference(b, a))?;
        let rule = if strict {
            "sub_pos.mp"
        } else {
            "sub_nonneg.mp"
        };
        Ok(format!(
            "{rule} (positive_of_check rootBox {term} {strict} hx (by decide +kernel))"
        ))
    }

    fn append_guard(&self, f: &Formula, steps: &mut Vec<String>) -> Result<(), String> {
        let proof = match f {
            Formula::Cmp {
                op: CmpOp::Le,
                lhs,
                rhs,
            } => self.inequality(lhs, rhs, false)?,
            Formula::Cmp {
                op: CmpOp::Lt,
                lhs,
                rhs,
            } => self.inequality(lhs, rhs, true)?,
            Formula::Cmp {
                op: CmpOp::Ge,
                lhs,
                rhs,
            } => self.inequality(rhs, lhs, false)?,
            Formula::Cmp {
                op: CmpOp::Gt,
                lhs,
                rhs,
            } => self.inequality(rhs, lhs, true)?,
            Formula::And(xs) if xs.is_empty() => "trivial".into(),
            Formula::And(xs) => {
                for x in xs {
                    self.append_guard(x, steps)?;
                }
                return Ok(());
            }
            _ => {
                return Err("root-box side conditions require inequalities or conjunctions".into())
            }
        };
        steps.push(proof);
        Ok(())
    }
}

pub fn emit_root_box(sys: &StampedSystem, hints: &[String]) -> Result<String, String> {
    let StampedBody::Algebraic { vars, constraints } = &sys.body else {
        return Err("root boxes require a DC stamp".into());
    };
    if sys.expected != Some(ExpectedStatus::Sat) {
        return Err("root boxes require .expected sat".into());
    }
    let bindings: Vec<_> = sys
        .params
        .iter()
        .map(|p| (&p.name, Some((p.lo, p.hi))))
        .chain(vars.iter().map(|v| (&v.name, v.bounds)))
        .collect();
    let mut model = Model {
        names: BTreeMap::new(),
        defs: Vec::new(),
        coords: Vec::new(),
        initial: BTreeMap::new(),
        source: String::new(),
    };
    for hint in hints {
        let (name, raw) = hint
            .split_once('=')
            .ok_or("expected name=value or name=lo:hi")?;
        if !bindings.iter().any(|(v, _)| v.as_str() == name) {
            return Err(format!("unknown coordinate {name}"));
        }
        let number = |s: &str| {
            s.parse::<f64>()
                .ok()
                .filter(|v| v.is_finite())
                .ok_or_else(|| format!("invalid decimal {s}"))
        };
        let (lo, hi, term) = if let Some((l, h)) = raw.split_once(':') {
            let (lo, hi) = (number(l)?, number(h)?);
            if lo > hi {
                return Err(format!("reversed box for {name}"));
            }
            let id = model.coords.len();
            model.coords.push((name.into(), lo, hi));
            (lo, hi, format!(".var {id}"))
        } else {
            let v = number(raw)?;
            (v, v, model.term(&Expr::Num(v))?)
        };
        model.bind(name, &term)?;
        model
            .initial
            .insert(name.to_owned(), domain_interval(lo, hi)?);
    }
    let n = model.coords.len();
    if n == 0 {
        return Err("at least one root coordinate is required".into());
    }
    let mut proofs = BTreeMap::new();
    // Eliminate acyclic stamped assignments, retaining equations for all free coordinates.
    loop {
        let mut changed = false;
        for (i, c) in constraints.iter().enumerate() {
            if let Formula::Cmp {
                op: CmpOp::Eq,
                lhs,
                rhs,
            } = &c.formula
            {
                let Some((v, e)) = definition(lhs, rhs) else {
                    continue;
                };
                if model.names.contains_key(&v) {
                    continue;
                }
                let Ok(term) = model.term(&e) else {
                    continue;
                };
                let proof = if let Expr::Ln1pExp(z) = &e {
                    if matches!(lhs, Expr::Exp(_)) {
                        format!(
                            "exp_softplus (({} : PExpr).eval realTF (values x))",
                            model.term(z)?
                        )
                    } else {
                        "rfl".into()
                    }
                } else {
                    "rfl".into()
                };
                model.bind(&v, &term)?;
                model.defs.push((v, e));
                proofs.insert(i, proof);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    for (v, _) in &bindings {
        if !model.names.contains_key(*v) {
            return Err(format!("supply a value or interval for {v}"));
        }
    }
    let eqs: Vec<_> = constraints
        .iter()
        .enumerate()
        .filter_map(|(i, c)| match &c.formula {
            Formula::Cmp {
                op: CmpOp::Eq,
                lhs,
                rhs,
            } if !proofs.contains_key(&i) => Some((i, difference(lhs, rhs))),
            _ => None,
        })
        .collect();
    if eqs.len() != n {
        return Err(format!(
            "{} residual equations for {n} coordinates",
            eqs.len()
        ));
    }
    let mut rows = Vec::new();
    let mut used = BTreeSet::new();
    for (axis, (name, _, _)) in model.coords.iter().enumerate() {
        let lo = model.face_env(axis, false)?;
        let hi = model.face_env(axis, true)?;
        let (i, e, reverse) = eqs
            .iter()
            .filter(|(i, _)| !used.contains(i))
            .find_map(|(i, e)| {
                let l = eval_expr_iv(e, &lo)?;
                let h = eval_expr_iv(e, &hi)?;
                if l.hi <= 0. && h.lo >= 0. {
                    Some((*i, e, false))
                } else if h.hi <= 0. && l.lo >= 0. {
                    Some((*i, e, true))
                } else {
                    None
                }
            })
            .ok_or_else(|| format!("no residual has opposite verified face signs for {name}"))?;
        used.insert(i);
        let Expr::Sub(a, b) = e else { unreachable!() };
        let term = if reverse {
            model.term(&difference(b, a))?
        } else {
            model.term(e)?
        };
        rows.push(term);
        let symm = if reverse { ".symm" } else { "" };
        proofs.insert(i, format!("(sub_eq_zero.mp (hr {axis})){symm}"));
    }
    let intervals = model
        .coords
        .iter()
        .map(|(_, l, h)| {
            Ok(format!(
                "⟨{}, {}, by decide +kernel⟩",
                scalar(*l)?,
                scalar(*h)?
            ))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let mut steps = Vec::new();
    for (v, b) in &bindings {
        if let Some((l, h)) = b {
            let x = Expr::Var((*v).clone());
            steps.push(model.inequality(&Expr::Num(*l), &x, false)?);
            steps.push(model.inequality(&x, &Expr::Num(*h), false)?);
        }
    }
    if steps.is_empty() {
        steps.push("trivial".into());
    }
    for (i, c) in constraints.iter().enumerate() {
        if let Some(p) = proofs.get(&i) {
            steps.push(p.clone());
        } else {
            model.append_guard(&c.formula, &mut steps)?;
        }
    }
    model.append_guard(&sys.unsafe_formula, &mut steps)?;
    let args = bindings
        .iter()
        .map(|(v, _)| format!("{}.eval realTF (values x)", model.names[*v]))
        .collect::<Vec<_>>()
        .join(", ");
    Ok(format!("import SpiceSmtBench.BoxCertificate\n\n{}\nopen IntervalCheck BoxCertificate\n\n{}\nprivate def rootBox : Box {n} := ![{}]\nprivate def rows : Fin {n} → PExpr := ![{}]\n\nset_option maxRecDepth 32000 in\nset_option maxHeartbeats 300000 in\ntheorem certified : Target realTF := by\n  obtain ⟨x,hx,hr⟩ := checked_root rootBox rows (by decide +kernel) (by decide +kernel)\n  refine ⟨{args}, ?_⟩\n  simp only [realTF.zero_eq_ofRat, realTF.one_eq_ofRat, realTF.ofInt_eq_ofRat]\n  repeat' apply And.intro\n{}\n\nend SpiceSmtBench.Certificate\n",stamp_text(sys),model.source,intervals.join(", "),rows.join(",\n  "),steps.iter().map(|p|format!("  · exact {p}")).collect::<Vec<_>>().join("\n")))
}
