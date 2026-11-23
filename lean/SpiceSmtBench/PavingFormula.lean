import SpiceSmtBench.RealPhysics
import SpiceSmtBench.IntervalCheck

namespace SpiceSmtBench.IntervalCheck

/-- Stamped predicates, including compound unsafe conditions. The same leaf
index selects a formula in the Rust tree and in the Lean certificate. -/
inductive PFormula where
  | lit (b : Bool)
  | atom (cmp : PCmp) (e : PExpr)
  | conj (a b : PFormula)
  | disj (a b : PFormula)
  | neg (a : PFormula)

def PFormula.holds (env : Nat → ℝ) : PFormula → Prop
  | .lit b => b = true
  | .atom cmp e => cmp.holds realTF (e.eval realTF env)
  | .conj a b => a.holds env ∧ b.holds env
  | .disj a b => a.holds env ∨ b.holds env
  | .neg a => ¬a.holds env

private def confirm (op : PCmp) (iv : QInterval) : Bool :=
  match op with
  | .eqZero => decide (QRat.le QRat.zero iv.lo ∧ QRat.le iv.hi QRat.zero)
  | .geZero => decide (QRat.le QRat.zero iv.lo)
  | .gtZero => decide (QRat.lt QRat.zero iv.lo)

private theorem confirm_sound (op : PCmp) {iv : QInterval} {x : ℝ}
    (hm : memInterval realTF iv x) (h : confirm op iv) : op.holds realTF x := by
  have low (h : QRat.le QRat.zero iv.lo) : 0 ≤ x := by
    have h' := (QRat.eval_le_iff realTF _ _).2 h
    rw [QRat.eval_zero] at h'
    exact le_trans h' hm.1
  cases op
  · obtain ⟨a,b⟩ := of_decide_eq_true h
    have h' := (QRat.eval_le_iff realTF _ _).2 b
    rw [QRat.eval_zero] at h'
    exact le_antisymm (le_trans hm.2 h') (low a)
  · have h' := (QRat.eval_lt_iff realTF _ _).2 (of_decide_eq_true h)
    rw [QRat.eval_zero] at h'
    exact lt_of_lt_of_le h' hm.1
  · exact low (of_decide_eq_true h)

def PFormula.check (box : List QInterval) (want : Bool) : PFormula → Bool
  | .lit b => want == b
  | .atom op e => (evalPExpr box e).any (if want then confirm op else refuteConstraint op)
  | .conj a b => if want then a.check box true && b.check box true
                         else a.check box false || b.check box false
  | .disj a b => if want then a.check box true || b.check box true
                         else a.check box false && b.check box false
  | .neg a => a.check box (!want)

theorem PFormula.check_sound (f : PFormula) (env : Nat → ℝ) (box : List QInterval)
    (hm : memBox realTF box env) (want : Bool) (ok : f.check box want) :
    if want then f.holds env else ¬f.holds env := by
  induction f generalizing want with
  | lit b => cases b <;> cases want <;> simp_all [check,holds]
  | atom op e =>
    cases he : evalPExpr box e with
    | none => simp [check,he] at ok
    | some iv =>
      have hv := evalPExpr_sound realTF box env hm e iv he
      cases want
      · exact refuteConstraint_sound realTF _ _ _ hv (by simpa [check,he] using ok)
      · exact confirm_sound _ hv (by simpa [check,he] using ok)
  | conj a b ha hb | disj a b ha hb =>
    cases want <;> simp_all only [check, holds, Bool.false_eq_true, ↓reduceIte,
      Bool.and_eq_true, Bool.or_eq_true] <;>
      grind [ha false, ha true, hb false, hb true]
  | neg a ha =>
    cases want <;> simp_all only [check, holds, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.not_true] <;> grind [ha true, ha false]

def checkFormulaLeaf (cs : List PFormula) (reason : Nat) (box : List QInterval) : Bool :=
  cs[reason]?.any (fun f => f.check box false)

theorem checkFormulaLeaf_sound (cs : List PFormula) (reason : Nat) (box : List QInterval)
    (env : Nat → ℝ) (ok : checkFormulaLeaf cs reason box) (hm : memBox realTF box env) :
    ¬ ∀ f ∈ cs, f.holds env := by
  cases he : cs[reason]? with
  | none => simp [checkFormulaLeaf,he] at ok
  | some f =>
    have hc : f.check box false := by simpa [checkFormulaLeaf,he] using ok
    exact fun hs => f.check_sound env box hm false hc (hs _ (List.mem_of_getElem? he))

end SpiceSmtBench.IntervalCheck
