import SpiceSmtBench.BoxRoot
import SpiceSmtBench.RealInterval

namespace SpiceSmtBench.BoxCertificate
open LeanCert.Core IntervalCheck RealInterval

abbrev Box (n : Nat) := Fin n → I

def readCoord {n : Nat} {α : Type} (x : Fin n → α) (fallback : α) (j : Nat) :=
  if h : j < n then x ⟨j,h⟩ else fallback

def values {n : Nat} (x : Fin n → ℝ) := readCoord x 0

private def ranges {n : Nat} (box : Box n) := readCoord box (.singleton 0)

def endpoint (a : I) (high : Bool) := if high then a.hi else a.lo

private def face {n : Nat} (box : Box n) (i : Fin n) (high : Bool) : Box n :=
  Function.update box i (.singleton (endpoint (box i) high))

def checkFace {n : Nat} (box : Box n) (row : PExpr) (i : Fin n) (high : Bool) :=
  (enclose (ranges (face box i high)) row).any fun v =>
    if high then decide (0 ≤ v.lo) else decide (v.hi ≤ 0)

def checkDomain {n : Nat} (box : Box n) (row : PExpr) := (enclose (ranges box) row).isSome

private theorem mem_ranges {n : Nat} {x : Fin n → ℝ} {box : Box n}
    (hx : ∀ i, x i ∈ box i) (j : Nat) : values x j ∈ ranges box j := by
  unfold values ranges readCoord
  split
  · apply hx
  · exact_mod_cast IntervalRat.mem_singleton 0

private theorem face_sign {n : Nat} {box : Box n} {row : PExpr} {i : Fin n}
    {x : Fin n → ℝ} (hx : ∀ j, x j ∈ box j) (high : Bool)
    (side : x i = (endpoint (box i) high : ℝ)) (ok : checkFace box row i high) :
    if high then 0 ≤ row.eval realTF (values x) else row.eval realTF (values x) ≤ 0 := by
  have hm : ∀ j, x j ∈ face box i high j := by
    intro j
    by_cases h : j = i
    · subst j
      simpa only [face, Function.update_self, side] using IntervalRat.mem_singleton (endpoint (box i) high)
    · simpa [face,h] using hx j
  unfold checkFace at ok
  cases he : enclose (ranges (face box i high)) row with
  | none => simp [he] at ok
  | some v =>
    have hv := enclose_sound row _ _ (mem_ranges hm) he
    cases high <;> simp_all only [Option.any_some, Bool.false_eq_true, ↓reduceIte,
      decide_eq_true_eq]
    · exact hv.2.trans (by exact_mod_cast ok)
    · exact (show (0:ℝ) ≤ v.lo by exact_mod_cast ok).trans hv.1

theorem exp_softplus (z : ℝ) :
    realTF.exp (realTF.ln1pExp z) = realTF.add (realTF.ofRat 1 1) (realTF.exp z) := by
  rw [← realTF.one_eq_ofRat, realTF.ln1pExp_spec]

/-- Side conditions on the root, including parameter bounds and strict failure guards. -/
def checkPositive {n : Nat} (box : Box n) (e : PExpr) (strict : Bool) :=
  (enclose (ranges box) e).any fun v =>
    if strict then decide (0 < v.lo) else decide (0 ≤ v.lo)

theorem positive_of_check {n : Nat} (box : Box n) (e : PExpr) (strict : Bool)
    {x : Fin n → ℝ} (hx : ∀ j, x j ∈ box j) (ok : checkPositive box e strict) :
    if strict then 0 < e.eval realTF (values x) else 0 ≤ e.eval realTF (values x) := by
  unfold checkPositive at ok
  cases he : enclose (ranges box) e with
  | none => simp [he] at ok
  | some v =>
    have h := (enclose_sound e _ _ (mem_ranges hx) he).1
    cases strict <;> simp_all only [Option.any_some, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
    · exact (show (0:ℝ) ≤ v.lo by exact_mod_cast ok).trans h
    · exact (show (0:ℝ) < v.lo by exact_mod_cast ok).trans_le h

/-- Check all residuals on a rational box and both faces normal to each
coordinate. Every returned real assignment simultaneously zeros every row. -/
theorem checked_root {n : Nat} (box : Box n) (rows : Fin n → PExpr)
    (domain : ∀ i, checkDomain box (rows i))
    (faces : ∀ i high, checkFace box (rows i) i high) :
    ∃ x : Fin n → ℝ, (∀ i, x i ∈ box i) ∧ ∀ i, (rows i).eval realTF (values x) = 0 := by
  let lo (i : Fin n) : ℝ := (box i).lo
  let hi (i : Fin n) : ℝ := (box i).hi
  let f (x : Fin n → ℝ) (i : Fin n) := (rows i).eval realTF (values x)
  have mem {x : Fin n → ℝ} (hx : x ∈ Set.Icc lo hi) (i : Fin n) : x i ∈ box i :=
    ⟨hx.1 i,hx.2 i⟩
  have cont : ContinuousOn f (Set.Icc lo hi) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply continuous_pi
    intro i
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (domain i)
    apply enclose_continuous (rows i) _ (fun x : Set.Icc lo hi => values x.val)
      (fun x => mem_ranges (mem x.property)) _ hv
    intro j
    unfold values readCoord
    split
    · exact (continuous_apply _).comp continuous_subtype_val
    · exact continuous_const
  obtain ⟨x,hx,hr⟩ := box_root lo hi (fun i => by dsimp [lo,hi]; exact_mod_cast (box i).le) f cont
    (fun x hx i e => face_sign (mem hx) false e (faces i false))
    (fun x hx i e => face_sign (mem hx) true e (faces i true))
  exact ⟨x,mem hx,fun i => congrFun hr i⟩

end SpiceSmtBench.BoxCertificate
