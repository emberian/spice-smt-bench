import SpiceSmtBench.TransientWindows
import SpiceSmtBench.BoxRoot

namespace SpiceSmtBench.TransferBox
open Enclosed LinearTransient TransientWindows

def identityBox {n : Nat} (i j : Fin n) : Window :=
  if i=j then ⟨scale,scale⟩ else ⟨0,0⟩

def rhsBox {n} (H : Fin n → Fin (n+1) → Window) (i : Fin n) :
    Fin (n+1) → Window :=
  Fin.cases (H i 0) (fun j => add (identityBox i j) (H i j.succ))

def image {n} (H T : Fin n → Fin (n+1) → Window) (i : Fin n) (j : Fin (n+1)) : Window :=
  add (applyRow (fun a => H i a.succ) (fun a => T a j)) (rhsBox H i j)

def contained (a b : Window) : Bool := decide (b.lo ≤ a.lo ∧ a.hi ≤ b.hi)
private theorem holds_of_contained {a b x} (h : contained a b) (hx : holds a x) : holds b x := by
  obtain ⟨l,u⟩ := of_decide_eq_true h
  exact ⟨(Int.cast_le.mpr l).trans hx.1,hx.2.trans (Int.cast_le.mpr u)⟩

/-- An invariant box for each column of the implicit trapezoidal transfer
matrix contains an exact real solution of its linear system. -/
theorem exists_transfer {n} (F : Flow n) (H T : Fin n → Fin (n+1) → Window)
    (coeff : ∀ i j, holds (H i j) ((F i).coeff j).val)
    (nonempty : ∀ i j, (T i j).lo ≤ (T i j).hi)
    (maps : ∀ i j, contained (image H T i j) (T i j)) :
    ∃ P : Grid n (n+1), (∀ i j, holds (T i j) (P i j).val) ∧
      ∀ i k, ∑ j, (lhs F i j).val*(P j k).val = (rhs F i k).val := by
  have hs : (0:ℝ) < scale := by norm_num [scale]
  have col (j : Fin (n+1)) : ∃ x : Fin n → ℝ,
      (∀ i, holds (T i j) (x i)) ∧
      ∀ i, x i = (∑ a, ((F i).coeff a.succ).val*x a) + (rhs F i j).val := by
    let lo := fun i => ((T i j).lo:ℝ)/scale
    let hi := fun i => ((T i j).hi:ℝ)/scale
    let f := fun (x : Fin n → ℝ) i => (∑ a, ((F i).coeff a.succ).val*x a) + (rhs F i j).val
    have lohi : lo ≤ hi := fun i => div_le_div_of_nonneg_right (Int.cast_le.mpr (nonempty i j)) hs.le
    have mem (x : Fin n → ℝ) : x ∈ Set.Icc lo hi ↔ ∀ i, holds (T i j) (x i) := by
      constructor
      · intro h i
        exact ⟨by simpa [mul_comm] using (div_le_iff₀ hs).mp (h.1 i),
          by simpa [mul_comm] using (le_div_iff₀ hs).mp (h.2 i)⟩
      · intro h
        exact ⟨fun i => (div_le_iff₀ hs).mpr (by simpa [mul_comm] using (h i).1),
          fun i => (le_div_iff₀ hs).mpr (by simpa [mul_comm] using (h i).2)⟩
    have into (x : Fin n → ℝ) (hx : x ∈ Set.Icc lo hi) : f x ∈ Set.Icc lo hi := by
      apply (mem _).mpr; intro i
      apply holds_of_contained (maps i j)
      apply add_ok (applyRow_ok _ _ _ _ (fun a => coeff i a.succ) ((mem _).mp hx))
      refine Fin.cases (coeff i 0) (fun a => ?_) j
      apply add_ok _ (coeff i a.succ)
      by_cases h : i=a <;> simp [identityBox,h,holds]
    obtain ⟨x,hx,eq⟩ := box_root lo hi lohi (fun x i => x i-f x i)
      (by dsimp [f]; fun_prop)
      (fun x h i e => by have := (into x h).1 i; linarith)
      (fun x h i e => by have := (into x h).2 i; linarith)
    exact ⟨x,(mem x).mp hx,fun i => sub_eq_zero.mp (congrFun eq i)⟩
  choose x enclosed law using col
  let P : Grid n (n+1) := fun i j => ⟨x j i,none,by simp⟩
  refine ⟨P,fun i j => enclosed j i,fun i j => ?_⟩
  simp only [lhs,sub_val,sub_mul,Finset.sum_sub_distrib]
  simp [apply_ite,ite_mul,P]
  linarith only [law j i]

end SpiceSmtBench.TransferBox
