import SpiceSmtBench.LinearTransient
import SpiceSmtBench.Microstrip
import SpiceSmtBench.StoredEnergy

namespace SpiceSmtBench.LineBounds
open Enclosed LeanCert.Core IntervalRat

scoped instance (n : Nat) : OfNat Enclosed n := ⟨const n⟩
@[simp] theorem numeral_val (n : Nat) : (no_index (OfNat.ofNat n : Enclosed)).val = (n:ℝ) := by
  change ((n:ℚ):ℝ) = n
  simp

structure Components where
  cp : Enclosed
  cn : Enclosed
  cm : Enclosed
  lp : Enclosed
  ln : Enclosed
  lm : Enclosed
  via : Enclosed
  ret : Enclosed
  k : Enclosed
  r : Enclosed

def box (lo hi : ℚ) (h : lo ≤ hi) := IntervalRat.mk lo hi h

def atPoint (b : IntervalRat) (x : ℝ) (h : x ∈ b) : Enclosed :=
  ⟨x,some b,by rintro _ ⟨⟩; exact h⟩
def atLo (b : IntervalRat) : Enclosed :=
  atPoint b b.lo ⟨le_rfl,Rat.cast_le.mpr b.le⟩

private def absBox (a : IntervalRat) : IntervalRat :=
  ⟨0,max (-a.lo) a.hi,by
    rcases le_total a.lo 0 with h|h
    · exact le_max_of_le_left (by linarith)
    · exact le_max_of_le_right (h.trans a.le)⟩
noncomputable def magnitude (x : Enclosed) : Enclosed :=
  ⟨|x.val|,x.box.map absBox,by
    intro b he
    obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp he
    obtain ⟨l,u⟩ := x.valid ha
    simp only [mem_def,absBox,Rat.cast_zero,Rat.cast_max,Rat.cast_neg,abs_nonneg,true_and]
    exact abs_le.mpr ⟨by have := le_max_left (-(a.lo:ℝ)) (a.hi:ℝ); linarith,
      u.trans (le_max_right ..)⟩⟩
@[simp] theorem magnitude_val (x : Enclosed) : (magnitude x).val=|x.val| := rfl

noncomputable def total {n : Nat} (x : Fin n → Enclosed) : Enclosed :=
  match n with
  | 0 => const 0
  | n+1 => x 0 + total (fun i : Fin n => x i.succ)
theorem total_val {n} (x : Fin n → Enclosed) : (total x).val = ∑ i, (x i).val := by
  induction n with
  | zero => simp [total]
  | succ n ih => rw [Fin.sum_univ_succ]; simp only [total,add_val,ih]

noncomputable def margin {n} (m : Fin n → Fin n → Enclosed) (w : Fin n → Enclosed) (i : Fin n) :=
  m i i - w i * w i - total (fun j => if i=j then const 0 else magnitude (m i j))

theorem margin_ok {n} (m : Fin n → Fin n → Enclosed) (w : Fin n → Enclosed) (i : Fin n)
    (h : (margin m w i).positive) :
    (w i).val^2 + (∑ j, if i=j then 0 else |(m i j).val|) ≤ (m i i).val := by
  have a := pos h
  simp only [margin,sub_val,mul_val,total_val,apply_ite,const_val,Rat.cast_zero,magnitude_val] at a
  linarith [sq (w i).val]

end SpiceSmtBench.LineBounds
