import SpiceSmtBench.PhysicsModels
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SpiceSmtBench

attribute [class] TranscendentalField

/-- Real interpretation of the operations used by the SPICE stamps. -/
noncomputable instance realTF : TranscendentalField ℝ where
  zero := 0
  one := 1
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  neg := Neg.neg
  exp := Real.exp
  ln1pExp z := Real.log (1 + Real.exp z)
  sqrt := Real.sqrt
  ofInt n := n
  ofRat n d := n / (d : ℝ)
  le := (· ≤ ·)
  lt := (· < ·)
  sqrt_nonneg := Real.sqrt_nonneg
  sqrt_sq := fun _ h => Real.mul_self_sqrt h
  zero_eq_ofRat := by simp
  one_eq_ofRat := by simp
  ofInt_eq_ofRat := by simp
  ofRat_eq_iff := by
    intro a b da db ha hb
    rw [div_eq_div_iff (by positivity) (by positivity)]
    norm_cast
  ofRat_le_iff := by
    intro a b da db ha hb
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    norm_cast
  ofRat_lt_iff := by
    intro a b da db ha hb
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    norm_cast
  ofRat_add := by intros; push_cast; field_simp
  ofRat_sub := by intros; push_cast; field_simp
  ofRat_neg := by intros; push_cast; rw [neg_div]
  ofRat_mul := by intros; push_cast; rw [div_mul_div_comm]
  ofRat_div_pos := by intros; push_cast; field_simp
  add_comm := add_comm
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_neg_self := add_neg_cancel
  sub_eq_add_neg := sub_eq_add_neg
  sub_self := sub_self
  mul_comm := mul_comm
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_zero := mul_zero
  mul_add := mul_add
  mul_sub := mul_sub
  div_self_pos := fun _ h => div_self h.ne'
  div_zero_num := fun _ _ => zero_div _
  div_two_add_self := by intro x; ring
  mul_div_cancel_pos := fun _ _ h => div_mul_cancel₀ _ h.ne'
  neg_div := fun x y => (neg_div y x).symm
  le_refl := le_refl
  le_trans := fun _ _ _ => le_trans
  le_antisymm := fun _ _ => le_antisymm
  le_total := le_total
  lt_iff_le_not_le := fun _ _ => lt_iff_le_not_ge
  add_le_add := fun _ _ _ _ => add_le_add
  sub_le_sub := fun _ _ _ _ => sub_le_sub
  neg_le_neg := fun _ _ => neg_le_neg
  mul_nonneg := fun _ _ => mul_nonneg
  mul_le_mul_nonneg_left := fun _ _ _ hc h => mul_le_mul_of_nonneg_left h hc
  sq_mono_nonneg := fun _ _ ha hab => mul_self_le_mul_self ha hab
  div_nonneg_of_pos := fun _ _ ha hb => div_nonneg ha hb.le
  div_le_div_of_pos := fun _ _ _ h hc => div_le_div_of_nonneg_right h hc.le
  div_ge_of_num_ge_den_le := fun _ _ _ _ ha hab hb hba => div_le_div₀ (ha.trans hab) hab hb hba
  exp_zero := Real.exp_zero
  exp_pos := Real.exp_pos
  exp_pos_surj := fun y hy => ⟨Real.log y, Real.exp_log hy⟩
  exp_add := Real.exp_add
  exp_mono := fun _ _ => Real.exp_le_exp.mpr
  one_add_le_exp := fun x => add_comm x 1 ▸ Real.add_one_le_exp x
  ln1pExp_spec := fun _ => Real.exp_log (by positivity)

/-- Rational endpoints bound the exponential throughout the real input interval.
For example, inputs in [0, 1/2] give outputs in [1, 2]. -/
theorem real_exp_in_rat_enclosure (lo hi : ℚ) (x : ℝ)
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) (hn : 0 ≤ hi) (hu : hi < 1) :
    (((1 + lo : ℚ) : ℝ) ≤ Real.exp x) ∧
    Real.exp x ≤ (((1 / (1 - hi) : ℚ)) : ℝ) := by
  push_cast
  constructor
  · linarith [Real.add_one_le_exp x]
  · exact (Real.exp_le_exp.mpr hhi).trans
      (Real.exp_bound_div_one_sub_of_interval (by exact_mod_cast hn) (by exact_mod_cast hu))

/-- Repeated halving would give arbitrarily many successive square roots of
the reduced numerator. No rational-valued doubling model can exceed one. -/
theorem no_rational_exp_with_doubling :
    ¬ ∃ f : ℚ → ℚ, (∀ t, f (2*t) = f t * f t) ∧ ∃ x, 1 < f x := by
  rintro ⟨f, hd, x, hx⟩
  have small (n : ℕ) : ∀ t, (f t).num.natAbs = n → n ≤ 1 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t ht
      by_contra! hlarge
      have he : f t = f (t/2) ^ 2 := by
        rw [← show 2 * (t/2) = t by ring, hd, pow_two, show 2 * (t/2) = t by ring]
      rw [he, Rat.num_pow, Int.natAbs_pow] at ht
      let m := (f (t/2)).num.natAbs
      change m ^ 2 = n at ht
      have hm : 1 < m := by
        by_contra! h
        rcases (show m = 0 ∨ m = 1 by omega) with h0 | h1
        · simp [h0] at ht; omega
        · simp [h1] at ht; omega
      have hlt : m < n := by nlinarith
      exact (Nat.not_le_of_lt hm) (ih m hlt (t/2) rfl)
  have hs := small _ x rfl
  have hden := (f x).den_pos
  simp [Rat.lt_iff] at hx
  omega

end SpiceSmtBench
