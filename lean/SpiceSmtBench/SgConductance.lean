import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace SpiceSmtBench.SgConductance

/-- Resistance of a unit edge with linearly interpolated log conductivity. -/
noncomputable def resistance (a b : ℝ) :=
  ∫ x : ℝ in 0..1, Real.exp (-((1-x)*a+x*b))

noncomputable def conductance (a b : ℝ) := 1/resistance a b

private theorem positive (a b : ℝ) : 0 < resistance a b := by
  apply intervalIntegral.integral_pos (by norm_num) (by fun_prop)
    (fun _ _ => (Real.exp_pos _).le) ⟨0,⟨by norm_num, by norm_num⟩,Real.exp_pos _⟩

theorem conductance_pos (a b : ℝ) : 0 < conductance a b := one_div_pos.mpr (positive a b)

theorem monotone {a b A B : ℝ} (ha : a ≤ A) (hb : b ≤ B) : conductance a b ≤ conductance A B := by
  apply one_div_le_one_div_of_le (positive A B)
  apply intervalIntegral.integral_mono_on (by norm_num)
    (Continuous.intervalIntegrable (by fun_prop) ..) (Continuous.intervalIntegrable (by fun_prop) ..)
  intro x hx
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hx.2)) (mul_le_mul_of_nonneg_left hb hx.1))

private theorem integrated {a b : ℝ} (hn : a ≠ b) :
    resistance a b = (Real.exp (-a)-Real.exp (-b))/(b-a) := by
  have neq : a-b ≠ 0 := sub_ne_zero.mpr hn
  let f (x : ℝ) := Real.exp (-((1-x)*a+x*b))/(a-b)
  have derivative (x : ℝ) : HasDerivAt f (Real.exp (-((1-x)*a+x*b))) x := by
    have h := ((((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).mul_const a).add
      ((hasDerivAt_id x).mul_const b)).neg.exp.div_const (a-b)
    convert h using 1 <;> dsimp [f]; field_simp; ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1) (fun x _ => derivative x)
    (Continuous.intervalIntegrable (by fun_prop) ..)
  change resistance a b = _ at h
  rw [h]; simp [f]; field_simp; ring

theorem formula {a b : ℝ} (hn : a ≠ b) :
    conductance a b = (b-a)/(Real.exp (-a)-Real.exp (-b)) := by rw [conductance, integrated hn, one_div,inv_div]

theorem bernoulli {a b w : ℝ} (eqn : w*(Real.exp (b-a)-1)=b-a) (neutral : a=b → w=1) :
    w*Real.exp b = conductance a b := by
  by_cases h : a=b
  · subst b
    rw [neutral rfl,one_mul,conductance,resistance]
    simp_rw [show ∀ x : ℝ, (1-x)*a+x*a = a by intro x; ring]
    simp [Real.exp_neg]
  · rw [formula h]
    apply (eq_div_iff (sub_ne_zero.mpr (fun he => h (neg_injective (Real.exp_injective he))))).2
    calc
      _ = w*(Real.exp (b-a)-1) := by
        rw [mul_assoc,mul_sub,← Real.exp_add,← Real.exp_add,add_neg_cancel,Real.exp_zero]
        simp [sub_eq_add_neg]
      _ = _ := eqn

end SpiceSmtBench.SgConductance
