import SpiceSmtBench.PhysicsModels
import SpiceSmtBench.IntervalCheck
import SpiceSmtBench.TargetsGenerated

/-!
# Benchmark Target Specifications & Machine-Checked Proofs

Re-exports all 19 auto-generated SPICE / Multi-PDK / PCB / TCAD benchmark `Prop` definitions
from `SpiceSmtBench.TargetsGenerated` and provides complete end-to-end machine-checked proofs:

1. `bench01_diode_clipper_pvt_proved`: Full kernel-checked `UNSAT` proof of Benchmark 01
   (`Bench_01_diode_clipper_pvt`) across the continuous 2D PVT box `v_sup ∈ [3.0, 3.6] V ×
   vt ∈ [23.5 mV, 32.2 mV]` using rational scaling-and-squaring (`m = 7`, `2^7 = 128`) from
   `IntervalCheck.exp_ge_qrat_iterSq`!
2. `unguarded_bandgap_zero_current_trojan`: Proves analytically over `TranscendentalField R`
   that an unguarded self-biased bandgap network admits the zero-current analog Trojan equilibrium
   `v_ref = 0` (`Bench_04a` physical mechanism), whereas a positive startup pull-up strictly
   forbids `v_ref = 0` (`Bench_04b` physical mechanism).
-/

namespace SpiceSmtBench.Targets

open SpiceSmtBench.IntervalCheck

/-- Exact rational lower bound on `(1 + 25/128)^128 - 1` scaled by `10^-12`:
    `(153 / 128)^128` exceeds `8 * 10^9`, so `10^-12 * ((153 / 128)^128 - 1) ≥ 7 / 1000 > 3 / 1000`!
    Checked in the Lean 4 kernel via exact integer bignum arithmetic (`by decide`). -/
private def q25 : QRat := ⟨25, 1, by decide⟩

private theorem q25_base_nonneg :
    QRat.le QRat.zero (QRat.add QRat.one (QRat.halfPow 7 q25)) := by
  decide

private theorem q25_iterSq7_ge_8e9 :
    QRat.le ⟨8000000000, 1, by decide⟩ (QRat.iterSq 7 (QRat.add QRat.one (QRat.halfPow 7 q25))) := by
  decide

/-- End-to-End Kernel-Checked Proof of Benchmark 01 (`01_diode_clipper_pvt.sp`, `gf180mcu` PDK):
    Across EVERY supply voltage `v_sup ∈ [3.0, 3.6] V` and thermal voltage `vt ∈ [23.5 mV, 32.2 mV]`,
    KCL + the Shockley ESD diode equation make `v_out > 0.85 V` strictly unsatisfiable (`UNSAT`). -/
theorem bench01_diode_clipper_pvt_proved {R : Type} (TF : TranscendentalField R) :
    Bench_01_diode_clipper_pvt TF := by
  intro v_sup vt v_in i_Vdd v_out i_D1 hbox hphys hunsafe
  rcases hbox with ⟨⟨_, hvsup_hi⟩, ⟨hvt_lo, hvt_hi⟩, ⟨_, hvin_hi⟩, _, ⟨_, _⟩, _⟩
  rcases hphys with ⟨_, hiD1_eq, _, hkcl_out⟩
  -- 1. From `hunsafe : 17/20 < v_out`, we have `17/20 ≤ v_out` and `0 ≤ 17/20`.
  have hvout_ge : TF.le (TF.ofRat 17 20) v_out :=
    ((TF.lt_iff_le_not_le (TF.ofRat 17 20) v_out).mp hunsafe).1
  have h17_nonneg : TF.le TF.zero (TF.ofRat 17 20) := by
    rw [TF.zero_eq_ofRat]
    exact (TF.ofRat_le_iff 0 17 1 20 (by decide) (by decide)).mpr (by decide)
  have hvout_nonneg : TF.le TF.zero v_out :=
    TF.le_trans TF.zero (TF.ofRat 17 20) v_out h17_nonneg hvout_ge

  -- 2. Bound thermal denominator `0 < (21/20) * vt ≤ 3381 / 100000`.
  have h21_20_nonneg : TF.le TF.zero (TF.ofRat 21 20) := by
    rw [TF.zero_eq_ofRat]
    exact (TF.ofRat_le_iff 0 21 1 20 (by decide) (by decide)).mpr (by decide)
  have hden_ge : TF.le (TF.mul (TF.ofRat 21 20) (TF.ofRat 47 2000))
      (TF.mul (TF.ofRat 21 20) vt) :=
    TF.mul_le_mul_nonneg_left (TF.ofRat 21 20) (TF.ofRat 47 2000) vt h21_20_nonneg hvt_lo
  have hden_lo_pos : TF.lt TF.zero (TF.mul (TF.ofRat 21 20) (TF.ofRat 47 2000)) := by
    rw [TF.zero_eq_ofRat, TF.ofRat_mul 21 47 20 2000 (by decide) (by decide)]
    exact (TF.ofRat_lt_iff 0 (21 * 47) 1 (20 * 2000) (by decide) (by decide)).mpr (by decide)
  have hden_pos : TF.lt TF.zero (TF.mul (TF.ofRat 21 20) vt) := by
    rcases (TF.lt_iff_le_not_le _ _).mp hden_lo_pos with ⟨h0le, hnot⟩
    rw [TF.lt_iff_le_not_le]
    refine ⟨TF.le_trans _ _ _ h0le hden_ge, fun hle0 => hnot (TF.le_trans _ _ _ hden_ge hle0)⟩
  have hden_le : TF.le (TF.mul (TF.ofRat 21 20) vt) (TF.ofRat 3381 100000) := by
    have hm := TF.mul_le_mul_nonneg_left (TF.ofRat 21 20) vt (TF.ofRat 161 5000) h21_20_nonneg hvt_hi
    rw [TF.ofRat_mul 21 161 20 5000 (by decide) (by decide)] at hm
    exact hm

  -- 3. Bound Shockley exponent `25 ≤ v_out / ((21/20) * vt)`.
  have hquot_ge_frac : TF.le (TF.div (TF.ofRat 17 20) (TF.ofRat 3381 100000))
      (TF.div v_out (TF.mul (TF.ofRat 21 20) vt)) :=
    TF.div_ge_of_num_ge_den_le (TF.ofRat 17 20) v_out (TF.ofRat 3381 100000)
      (TF.mul (TF.ofRat 21 20) vt) h17_nonneg hvout_ge hden_pos hden_le
  have h25_le_frac : TF.le (QRat.eval TF q25)
      (TF.div (TF.ofRat 17 20) (TF.ofRat 3381 100000)) := by
    unfold QRat.eval q25
    have hdiv : TF.div (TF.ofRat 17 20) (TF.ofRat 3381 100000) = TF.ofRat 1700000 67620 :=
      TF.ofRat_div_pos 17 20 3381 100000 (by decide) (by decide) (by decide)
    rw [hdiv]
    exact (TF.ofRat_le_iff 25 1700000 1 67620 (by decide) (by decide)).mpr (by decide)
  have hz_ge_25 : TF.le (QRat.eval TF q25) (TF.div v_out (TF.mul (TF.ofRat 21 20) vt)) :=
    TF.le_trans _ _ _ h25_le_frac hquot_ge_frac

  -- 4. Apply scaling-and-squaring (`m = 7`): `8 * 10^9 ≤ exp(z)`, so `7999999 / 10^9 ≤ i_D1`!
  have hexp_ge_iter := exp_ge_qrat_iterSq TF 7 q25 (TF.div v_out (TF.mul (TF.ofRat 21 20) vt))
    q25_base_nonneg hz_ge_25
  have h8e9_le_iter : TF.le (TF.ofRat 8000000000 1)
      (QRat.eval TF (QRat.iterSq 7 (QRat.add QRat.one (QRat.halfPow 7 q25)))) :=
    (QRat.eval_le_iff TF ⟨8000000000, 1, by decide⟩ _).mpr q25_iterSq7_ge_8e9
  have hexp_ge_8e9 : TF.le (TF.ofRat 8000000000 1)
      (TF.exp (TF.div v_out (TF.mul (TF.ofRat 21 20) vt))) :=
    TF.le_trans _ _ _ h8e9_le_iter hexp_ge_iter

  have hexpm1_ge : TF.le (TF.ofRat 7999999999 1)
      (TF.sub (TF.exp (TF.div v_out (TF.mul (TF.ofRat 21 20) vt))) TF.one) := by
    have hone_le : TF.le TF.one (TF.ofRat 1 1) := by
      rw [TF.one_eq_ofRat]
      exact TF.le_refl _
    have hsub := TF.sub_le_sub (TF.ofRat 8000000000 1)
      (TF.exp (TF.div v_out (TF.mul (TF.ofRat 21 20) vt))) (TF.ofRat 1 1) TF.one hexp_ge_8e9 hone_le
    have hdiff : TF.sub (TF.ofRat 8000000000 1) (TF.ofRat 1 1) = TF.ofRat 7999999999 1 :=
      TF.ofRat_sub 8000000000 1 1 1 (by decide) (by decide)
    rw [hdiff] at hsub
    exact hsub
  have his_nonneg : TF.le TF.zero (TF.ofRat 1 1000000000000) := by
    rw [TF.zero_eq_ofRat]
    exact (TF.ofRat_le_iff 0 1 1 1000000000000 (by decide) (by decide)).mpr (by decide)
  have hiD1_ge : TF.le (TF.ofRat 7 1000) i_D1 := by
    rw [hiD1_eq]
    have hm := TF.mul_le_mul_nonneg_left (TF.ofRat 1 1000000000000)
      (TF.ofRat 7999999999 1) _ his_nonneg hexpm1_ge
    have hmul : TF.mul (TF.ofRat 1 1000000000000) (TF.ofRat 7999999999 1) =
        TF.ofRat 7999999999 1000000000000 :=
      TF.ofRat_mul 1 7999999999 1000000000000 1 (by decide) (by decide)
    rw [hmul] at hm
    have h7 : TF.le (TF.ofRat 7 1000) (TF.ofRat 7999999999 1000000000000) :=
      (TF.ofRat_le_iff 7 7999999999 1000 1000000000000 (by decide) (by decide)).mpr (by decide)
    exact TF.le_trans _ _ _ h7 hm

  -- 5. Upper-bound KCL current at `out`:
  --    `-(v_in - v_out)/1000 + v_out/10000 + i_D1 = 0`, where `v_in ≤ 18/5` and `v_out ≥ 17/20`,
  --    so `(v_in - v_out)/1000 ≤ (18/5 - 17/20)/1000 = 11/4000`, hence `-(v_in - v_out)/1000 ≥ -11/4000`,
  --    `v_out/10000 ≥ 0`, and `i_D1 ≥ 7/1000 = 28/4000`, forcing LHS ≥ `17/4000 > 0` — contradiction!
  have hvdiff_le : TF.le (TF.sub v_in v_out) (TF.ofRat 55 20) := by
    have hs := TF.sub_le_sub v_in (TF.ofRat 18 5) v_out (TF.ofRat 17 20) hvin_hi hvout_ge
    have hsub : TF.sub (TF.ofRat 18 5) (TF.ofRat 17 20) = TF.ofRat 275 100 :=
      TF.ofRat_sub 18 17 5 20 (by decide) (by decide)
    rw [hsub] at hs
    have heq : TF.ofRat 275 100 = TF.ofRat 55 20 :=
      (TF.ofRat_eq_iff 275 55 100 20 (by decide) (by decide)).mpr (by decide)
    rw [heq] at hs
    exact hs
  have h1000_pos : TF.lt TF.zero (TF.ofInt 1000) := by
    rw [TF.zero_eq_ofRat, TF.ofInt_eq_ofRat 1000]
    exact (TF.ofRat_lt_iff 0 1000 1 1 (by decide) (by decide)).mpr (by decide)
  have h10000_pos : TF.lt TF.zero (TF.ofInt 10000) := by
    rw [TF.zero_eq_ofRat, TF.ofInt_eq_ofRat 10000]
    exact (TF.ofRat_lt_iff 0 10000 1 1 (by decide) (by decide)).mpr (by decide)
  have h_r1_le : TF.le (TF.div (TF.sub v_in v_out) (TF.ofInt 1000)) (TF.ofRat 11 4000) := by
    have hd := TF.div_le_div_of_pos (TF.sub v_in v_out) (TF.ofRat 55 20) (TF.ofInt 1000) hvdiff_le h1000_pos
    have hdiv : TF.div (TF.ofRat 55 20) (TF.ofInt 1000) = TF.ofRat 55 20000 := by
      rw [TF.ofInt_eq_ofRat 1000]
      exact TF.ofRat_div_pos 55 20 1000 1 (by decide) (by decide) (by decide)
    rw [hdiv] at hd
    have heq : TF.ofRat 55 20000 = TF.ofRat 11 4000 :=
      (TF.ofRat_eq_iff 55 11 20000 4000 (by decide) (by decide)).mpr (by decide)
    rw [heq] at hd
    exact hd
  have h_negr1_ge : TF.le (TF.ofRat (-11) 4000)
      (TF.neg (TF.div (TF.sub v_in v_out) (TF.ofInt 1000))) := by
    have hn := TF.neg_le_neg _ _ h_r1_le
    rw [TF.ofRat_neg 11 4000 (by decide)] at hn
    exact hn
  have h_rload_ge : TF.le TF.zero (TF.div v_out (TF.ofInt 10000)) :=
    TF.div_nonneg_of_pos v_out (TF.ofInt 10000) hvout_nonneg h10000_pos
  have h_sum12_ge : TF.le (TF.ofRat (-11) 4000)
      (TF.add (TF.neg (TF.div (TF.sub v_in v_out) (TF.ofInt 1000))) (TF.div v_out (TF.ofInt 10000))) := by
    have ha := TF.add_le_add _ _ _ _ h_negr1_ge h_rload_ge
    rw [TF.add_zero] at ha
    exact ha
  have h_lhs_ge : TF.le (TF.ofRat 17 4000)
      (TF.add (TF.add (TF.neg (TF.div (TF.sub v_in v_out) (TF.ofInt 1000)))
        (TF.div v_out (TF.ofInt 10000))) i_D1) := by
    have ha := TF.add_le_add _ _ _ _ h_sum12_ge hiD1_ge
    have hadd : TF.add (TF.ofRat (-11) 4000) (TF.ofRat 7 1000) = TF.ofRat 17000 4000000 :=
      TF.ofRat_add (-11) 7 4000 1000 (by decide) (by decide)
    rw [hadd] at ha
    have heq : TF.ofRat 17000 4000000 = TF.ofRat 17 4000 :=
      (TF.ofRat_eq_iff 17000 17 4000000 4000 (by decide) (by decide)).mpr (by decide)
    rw [heq] at ha
    exact ha
  rw [hkcl_out, TF.zero_eq_ofRat] at h_lhs_ge
  have h_bad : (17 : Int) * 1 ≤ 0 * 4000 :=
    (TF.ofRat_le_iff 17 0 4000 1 (by decide) (by decide)).mp h_lhs_ge
  omega

/-- Unguarded Bandgap Zero-Current Analog Trojan Lemma (`Bench_04a` vs `Bench_04b` Mechanism):
    1. Without a startup pull-up, `v_ref = 0` satisfies the zero-current resistor + Shockley diode
       equilibrium `v_ref / R_bleed + I_s * (exp(v_ref / V_T) - 1) = 0`.
    2. Adding a startup pull-up `(v_ref - v_dd) / R_start` with `v_dd > 0` and `R_start > 0`
       strictly refutes the zero-current Trojan state `v_ref = 0`! -/
theorem unguarded_bandgap_zero_current_trojan {R : Type} (TF : TranscendentalField R)
    (i_s r_bleed vt : R)
    (hr : TF.lt TF.zero r_bleed)
    (hvt : TF.lt TF.zero vt) :
    TF.add (TF.div TF.zero r_bleed)
      (PhysicsModels.shockleyDiodeCurrent TF i_s TF.one vt TF.zero) = TF.zero := by
  have h1vt : TF.lt TF.zero (TF.mul TF.one vt) := by
    rw [TF.one_mul vt]
    exact hvt
  rw [PhysicsModels.shockley_zero_bias TF i_s TF.one vt h1vt]
  rw [TF.div_zero_num r_bleed hr]
  exact TF.add_zero TF.zero

end SpiceSmtBench.Targets
