import Mathlib.Analysis.Complex.ExponentialBounds
import SpiceSmtBench.BandgapCertificate
import SpiceSmtBench.RingCertificate
import SpiceSmtBench.FinCertificate
import SpiceSmtBench.GanCertificate
import SpiceSmtBench.PdnCertificate
import SpiceSmtBench.GaaCertificate
import SpiceSmtBench.GaaSafety
import SpiceSmtBench.RealPhysics
import SpiceSmtBench.SramReplay
import SpiceSmtBench.IntervalCheck
import SpiceSmtBench.TargetsGenerated
import SpiceSmtBench.PcbCertificate

/-!
# Benchmark Target Specifications & Machine-Checked Proofs

Re-exports all 19 auto-generated SPICE / Multi-PDK / PCB / TCAD benchmark `Prop` definitions
from `SpiceSmtBench.TargetsGenerated` and provides complete end-to-end machine-checked proofs:

Sixteen of the nineteen generated targets have end-to-end proofs over `ℝ` via `realTF`.

| Generated query | Proved over ℝ | Open |
| --- | --- | --- |
| UNSAT safety | 01, 02, 03a, 04b, 05, 06, 07, 08, 09a, 11, 13, 14a | 10, 12b |
| SAT violation | 03b, 04a, 09b, 14b | 12a |

Transient targets quantify over the integration samples in the generated stamps.
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

/-- Zero voltage satisfies the resistor/diode zero-current identity.
    This is a component lemma, not a theorem about the generated bandgap decks. -/
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

private def diodeResidual : PExpr :=
  .add (.add (.neg (.div (.sub (.var 0) (.var 2)) (.const ⟨1000, 1, by decide⟩)))
    (.div (.var 2) (.const ⟨10000, 1, by decide⟩)))
    (.mul (.const ⟨1, 1000000000000, by decide⟩)
      (.sub (.exp (.div (.var 2) (.mul (.const ⟨21, 20, by decide⟩) (.var 1)))) (.const QRat.one)))

private def diodeConstraints : List PConstraint :=
  [(.gtZero, .sub (.var 2) (.const ⟨17, 20, by decide⟩)), (.eqZero, diodeResidual)]

private def diodeBox : List QInterval :=
  [⟨⟨3, 1, by decide⟩, ⟨18, 5, by decide⟩⟩, ⟨⟨47, 2000, by decide⟩, ⟨161, 5000, by decide⟩⟩, ⟨⟨-1, 2, by decide⟩, ⟨18, 5, by decide⟩⟩]

private def diodeTree : PavingTree := .split 2 ⟨17, 20, by decide⟩ (.leaf 0) (.leaf 1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem diodeReplay : verifyPaving (checkConcreteLeaf diodeConstraints) diodeTree diodeBox = true := by
  decide

/-- Concrete two-leaf rational interval replay of the generated diode target. -/
theorem bench01_paving_certificate_proved {R : Type} (TF : TranscendentalField R) :
    Bench_01_diode_clipper_pvt TF := by
  intro vs vt vin iV vo iD hb hp hu
  let env : Nat → R := fun i => if i = 0 then vin else if i = 1 then vt else vo
  have hm : memBox TF diodeBox env := by
    rcases hb with ⟨_, hvt, hvin, _, hvo, _⟩
    exact ⟨⟨by simpa only [QRat.eval, TF.ofInt_eq_ofRat, env, ↓reduceIte] using hvin.1, hvin.2⟩, hvt, hvo, trivial⟩
  have active : holdsConstraints TF diodeConstraints env := by
    intro c hc
    simp only [diodeConstraints, List.mem_cons, List.not_mem_nil, or_false] at hc
    cases hc with
    | inl hc =>
      subst c
      change TF.lt TF.zero (TF.sub vo (TF.ofRat 17 20))
      obtain ⟨hle, hnot⟩ := (TF.lt_iff_le_not_le _ _).mp hu
      apply (TF.lt_iff_le_not_le _ _).mpr
      constructor
      · have h := TF.sub_le_sub _ _ (TF.ofRat 17 20) (TF.ofRat 17 20) hle (TF.le_refl _)
        simpa only [TF.sub_self] using h
      · intro h
        have h' := TF.add_le_add _ _ (TF.ofRat 17 20) (TF.ofRat 17 20) h (TF.le_refl _)
        have hn : TF.add (TF.neg (TF.ofRat 17 20)) (TF.ofRat 17 20) = TF.zero := by rw [TF.add_comm, TF.add_neg_self]
        exact hnot (by simpa only [TF.sub_eq_add_neg, TF.add_assoc, hn, TF.add_zero, TF.zero_add] using h')
    | inr hc =>
      subst c
      rcases hp with ⟨_, hd, _, hk⟩
      rw [hd] at hk
      simpa [PCmp.holds, diodeResidual, PExpr.eval, QRat.eval, QRat.one,
        env, TF.ofInt_eq_ofRat, TF.one_eq_ofRat] using hk
  exact paving_unsat_sound TF (holdsConstraints TF diodeConstraints) (checkConcreteLeaf diodeConstraints)
    (checkConcreteLeaf_sound TF diodeConstraints) diodeTree diodeBox env diodeReplay hm active

/-- Positive startup injection makes the zero-voltage resistor/diode KCL impossible.
    This is a component theorem, independent of the generated bandgap circuit. -/
theorem guarded_bandgap_startup_refutes_zero_current {R : Type} (TF : TranscendentalField R)
    (i_s r_bleed vt startup : R) (hr : TF.lt TF.zero r_bleed)
    (hvt : TF.lt TF.zero vt) (hstart : TF.lt TF.zero startup) :
    ¬ (TF.sub (TF.add (TF.div TF.zero r_bleed)
      (PhysicsModels.shockleyDiodeCurrent TF i_s TF.one vt TF.zero)) startup = TF.zero) := by
  rw [unguarded_bandgap_zero_current_trojan TF i_s r_bleed vt hr hvt,
    TF.sub_eq_add_neg, TF.zero_add]
  intro h
  have he := congrArg (fun z => TF.add startup z) h
  have hs : TF.zero = startup := by simpa only [TF.add_neg_self, TF.add_zero] using he
  exact ((TF.lt_iff_le_not_le _ _).mp hstart).2 (hs ▸ TF.le_refl TF.zero)

private def filterSlope : PExpr :=
  let z := PExpr.div (.sub (.var 4) (.const ⟨1,4000000000,by decide⟩)) (.const ⟨9,50000000000,by decide⟩)
  .div (.sub (.sub (.mul (.var 0) (.exp (.neg (.mul z z)))) (.div (.var 3) (.const ⟨2500,1,by decide⟩)))
    (.mul (.const ⟨3,2500000000000,by decide⟩) (.sub (.exp (.div (.var 3) (.mul (.const ⟨21,20,by decide⟩) (.var 1)))) (.const QRat.one))))
    (.const ⟨1,125000000000,by decide⟩)

private def filterStepConstraints : List PConstraint :=
  [(.eqZero, .sub (.var 3) (.add (.var 2) (.mul (.const ⟨1,10000000000,by decide⟩) filterSlope)))]

private def filterStepBox : List QInterval :=
  [⟨QRat.zero, ⟨7,200,by decide⟩⟩,
   ⟨⟨3,125,by decide⟩, ⟨31,1000,by decide⟩⟩,
   ⟨⟨-1,5,by decide⟩, QRat.one⟩,
   ⟨QRat.one, ⟨2,1,by decide⟩⟩,
   ⟨QRat.zero, ⟨3,5000000000,by decide⟩⟩]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem filterStepReplay : checkConcreteLeaf filterStepConstraints 0 filterStepBox = true := by decide

/-- A rational barrier certificate proves every backward-Euler sample of 06 safe. -/
theorem bench06_rc_diode_glitch_filter_proved {R : Type} (TF : TranscendentalField R) :
    Bench_06_rc_diode_glitch_filter_ode TF := by
  intro ip vt state
  dsimp only
  intro hb hp hu
  rcases hb with ⟨hip, hvt, hs⟩
  rcases hp with ⟨hi, hstep⟩
  have guard : ∀ k, k ≤ 6 → TF.le (state k 0) TF.one := by
    intro k hk
    induction k with
    | zero =>
      apply TF.le_trans _ _ _ hi.2
      rw [TF.one_eq_ofRat]
      exact (TF.ofRat_le_iff 1 1 20 1 (by decide) (by decide)).mpr (by decide)
    | succ k ih =>
      have hk' : k ≤ 6 := by omega
      have hk6 : k < 6 := by omega
      cases TF.le_total (state (k+1) 0) TF.one with
      | inl h => exact h
      | inr h =>
        let t : R := ([TF.zero, TF.ofRat 1 10000000000, TF.ofRat 1 5000000000,
          TF.ofRat 3 10000000000, TF.ofRat 1 2500000000, TF.ofRat 1 2000000000,
          TF.ofRat 3 5000000000] : List R).getD (k+1) TF.zero
        have ht : TF.le TF.zero t ∧ TF.le t (TF.ofRat 3 5000000000) := by
          have casesK : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
          rcases casesK with h | h | h | h | h | h <;> subst k <;>
            simp only [t, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] <;>
            constructor <;> (try rw [TF.zero_eq_ofRat]) <;>
            apply (TF.ofRat_le_iff _ _ _ _ (by decide) (by decide)).mpr <;> decide
        let env : Nat → R := fun i => ([ip, vt, state k 0, state (k+1) 0, t] : List R).getD i TF.zero
        have hm : memBox TF filterStepBox env := by
          change (TF.le (QRat.eval TF QRat.zero) ip ∧ TF.le ip (TF.ofRat 7 200)) ∧
            (TF.le (TF.ofRat 3 125) vt ∧ TF.le vt (TF.ofRat 31 1000)) ∧
            (TF.le (TF.ofRat (-1) 5) (state k 0) ∧ TF.le (state k 0) (QRat.eval TF QRat.one)) ∧
            (TF.le (QRat.eval TF QRat.one) (state (k+1) 0) ∧ TF.le (state (k+1) 0) (TF.ofRat 2 1)) ∧
            (TF.le (QRat.eval TF QRat.zero) t ∧ TF.le t (TF.ofRat 3 5000000000)) ∧ True
          rw [QRat.eval_zero, QRat.eval_one, ← TF.ofInt_eq_ofRat 2]
          exact ⟨hip, hvt, ⟨(hs k hk').1, ih hk'⟩, ⟨h, (hs (k+1) hk).2⟩, ht, trivial⟩
        have hc : holdsConstraints TF filterStepConstraints env := by
          intro c hc
          simp only [filterStepConstraints, List.mem_singleton] at hc
          subst c
          have he := hstep k hk6
          change state (k+1) 0 = _ at he
          change TF.sub (state (k+1) 0) _ = TF.zero
          have hv : (PExpr.add (.var 2) (.mul (.const ⟨1,10000000000,by decide⟩) filterSlope)).eval TF env = state (k+1) 0 := by
            simpa [PExpr.eval, filterSlope, QRat.eval, QRat.one, env, t,
              TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using he.symm
          change TF.sub (state (k+1) 0) ((PExpr.add (.var 2) (.mul (.const ⟨1,10000000000,by decide⟩) filterSlope)).eval TF env) = TF.zero
          rw [hv, TF.sub_self]
        exact False.elim (checkConcreteLeaf_sound TF filterStepConstraints 0 filterStepBox env filterStepReplay hm hc)
  obtain ⟨k, hk, hu⟩ := hu
  have h := TF.le_trans _ _ _ hu (guard k hk)
  rw [TF.one_eq_ofRat] at h
  have hn := (TF.ofRat_le_iff 11 1 10 1 (by decide) (by decide)).mp h
  contradiction

-- BEGIN GENERATED PCB BRIDGE
/-- Full continuous manufacturing-box proof by checked forward bounds and paving. -/
theorem bench09a_pcb_microstrip_dfm_proved {R : Type} (TF : TranscendentalField R) :
    Bench_09a_pcb_microstrip_dfm_unsat TF := by
  intro dw_etch ds_etch dh_lam t_cu er_lam v_tx i_Vdrv v_tx_p i_Vdp v_tx_n i_Vdn v_rx thickness_log_tl50 su_tl50 eeff_tl50 seeff_tl50 lnz_tl50 Z0_tl50 wide_log_tl50 Ltot_tl50 Ctot_tl50 Rdc_tl50 v_rx_p v_rx_n thickness_log_diff90_p su_diff90_p eeff_diff90_p seeff_diff90_p lnz_diff90_p Z0_diff90_p wide_log_diff90_p Ltot_diff90_p Ctot_diff90_p Rdc_diff90_p thickness_log_diff90_n su_diff90_n eeff_diff90_n seeff_diff90_n lnz_diff90_n Z0_diff90_n wide_log_diff90_n Ltot_diff90_n Ctot_diff90_n Rdc_diff90_n kc_diff90 Zdiff_diff90 odd_factor_diff90 Cm_diff90 Lm_diff90 hb hp hu
  rcases hp with ⟨⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩, ⟨h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩⟩, ⟨⟨h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46⟩, ⟨h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62⟩⟩⟩
  let env : Nat → R := fun i => ([dw_etch, ds_etch, dh_lam, t_cu, er_lam, thickness_log_tl50, su_tl50, eeff_tl50, seeff_tl50, wide_log_tl50, Z0_tl50, thickness_log_diff90_n, su_diff90_n, eeff_diff90_n, seeff_diff90_n, wide_log_diff90_n, Z0_diff90_n, thickness_log_diff90_p, su_diff90_p, eeff_diff90_p, seeff_diff90_p, wide_log_diff90_p, Z0_diff90_p, kc_diff90, odd_factor_diff90, Zdiff_diff90] : List R).getD i TF.zero
  have hd : holdsDefinitions TF env 5 pcbDefinitions := by
    change (PDefinition.holds TF env 5 ⟨.logarithm, (.div (.mul (.const ⟨2, 1, by decide⟩) (.add (.const ⟨1, 10000, by decide⟩) (.var 2))) (.var 3))⟩) ∧ (PDefinition.holds TF env 6 ⟨.squareRoot, (.add (.const ⟨1, 1, by decide⟩) (.div (.const ⟨12, 1, by decide⟩) (.div (.add (.add (.const ⟨9, 50000, by decide⟩) (.var 0)) (.mul (.div (.var 3) (.const ⟨3141592653589793, 1000000000000000, by decide⟩)) (.add (.const ⟨1, 1, by decide⟩) (.var 5)))) (.add (.const ⟨1, 10000, by decide⟩) (.var 2)))))⟩) ∧ (PDefinition.holds TF env 7 ⟨.direct, (.add (.div (.add (.var 4) (.const ⟨1, 1, by decide⟩)) (.const ⟨2, 1, by decide⟩)) (.div (.sub (.var 4) (.const ⟨1, 1, by decide⟩)) (.mul (.const ⟨2, 1, by decide⟩) (.var 6))))⟩) ∧ (PDefinition.holds TF env 8 ⟨.squareRoot, (.var 7)⟩) ∧ (PDefinition.holds TF env 9 ⟨.logarithm, (.add (.div (.add (.add (.const ⟨9, 50000, by decide⟩) (.var 0)) (.mul (.div (.var 3) (.const ⟨3141592653589793, 1000000000000000, by decide⟩)) (.add (.const ⟨1, 1, by decide⟩) (.var 5)))) (.add (.const ⟨1, 10000, by decide⟩) (.var 2))) (.const ⟨361, 250, by decide⟩))⟩) ∧ (PDefinition.holds TF env 10 ⟨.direct, (.div (.const ⟨7539822368615503, 20000000000000, by decide⟩) (.mul (.var 8) (.add (.add (.div (.add (.add (.const ⟨9, 50000, by decide⟩) (.var 0)) (.mul (.div (.var 3) (.const ⟨3141592653589793, 1000000000000000, by decide⟩)) (.add (.const ⟨1, 1, by decide⟩) (.var 5)))) (.add (.const ⟨1, 10000, by decide⟩) (.var 2))) (.const ⟨1393, 1000, by decide⟩)) (.mul (.const ⟨667, 1000, by decide⟩) (.var 9)))))⟩) ∧ (PDefinition.holds TF env 11 ⟨.logarithm, (.div (.mul (.const ⟨2, 1, by decide⟩) (.add (.const ⟨1, 10000, by decide⟩) (.var 2))) (.var 3))⟩) ∧ (PDefinition.holds TF env 12 ⟨.squareRoot, (.add (.const ⟨1, 1, by decide⟩) (.div (.const ⟨12, 1, by decide⟩) (.div (.add (.add (.const ⟨17, 100000, by decide⟩) (.var 0)) (.mul (.div (.var 3) (.const ⟨3141592653589793, 1000000000000000, by decide⟩)) (.add (.const ⟨1, 1, by decide⟩) (.var 11)))) (.add (.const ⟨1, 10000, by decide⟩) (.var 2)))))⟩) ∧ (PDefinition.holds TF env 13 ⟨.direct, (.add (.div (.add (.var 4) (.const ⟨1, 1, by decide⟩)) (.const ⟨2, 1, by decide⟩)) (.div (.sub (.var 4) (.const ⟨1, 1, by decide⟩)) (.mul (.const ⟨2, 1, by decide⟩) (.var 12))))⟩) ∧ (PDefinition.holds TF env 14 ⟨.squareRoot, (.var 13)⟩) ∧ (PDefinition.holds TF env 15 ⟨.logarithm, (.add (.div (.add (.add (.const ⟨17, 100000, by decide⟩) (.var 0)) (.mul (.div (.var 3) (.const ⟨3141592653589793, 1000000000000000, by decide⟩)) (.add (.const ⟨1, 1, by decide⟩) (.var 11)))) (.add (.const ⟨1, 10000, by decide⟩) (.var 2))) (.const ⟨361, 250, by decide⟩))⟩) ∧ (PDefinition.holds TF env 16 ⟨.direct, (.div (.const ⟨7539822368615503, 20000000000000, by decide⟩) (.mul (.var 14) (.add (.add (.div (.add (.add (.const ⟨17, 100000, by decide⟩) (.var 0)) (.mul (.div (.var 3) (.const ⟨3141592653589793, 1000000000000000, by decide⟩)) (.add (.const ⟨1, 1, by decide⟩) (.var 11)))) (.add (.const ⟨1, 10000, by decide⟩) (.var 2))) (.const ⟨1393, 1000, by decide⟩)) (.mul (.const ⟨667, 1000, by decide⟩) (.var 15)))))⟩) ∧ (PDefinition.holds TF env 17 ⟨.logarithm, (.div (.mul (.const ⟨2, 1, by decide⟩) (.add (.const ⟨1, 10000, by decide⟩) (.var 2))) (.var 3))⟩) ∧ (PDefinition.holds TF env 18 ⟨.squareRoot, (.add (.const ⟨1, 1, by decide⟩) (.div (.const ⟨12, 1, by decide⟩) (.div (.add (.add (.const ⟨17, 100000, by decide⟩) (.var 0)) (.mul (.div (.var 3) (.const ⟨3141592653589793, 1000000000000000, by decide⟩)) (.add (.const ⟨1, 1, by decide⟩) (.var 17)))) (.add (.const ⟨1, 10000, by decide⟩) (.var 2)))))⟩) ∧ (PDefinition.holds TF env 19 ⟨.direct, (.add (.div (.add (.var 4) (.const ⟨1, 1, by decide⟩)) (.const ⟨2, 1, by decide⟩)) (.div (.sub (.var 4) (.const ⟨1, 1, by decide⟩)) (.mul (.const ⟨2, 1, by decide⟩) (.var 18))))⟩) ∧ (PDefinition.holds TF env 20 ⟨.squareRoot, (.var 19)⟩) ∧ (PDefinition.holds TF env 21 ⟨.logarithm, (.add (.div (.add (.add (.const ⟨17, 100000, by decide⟩) (.var 0)) (.mul (.div (.var 3) (.const ⟨3141592653589793, 1000000000000000, by decide⟩)) (.add (.const ⟨1, 1, by decide⟩) (.var 17)))) (.add (.const ⟨1, 10000, by decide⟩) (.var 2))) (.const ⟨361, 250, by decide⟩))⟩) ∧ (PDefinition.holds TF env 22 ⟨.direct, (.div (.const ⟨7539822368615503, 20000000000000, by decide⟩) (.mul (.var 20) (.add (.add (.div (.add (.add (.const ⟨17, 100000, by decide⟩) (.var 0)) (.mul (.div (.var 3) (.const ⟨3141592653589793, 1000000000000000, by decide⟩)) (.add (.const ⟨1, 1, by decide⟩) (.var 17)))) (.add (.const ⟨1, 10000, by decide⟩) (.var 2))) (.const ⟨1393, 1000, by decide⟩)) (.mul (.const ⟨667, 1000, by decide⟩) (.var 21)))))⟩) ∧ (PDefinition.holds TF env 23 ⟨.direct, (.exp (.neg (.div (.mul (.const ⟨19, 10, by decide⟩) (.add (.const ⟨9, 50000, by decide⟩) (.var 1))) (.add (.const ⟨1, 10000, by decide⟩) (.var 2)))))⟩) ∧ (PDefinition.holds TF env 24 ⟨.squareRoot, (.div (.sub (.const ⟨1, 1, by decide⟩) (.var 23)) (.add (.const ⟨1, 1, by decide⟩) (.var 23)))⟩) ∧ (PDefinition.holds TF env 25 ⟨.direct, (.mul (.add (.var 22) (.var 16)) (.var 24))⟩) ∧ True
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (h7)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (And.intro h8 h9)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (h10)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (And.intro h11 h12)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (h14)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (h15)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (h39)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (And.intro h40 h41)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (h42)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (And.intro h43 h44)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (h46)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (h47)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (h23)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (And.intro h24 h25)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (h26)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (And.intro h27 h28)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (h30)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (h31)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (h51)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (And.intro h52 h53)
    · simpa only [PDefinition.holds, PExpr.eval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, TF.zero_eq_ofRat, TF.one_eq_ofRat, TF.ofInt_eq_ofRat] using (h54)
  have hm : memBox TF pcbRoot env := by
    rcases hb with ⟨p0, p1, p2, p3, p4, _⟩
    simpa only [memBox, pcbRoot, memInterval, QRat.eval, env, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] using (And.intro p0 (And.intro p1 (And.intro p2 (And.intro p3 (And.intro p4 True.intro)))))
  have hn : ¬ holdsRanges TF env pcbRanges := by
    intro hr
    change (TF.le (TF.ofRat 45 1) Z0_tl50 ∧ TF.le Z0_tl50 (TF.ofRat 55 1)) ∧ (TF.le (TF.ofRat 90 1) Zdiff_diff90 ∧ TF.le Zdiff_diff90 (TF.ofRat 110 1)) ∧ True at hr
    simp only [TF.ofInt_eq_ofRat] at hu
    rcases hu with h | h | h | h
    · exact ((TF.lt_iff_le_not_le _ _).mp h).2 hr.1.1
    · exact ((TF.lt_iff_le_not_le _ _).mp h).2 hr.1.2
    · exact ((TF.lt_iff_le_not_le _ _).mp h).2 hr.2.1.1
    · exact ((TF.lt_iff_le_not_le _ _).mp h).2 hr.2.1.2
  exact paving_unsat_sound TF (fun env => holdsDefinitions TF env 5 pcbDefinitions ∧ ¬ holdsRanges TF env pcbRanges)
    (checkForwardLeaf 5 pcbDefinitions pcbRanges pcbCertificates)
    (checkForwardLeaf_sound TF 5 pcbDefinitions pcbRanges pcbCertificates)
    pcbTree pcbRoot env pcbReplay hm ⟨hd, hn⟩
-- END GENERATED PCB BRIDGE




private noncomputable abbrev body (d : ℝ) := 13/2+d
private noncomputable abbrev qmShift (d : ℝ) :=
  4178112912843729/5000000000000000 * (1/(body d*body d) - 23668639053254437/1000000000000000000)
private noncomputable abbrev aspect (d : ℝ) := (64+body d)/21
private noncomputable abbrev dibl (k l : ℝ) := k * Real.exp (-(21/(2*l)))

private theorem fin_shift_range {d : ℝ} (hd : -9/20 ≤ d ∧ d ≤ 9/20) :
    -1/200 ≤ qmShift d ∧ qmShift d ≤ 1/200 := by
  have hl : 6 ≤ body d := by dsimp [body]; linarith
  have hu : body d ≤ 7 := by dsimp [body]; linarith
  have hb : 0 < body d := by linarith
  have ha := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 6) hl
  have hh := mul_self_le_mul_self hb.le hu
  have h1 := one_div_le_one_div_of_le (by positivity : 0 < body d*body d) hh
  have h2 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 6*6) ha
  dsimp [qmShift]; constructor <;> linarith

private theorem softplus_range {y z : ℝ} (h : Real.exp y = 1+Real.exp z) :
    z ≤ y ∧ y ≤ max 0 z + 1 := by
  constructor
  · apply Real.exp_le_exp.mp; rw [h]; linarith
  · apply Real.exp_le_exp.mp
    rw [h,Real.exp_add]
    have ha := Real.exp_le_exp.mpr (le_max_right 0 z)
    have hb := Real.exp_le_exp.mpr (le_max_left 0 z)
    rw [Real.exp_zero] at hb
    nlinarith only [ha,hb,mul_le_mul_of_nonneg_left Real.exp_one_gt_two.le (Real.exp_pos (max 0 z)).le]

set_option maxHeartbeats 900000 in
/-- The pull-up has enough drain voltage and overdrive to exceed the residual
pull-down current even at the smallest aspect ratio in the 7 nm etch box. -/
theorem bench02_asap7_inverter_snm_proved : Bench_02_asap7_finfet_inverter_snm realTF := by
  intro vdd vi d dl t sup iv vin ii vo lp pf pr ip ln nf nr inn box phys unsafeV
  dsimp only [realTF] at box phys unsafeV
  push_cast at box phys unsafeV
  obtain ⟨_,_,hd,hl,ht,hs,hv,ho⟩ := box
  simp only [and_assoc] at phys
  obtain ⟨_,_,_,htv,_,_,_,_,hpf0,hpf,hpr0,hpr,hip,_,_,_,_,hln0,hln,hnf0,hnf,_,_,hin,_,kcl,_⟩ := phys
  let L := (1000000000:ℝ)*((21+dl)*(1/1000000000))
  let D := 2*(4308666631/50000000000000*t)
  let A := 2*((64+body d)/L)
  let ep := 17/5 * Real.exp (-(L/(2*lp)))
  let en := 16/5 * Real.exp (-(L/(2*ln)))
  let p := 17/20 * ((sup-vin)-(7/25 + (-17/20000)*(t-300) + qmShift d - ep*(sup-vo)))
  let n := 43/50 * (vin-(27/100 + (-17/20000)*(t-300) + qmShift d - en*vo))
  change Real.exp pf = 1+Real.exp (p/D) at hpf
  change Real.exp pr = 1+Real.exp ((p-(sup-vo))/D) at hpr
  change Real.exp nf = 1+Real.exp (n/D) at hnf
  change ip = -((13/50000000*A)*(pf*pf-pr*pr)/(1+1/10*pf)) at hip
  change inn = (3/10000000*A)*(nf*nf-nr*nr)/(1+1/10*nf) at hin
  have hL : 20 ≤ L := by dsimp [L]; linarith only [hl.1]
  have hA : 0 < A := by dsimp [A,body]; positivity
  have hD : 0 < D := by dsimp [D]; linarith only [htv]
  have hDu : D ≤ 63/1000 := by dsimp [D]; linarith only [ht.2]
  have he0 : 0 ≤ ep := by dsimp [ep]; positivity
  have hln : 0 < ln ∧ ln ≤ 8/3 := by constructor <;> nlinarith [hd.1,hd.2]
  have harg : 3+3/4 ≤ L/(2*ln) := (le_div_iff₀ (by linarith)).2 (by linarith)
  have he3 : (27/10:ℝ)^3 ≤ Real.exp 3 := by
    rw [show (3:ℝ) = (3:ℕ)*1 by norm_num,Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
  have he := Real.exp_le_exp.mpr harg
  rw [Real.exp_add] at he
  have hx : 32 ≤ Real.exp (L/(2*ln)) := by
    nlinarith only [he,mul_le_mul he3 (Real.add_one_le_exp (3/4)) (by norm_num) (Real.exp_pos _).le]
  have henu : en ≤ 1/10 := by
    dsimp [en]; rw [Real.exp_neg,← div_eq_mul_inv]; exact (div_le_iff₀ (Real.exp_pos _)).2 (by linarith)
  have hevo : en*vo ≤ 27/500 := (mul_le_mul henu unsafeV.le ho.1 (by norm_num)).trans_eq (by norm_num)
  obtain ⟨hsl,hsu⟩ := fin_shift_range hd
  have hn : n/D ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by dsimp [n]; linarith only [hv.2,hevo,ht.2,hsl]) hD.le
  have hnf1 := (softplus_range hnf).2
  rw [max_eq_left hn] at hnf1
  have vdrop : 11/100 ≤ sup-vo := by linarith only [hs.1,unsafeV]
  have hp : 5/2 ≤ p/D := (le_div_iff₀ hD).2 (by
    dsimp [p]; linarith only [hs.1,hv.2,ht.1,hsu,hDu,mul_nonneg he0 (by linarith : 0 ≤ sup-vo)])
  have hdrop : 17/10 ≤ (sup-vo)/D := (le_div_iff₀ hD).2 (by linarith)
  have pfmin := hp.trans (softplus_range hpf).1
  have prmax := (softplus_range hpr).2
  have gap : 7/10 ≤ pf-pr := by
    rcases le_total ((p-(sup-vo))/D) 0 with hz | hz
    · rw [max_eq_left hz] at prmax; linarith
    · rw [max_eq_right hz,sub_div] at prmax
      linarith only [prmax,hdrop,(softplus_range hpf).1]
  have del : 7/10*pf ≤ pf*pf-pr*pr := by
    nlinarith only [mul_le_mul_of_nonneg_right gap hpf0,mul_nonneg (by linarith : 0 ≤ pf-pr) hpr0]
  have hn1 : nf*nf-nr*nr ≤ 1 := by nlinarith only [mul_self_le_mul_self hnf0 hnf1,sq_nonneg nr]
  have pden : 0 < 1+1/10*pf := by positivity
  have nden : 0 < 1+1/10*nf := by positivity
  have driveP : (3/10000000)*A < -ip := by
    rw [hip,neg_neg]; apply (lt_div_iff₀ pden).2
    have : 3/10000000*(1+1/10*pf) < 13/50000000*(pf*pf-pr*pr) := by linarith only [del,pfmin]
    nlinarith only [mul_lt_mul_of_pos_right this hA]
  have driveN : inn ≤ (3/10000000)*A := by
    rw [hin]; apply (div_le_iff₀ nden).2
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith only [hn1,hnf0]
  linarith only [driveP,driveN,kcl]

private theorem qmShift_bounds {d : ℝ} (hd : -7/20 ≤ d ∧ d ≤ 7/20) :
    -3/1000 ≤ qmShift d ∧ qmShift d ≤ 3/1000 := by
  have hl : 123/20 ≤ body d := by dsimp [body]; linarith
  have hu : body d ≤ 137/20 := by dsimp [body]; linarith
  have hb : 0 < body d := by linarith
  have hl' := mul_self_le_mul_self (by norm_num : 0 ≤ (123/20:ℝ)) hl
  have hu' := mul_self_le_mul_self hb.le hu
  have h1 : 1/(137/20*(137/20):ℝ) ≤ 1/(body d*body d) :=
    one_div_le_one_div_of_le (by positivity) hu'
  have h2 : 1/(body d*body d) ≤ 1/(123/20*(123/20):ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hl'
  dsimp [qmShift]; constructor <;> linarith

private theorem dibl_bounds {l z k : ℝ} (hl : 0 ≤ l) (hs : l*l = z)
    (hz : 123/20 ≤ z ∧ z ≤ 137/20) (hk : 3 ≤ k ∧ k ≤ 16/5) :
    4/100 ≤ dibl k l ∧ dibl k l ≤ 7/100 := by
  have hlo : 42/17 ≤ l := by nlinarith
  have hhi : l ≤ 21/8 := by nlinarith
  have hd : 0 < 2*l := by linarith
  have hl4 : 4 ≤ 21/(2*l) := (le_div_iff₀ hd).2 (by linarith)
  have hh4 : 21/(2*l) ≤ 17/4 := (div_le_iff₀ hd).2 (by linarith)
  have hpow : Real.exp (17/4) ^ 4 = Real.exp 1 ^ 17 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h17 := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_d9.le 17
  have hx : Real.exp (17/4) ≤ 75 := by
    by_contra! hn
    have hlt := pow_lt_pow_left₀ hn (by norm_num) (by decide : 4 ≠ 0)
    rw [hpow] at hlt; linarith
  have hy : (50:ℝ) ≤ Real.exp 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 4
    rw [← Real.exp_nat_mul] at h; norm_num at h ⊢; linarith
  have hE := Real.exp_pos (21/(2*l))
  have hub := (Real.exp_le_exp.mpr hh4).trans hx
  have hlb := hy.trans (Real.exp_le_exp.mpr hl4)
  rw [dibl, Real.exp_neg, ← div_eq_mul_inv]
  exact ⟨(le_div_iff₀ hE).2 (by linarith), (div_le_iff₀ hE).2 (by linarith)⟩

set_option maxRecDepth 6000 in
theorem bench03a_asap7_sram_read_margin_proved : Bench_03a_asap7_sram_6t_fin_etch_unsat realTF := by
  intro d db phi lpa lda lga lpb ldb lgb state _sampleTime dx box phys
  obtain ⟨hd, hdb, hphi, hbox⟩ := box
  -- Keep the two implicit step equations folded while extracting static geometry.
  obtain ⟨⟨_, _, _, hpa, hpa2, _, _, _, hda, hda2, _, _, _, hga, hga2, _⟩,
    _, _, hpb, hpb2, _, _, _, hdb₀, hdb2, _, _, _, hgb, hgb2, init, steps⟩ := phys
  dsimp only [realTF] at hd hdb hphi
  push_cast at hd hdb hphi
  have bz (x : ℝ) (h : -7/20 ≤ x ∧ x ≤ 7/20) : 123/20 ≤ body x ∧ body x ≤ 137/20 := by
    dsimp [body]; constructor <;> linarith
  have bz0 : 123/20 ≤ (13/2:ℝ) ∧ (13/2:ℝ) ≤ 137/20 := by norm_num
  have puA := dibl_bounds hpa hpa2 (bz d hd) (k := 16/5) (by norm_num)
  have puB := dibl_bounds hpb hpb2 (bz d hd) (k := 16/5) (by norm_num)
  have pdA := dibl_bounds hda hda2 (bz d hd) (k := 3) (by norm_num)
  have pdB := dibl_bounds hdb₀ hdb2 (bz db hdb) (k := 3) (by norm_num)
  have pgA := dibl_bounds hga hga2 bz0 (k := 3) (by norm_num)
  have pgB := dibl_bounds hgb hgb2 bz0 (k := 3) (by norm_num)
  let env (k i : Nat) : ℝ := ([state k 0, state k 1, 33/100+qmShift d, dibl (16/5) lpa,
    dibl (16/5) lpb, 13/50000000*aspect d, 8/25+qmShift d, 8/25+phi+qmShift db,
    dibl 3 lda, dibl 3 ldb, 3/10000000*(2*aspect d), 3/10000000*(2*aspect db),
    dibl 3 lga, dibl 3 lgb] : List ℝ).getD i 0
  have mem (k : Nat) (hk : k ≤ 20) : memBox realTF SramCertificate.rootBox (env k) := by
    obtain ⟨h0,h1⟩ := hbox k hk
    dsimp only [realTF] at h0 h1
    push_cast at h0 h1
    have hq := qmShift_bounds hd
    have hb := qmShift_bounds hdb
    simp [memBox, memInterval, SramCertificate.rootBox, SramCertificate.range, realTF, QRat.eval, env,
      aspect, body]
    repeat' apply And.intro
    all_goals linarith only [h0.1,h0.2,h1.1,h1.2,hq.1,hq.2,hb.1,hb.2,hd.1,hd.2,hdb.1,hdb.2,
      hphi.1,hphi.2,puA.1,puA.2,puB.1,puB.2,pdA.1,pdA.2,pdB.1,pdB.2,pgA.1,pgA.2,pgB.1,pgB.2]
  have inv (k : Nat) (hk : k ≤ 20) : 29/50 ≤ state k 0 ∧ state k 1 ≤ 1/5 := by
    induction k with
    | zero =>
      obtain ⟨h0,h1⟩ := init
      change state 0 0 = 7/10 at h0
      change state 0 1 = 0 at h1
      rw [h0,h1]; norm_num
    | succ k ih =>
      obtain ⟨q0,b0⟩ := ih (by omega)
      obtain ⟨hq,hb⟩ := steps k (by omega)
      have hprev (side : Bool) : (SramCertificate.previous side).eval realTF (env (k+1)) =
          state k (if side then 1 else 0) := by
        cases side
        · apply sub_eq_iff_eq_add.mpr
          simpa [SramCertificate.previous, SramCertificate.drive, SramCertificate.c, PExpr.eval,
            realTF, QRat.eval, env, qmShift, aspect, body, dibl, dx] using hq
        · apply sub_eq_iff_eq_add.mpr
          simpa [SramCertificate.previous, SramCertificate.drive, SramCertificate.c, PExpr.eval,
            realTF, QRat.eval, env, qmShift, aspect, body, dibl, dx] using hb
      exact SramCertificate.invariantStep (env (k+1)) (mem _ hk)
        (by rwa [hprev]) (by rwa [hprev])
  rintro ⟨k,hk,hbad⟩
  obtain ⟨hq,hb⟩ := inv k hk
  change state k 0 - state k 1 < 3/25 at hbad
  linarith

private noncomputable abbrev thermal (t : ℝ) := 4308666631 / 50000000000000 * t
private noncomputable abbrev gain (t : ℝ) := (t/300 * (t/300) * (t/300)) *
  Real.exp (270772089507397/6250000000000 - (28/25)/thermal t)
private noncomputable abbrev junction (k t v : ℝ) := k * gain t * (Real.exp (v/thermal t) - 1)

/-- Uniform reverse-current floor and forward-current ceiling below 400 mV.
Combining the temperature and bias exponents retains their shared thermal voltage. -/
private theorem junctionBounds (k t v : ℝ) (hk : 0 ≤ k) (hk' : k ≤ 1/2000000000000000)
    (ht : 273 ≤ t) (ht' : t ≤ 398) :
    -(1/1000000000) ≤ junction k t v ∧
    (v ≤ 2/5 → junction k t v ≤ 1/5000) := by
  let d := thermal t
  let c := k * (t/300 * (t/300) * (t/300))
  have hd : 0 < d := by dsimp [d,thermal]; linarith
  have hd' : d ≤ 343/10000 := by dsimp [d,thermal]; linarith
  have ht₀ : 0 ≤ t/300 := by linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc' : c ≤ 3/2000000000000000 := by
    have ht3 : (t/300)^3 ≤ (4/3 : ℝ)^3 := pow_le_pow_left₀ ht₀ (by linarith) _
    have := mul_le_mul hk' (show t/300*(t/300)*(t/300) ≤ 3 by nlinarith) (by positivity) (by norm_num)
    exact this.trans_eq (by ring)
  let b : ℝ := 270772089507397/6250000000000 - (28/25)/d
  have expBound (u : ℝ) (n : ℕ) (h : u ≤ n) : Real.exp u ≤ (3 : ℝ)^n := by
    calc
      Real.exp u ≤ Real.exp (n*1) := Real.exp_le_exp.mpr (by simpa using h)
      _ = Real.exp 1 ^ n := Real.exp_nat_mul 1 n
      _ ≤ 3^n := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  have hb : b ≤ 11 := by
    have : (270772089507397/6250000000000 - 11) ≤ (28/25)/d :=
      (le_div_iff₀ hd).2 (by linarith)
    dsimp [b]; linarith
  have hbase := mul_le_mul hc' (expBound b 11 (by exact_mod_cast hb)) (Real.exp_pos _).le (by norm_num)
  have id : junction k t v = c * Real.exp (b+v/d) - c*Real.exp b := by
    rw [Real.exp_add]; dsimp [c,b,d,junction,gain]; ring
  rw [id]
  constructor
  · linarith [mul_nonneg hc (Real.exp_pos (b+v/d)).le]
  · intro hv
    have hbv : b+v/d ≤ 23 := by
      have h : (v-28/25)/d ≤ 23-270772089507397/6250000000000 :=
        (div_le_iff₀ hd).2 (by linarith)
      dsimp [b]; linarith [sub_div v (28/25) d]
    have := mul_le_mul hc' (expBound _ 23 (by exact_mod_cast hbv)) (Real.exp_pos _).le (by norm_num)
    linarith [mul_nonneg hc (Real.exp_pos b).le]

private theorem resistorBounds (v r lo hi : ℝ) (hr : 0 < r) (hl : lo ≤ r) (hh : r ≤ hi) :
    (lo*(v/r) ≤ v ∧ v ≤ hi*(v/r)) ∨ (hi*(v/r) ≤ v ∧ v ≤ lo*(v/r)) := by
  have h : r*(v/r) = v := by field_simp
  rcases le_total 0 (v/r) with hp | hn
  · exact Or.inl ⟨(mul_le_mul_of_nonneg_right hl hp).trans_eq h, h.symm.trans_le (mul_le_mul_of_nonneg_right hh hp)⟩
  · exact Or.inr ⟨(mul_le_mul_of_nonpos_right hh hn).trans_eq h, h.symm.trans_le (mul_le_mul_of_nonpos_right hl hn)⟩

/-- The two tapped base nodes and the 20 Ω emitter ballast exclude the 5 mA
holding branch throughout the stamped temperature and supply boxes. -/
theorem bench05_cmos_scr_latchup_holding_proved : Bench_05_cmos_scr_latchup_holding realTF := by
  intro vs rw rs t sup iv nw ps ep en cp bp cn bn box phys unsafeH
  dsimp only [realTF] at box phys unsafeH
  push_cast at box phys unsafeH
  obtain ⟨_, ⟨hrw, hrw'⟩, ⟨hrs, hrs'⟩, ⟨ht, ht'⟩, ⟨_,hs⟩, hn, hp, hep, hen⟩ := box
  obtain ⟨_, hcp, hbp, hcn, hbn, he, hf, hw, hb, hi⟩ := phys
  let kp : ℝ := 9/25000000000000000
  let kn : ℝ := 1/2000000000000000
  let a := junction kp t (ep-nw)
  let b := junction kn t (ps-en)
  let c := junction kp t (ps-nw)
  let d := junction kn t (ps-nw)
  change cp = -((a-c)-c/2) at hcp
  change bp = -(a/18+c/2) at hbp
  change cn = (b-d)-d/2 at hcn
  change bn = b/45+d/2 at hbn
  obtain ⟨ha, hfa⟩ := junctionBounds kp t (ep-nw) (by norm_num [kp]) (by norm_num [kp]) ht ht'
  obtain ⟨hbb, hfb⟩ := junctionBounds kn t (ps-en) (by norm_num [kn]) (by norm_num [kn]) ht ht'
  obtain ⟨hc, hfc⟩ := junctionBounds kp t (ps-nw) (by norm_num [kp]) (by norm_num [kp]) ht ht'
  obtain ⟨hd, hfd⟩ := junctionBounds kn t (ps-nw) (by norm_num [kn]) (by norm_num [kn]) ht ht'
  change _ ≤ a at ha; change _ → a ≤ _ at hfa
  change _ ≤ b at hbb; change _ → b ≤ _ at hfb
  change _ ≤ c at hc; change _ → c ≤ _ at hfc
  change _ ≤ d at hd; change _ → d ≤ _ at hfd
  have hwell := resistorBounds (sup-nw) rw 6 14 (by linarith) hrw hrw'
  have hsub := resistorBounds ps rs 5 12 (by linarith) hrs hrs'
  generalize (sup-nw)/rw = jw at *
  generalize ps/rs = js at *
  -- Each reverse-biased junction is bounded below independently of voltage.
  -- Above 400 mV only the resistive and current-balance constraints are needed.
  rcases le_or_gt (ep-nw) (2/5) with h | h
  all_goals try specialize hfa h
  all_goals rcases le_or_gt (ps-en) (2/5) with h | h
  all_goals try specialize hfb h
  all_goals rcases le_or_gt (ps-nw) (2/5) with h | h
  all_goals try specialize hfc h
  all_goals try specialize hfd h
  all_goals rcases hwell with ⟨_,_⟩ | ⟨_,_⟩ <;> rcases hsub with ⟨_,_⟩ | ⟨_,_⟩ <;> linarith

/-- An over-etched 138 μm trace on 118 μm laminate exceeds 56 Ω. The
logarithms, square roots and DC solution below are exact real witnesses. -/
theorem bench09b_pcb_microstrip_overetch_proved : Bench_09b_pcb_microstrip_overetch_sat realTF := by
  let t : ℝ := 7 / 250000
  let w : ℝ := 69 / 500000
  let h : ℝ := 59 / 500000
  let piDeck : ℝ := 3141592653589793 / 1000000000000000
  let l := Real.log (2*h/t)
  let u := (w + t/piDeck * (1+l))/h
  let s := Real.sqrt (1+12/u)
  let e := (77/20+1)/2 + (77/20-1)/(2*s)
  let a := Real.sqrt e
  let g := Real.log (u+361/250)
  let z := (7539822368615503/20000000000000)/(a*(u+1393/1000+667/1000*g))
  let r := (1/20)/(58000000*(w*t))
  let rx := 50/(r+50)
  have hl0 : 0 ≤ l := Real.log_nonneg (by norm_num [h,t])
  have hl3 : l ≤ 3 := by
    apply (Real.log_le_iff_le_exp (by norm_num [h,t])).2
    have he := Real.add_one_le_exp (1/2)
    have hid : Real.exp 3 = Real.exp (1/2) ^ 6 := by
      convert Real.exp_nat_mul (1/2) 6 using 1; norm_num
    rw [hid]
    exact le_trans (by norm_num [h,t] : 2*h/t ≤ (1/2+1 : ℝ)^6) (pow_le_pow_left₀ (by norm_num) he _)
  have hu : 1 ≤ u ∧ u ≤ 3/2 := by dsimp [u,w,h,t,piDeck]; constructor <;> linarith
  have hs2 := Real.sq_sqrt (show 0 ≤ 1+12/u by positivity)
  have hs : 3 ≤ s := by
    have : 8 ≤ 12/u := (le_div_iff₀ (by linarith : 0 < u)).2 (by linarith)
    dsimp [s]; nlinarith [Real.sqrt_nonneg (1+12/u)]
  have he : 0 < e ∧ e ≤ 3 := by
    dsimp [e]
    constructor
    · positivity
    · have : (77/20-1)/(2*s) ≤ (3/1 - (77/20+1)/2 : ℝ) := by
        apply (div_le_iff₀ (by positivity)).2; linarith
      linarith
  have ha : 0 < a ∧ a ≤ 7/4 := by
    exact ⟨Real.sqrt_pos.2 he.1, (Real.sqrt_le_iff).2 ⟨by norm_num, by linarith⟩⟩
  have hg0 : 0 ≤ g := Real.log_nonneg (by linarith)
  have hg : g ≤ 5/4 := by
    apply (Real.log_le_iff_le_exp (by linarith)).2
    have hstep := Real.add_one_le_exp (1/8)
    have hid : Real.exp (5/4) = Real.exp (1/8)^10 := by
      convert Real.exp_nat_mul (1/8) 10 using 1; norm_num
    rw [hid]
    exact le_trans (by linarith : u + 361/250 ≤ (1/8+1 : ℝ)^10)
      (pow_le_pow_left₀ (by norm_num) hstep _)
  have hscale : 0 < u+1393/1000+667/1000*g := by linarith
  have hz : 56 < z := by
    apply (lt_div_iff₀ (mul_pos ha.1 hscale)).2
    have bound := mul_le_mul ha.2 (show u+1393/1000+667/1000*g ≤ 3/2+1393/1000+667/1000*(5/4) by linarith)
      hscale.le (by norm_num)
    linarith
  have hr : r = 3125/14007 := by norm_num [r,w,t]
  refine ⟨-21/500000, 9/500000, t, 77/20, 1, -(1-rx)/r, rx, l, s, e, a,
    Real.log (8/u+u/4), z, g, (1/20)*(z*a)/299792458,
    ((1/20)*a/299792458)/z, r, ?_⟩
  dsimp only [realTF]
  push_cast
  have hw : (9/50000 : ℝ) + -21/500000 = w := by norm_num [w]
  have hh : (1/10000 : ℝ) + 9/500000 = h := by norm_num [h]
  simp only [hw, hh]
  repeat' constructor
  all_goals first
    | exact hz
    | exact Real.sqrt_nonneg _
    | exact Real.exp_log (by positivity)
    | exact Real.mul_self_sqrt (by positivity)
    | exact div_mul_cancel₀ _ (by linarith : z ≠ 0)
    | rfl
    | norm_num [rx, hr, r, t, w, h]

private noncomputable abbrev sigeJunction (scale t offset bias : ℝ) :=
  scale * ((t/300 * (t/300) * (t/300)) *
    Real.exp (270772089507397/6250000000000 - (28/25-offset)/thermal t)) *
    (Real.exp (bias/thermal t) - 1)

/-- With a reference below 150 mV, every SiGe junction in its KCL sees at
most 250 mV forward bias. Combining the bandgap and bias exponents retains
their common temperature dependence. -/
private theorem sige_ceiling (k t g v : ℝ) (hk : 0 ≤ k) (ht : 273 ≤ t) (ht' : t ≤ 373)
    (hg : g ≤ 9/100) (hv : v ≤ 1/4) : sigeJunction k t g v ≤ k*1400000000 := by
  let d := thermal t
  let b := 270772089507397/6250000000000 - (28/25-g)/d
  let f := t/300 * (t/300) * (t/300)
  have hd : 0 < d := by dsimp [d,thermal]; linarith
  have hd' : d ≤ 322/10000 := by dsimp [d,thermal]; linarith
  have hf : 0 ≤ f := by dsimp [f]; positivity
  have hf' : f ≤ 2 := by
    have := pow_le_pow_left₀ (by linarith : 0 ≤ t/300) (by linarith : t/300 ≤ 5/4) 3
    dsimp [f]; nlinarith
  have hb : b+v/d ≤ 20 := by
    have h : (v-(28/25-g))/d ≤ 20-270772089507397/6250000000000 :=
      (div_le_iff₀ hd).2 (by linarith)
    dsimp [b]; linarith [sub_div v (28/25-g) d]
  have hex : Real.exp (b+v/d) ≤ 700000000 := by
    apply (Real.exp_le_exp.mpr hb).trans
    rw [show (20:ℝ) = (20:ℕ)*1 by norm_num,Real.exp_nat_mul]
    exact (pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 11/4) 20).trans (by norm_num)
  have hmul := mul_le_mul hf' hex (Real.exp_pos _).le (by norm_num)
  have id : sigeJunction k t g v = k * (f*Real.exp (b+v/d) - f*Real.exp b) := by
    rw [Real.exp_add]; dsimp [sigeJunction,b,d,f]; ring
  rw [id]
  apply mul_le_mul_of_nonneg_left _ hk
  linarith [mul_nonneg hf (Real.exp_pos b).le]

private theorem startup_floor (t v : ℝ) (ht : 273 ≤ t) (ht' : t ≤ 373) (hv : 3/10 ≤ v) :
    1/20000000 ≤ sigeJunction (1/10000000000) t 0 v := by
  let d := thermal t
  let b := 270772089507397/6250000000000 - (28/25)/d
  let f := t/300 * (t/300) * (t/300)
  have hd : 0 < d := by dsimp [d,thermal]; linarith
  have hd' : 235/10000 ≤ d := by dsimp [d,thermal]; linarith
  have hf : 3/4 ≤ f := by
    have := pow_le_pow_left₀ (by norm_num : 0 ≤ (91/100:ℝ)) (by linarith : 91/100 ≤ t/300) 3
    dsimp [f]; nlinarith
  have hb : 8 ≤ b+v/d := by
    have h : 8-270772089507397/6250000000000 ≤ (v-28/25)/d := (le_div_iff₀ hd).2 (by linarith)
    dsimp [b]; linarith [sub_div v (28/25) d]
  have hx : 2 ≤ Real.exp (v/d) := Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr
    ((le_div_iff₀ hd).2 (by dsimp [d,thermal]; linarith)))
  have he : (1500:ℝ) ≤ Real.exp (b+v/d) := by
    apply LE.le.trans _ (Real.exp_le_exp.mpr hb)
    rw [show (8:ℝ) = (8:ℕ)*1 by norm_num,Real.exp_nat_mul]
    exact (by norm_num : (1500:ℝ) ≤ (5/2)^8).trans
      (pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9] : 5/2 ≤ Real.exp 1) _)
  rw [Real.exp_add] at he
  have hh := mul_le_mul_of_nonneg_left (by linarith : Real.exp (v/d)/2 ≤ Real.exp (v/d)-1)
    (Real.exp_pos b).le
  have hi : 750 ≤ Real.exp b*(Real.exp (v/d)-1) := by linarith
  have := mul_le_mul hf hi (by norm_num) (by linarith)
  change _ ≤ (1/10000000000)*(f*Real.exp (270772089507397/6250000000000 - (28/25-0)/d))*(Real.exp (v/d)-1)
  rw [sub_zero]; change _ ≤ (1/10000000000)*(f*Real.exp b)*(Real.exp (v/d)-1)
  linarith only [this]

set_option maxHeartbeats 1600000 in
theorem bench04b_sige_bandgap_guarded_proved : Bench_04b_ihp_sige_bandgap_guarded_unsat realTF := by
  intro vdd t g sup iv ref vc f hfwdR mp f2 r2 mp2 e sk ic ib e2 sk2 ic2 ib2 vs ivs di box phys unsafeRef
  dsimp only [realTF] at box phys unsafeRef
  push_cast at box phys unsafeRef
  obtain ⟨hvd,ht,hg,_,href,hvc,he,he2,_⟩ := box
  simp only [and_assoc] at phys
  obtain ⟨hs,_,htv,hf0,hf,hr0,hr,hm,_,_,_,_,_,_,_,hsk0,hsk,hic,hib,_,_,_,hib2,hvs,hdi,_,kcl,_⟩ := phys
  let k1 : ℝ := 1/312500000000000000
  let k2 : ℝ := 1/39062500000000000
  let j := sigeJunction k1 t g (ref-e)
  let j2 := sigeJunction k2 t g (ref-e2)
  let jc := sigeJunction k2 t g (ref-vc)
  have jb := sige_ceiling k1 t g (ref-e) (by norm_num [k1]) ht.1 ht.2 hg.2 (by linarith [he.1])
  have j2b := sige_ceiling k2 t g (ref-e2) (by norm_num [k2]) ht.1 ht.2 hg.2 (by linarith [he2.1])
  have jcb := sige_ceiling k2 t g (ref-vc) (by norm_num [k2]) ht.1 ht.2 hg.2 (by linarith [hvc.1])
  change j ≤ _ at jb
  change j2 ≤ _ at j2b
  change jc ≤ _ at jcb
  have hstart := startup_floor t (vs-ref) ht.1 ht.2 (by linarith)
  simp only [sigeJunction,sub_zero] at hstart
  rw [← hdi] at hstart
  have hpm : mp ≤ 0 := by
    have er : hfwdR ≤ f := Real.exp_le_exp.mp (by
      rw [hr,hf]
      apply add_le_add_right
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith [hvd.1])
    nlinarith [mul_self_le_mul_self hr0 er]
  simp only [sub_self,zero_div,Real.exp_zero,sub_zero,mul_zero,add_zero] at hic hib hsk
  change ic = j/sk*(1+(ref-e)/45) at hic
  change ib = j/380 at hib
  change ib2 = j2/380 + jc/8 at hib2
  have hic' : ic ≤ 2*(k1*1400000000) := by
    have hp : 0 ≤ 1+(ref-e)/45 := by linarith [href.1,he.2]
    rcases le_total j 0 with hj | hj
    · have hi := mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hj hsk0) hp
      rw [hic]; exact hi.trans (by norm_num [k1])
    · have hs1 : 1 ≤ sk := by
        have hle : 1 ≤ sk*sk := by
          rw [hsk]
          change 1 ≤ 1 + j*j/(9/62500)
          linarith [mul_self_nonneg j]
        nlinarith
      have hj' : j/sk ≤ k1*1400000000 := (div_le_iff₀ (by linarith)).2
        (jb.trans (le_mul_of_one_le_right (by norm_num [k1]) hs1))
      rw [hic]
      exact (mul_le_mul hj' (by linarith [he.1] : 1+(ref-e)/45 ≤ 2) hp (by norm_num [k1])).trans_eq (mul_comm ..)
  dsimp [k1,k2] at hic' jb j2b jcb
  linarith only [hstart,hpm,hic',hib,hib2,jb,j2b,jcb,kcl,unsafeRef]

/-- A damaged pull-down fin admits a 20-step trajectory violating the read margin at 120 ps. -/
theorem bench03b_asap7_sram_fin_collapse_proved : Bench_03b_asap7_sram_6t_fin_collapse_sat realTF :=
  SramTrajectory.collapse_of_faces SramTrajectory.checkedFaces

/-- A seven-coordinate box contains a low-reference equilibrium at 300 K. -/
theorem bench04a_sige_bandgap_trojan_proved : Bench_04a_ihp_sige_bandgap_trojan_sat realTF :=
  BandgapCertificate.certified

theorem bench07_gan_soa_proved : Bench_07_gan_sic_halfbridge_shootthrough_soa_ode realTF :=
  GanCertificate.certified

theorem bench11_pdn_droop_proved : Bench_11_pcb_pdn_mlcc_derating_droop_ode realTF :=
  PdnCertificate.certified

theorem bench14a_gaa_thermal_safety_proved : Bench_14a_gt2n_gaa_nanosheet_electrothermal_unsat realTF :=
  GaaSafety.certified

theorem bench14b_gaa_thermal_excursion_proved : Bench_14b_gt2n_gaa_nanosheet_thermal_runaway_sat realTF :=
  GaaCertificate.certified

/-- The trapezoidal trajectory stays within the rail envelope at all 41 samples. -/
theorem bench08_ring_envelope_proved : Bench_08_gt2n_gaa_ring_oscillator_3stage_ode realTF :=
  RingCertificate.certified

/-- The wrapped 5 × 3 FinFET stays within 10 pA/µm over its full process box. -/
theorem bench13_finfet_leakage_proved : Bench_13_asap7_finfet_2d_poisson_qconfinement realTF :=
  FinCertificate.certified

end SpiceSmtBench.Targets
