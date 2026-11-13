import SpiceSmtBench.PhysicsModels
import SpiceSmtBench.IntervalCheck
import SpiceSmtBench.TargetsGenerated
import SpiceSmtBench.PcbCertificate

/-!
# Benchmark Target Specifications & Machine-Checked Proofs

Re-exports all 19 auto-generated SPICE / Multi-PDK / PCB / TCAD benchmark `Prop` definitions
from `SpiceSmtBench.TargetsGenerated` and provides complete end-to-end machine-checked proofs:

1. `bench01_diode_clipper_pvt_proved`: Full kernel-checked `UNSAT` proof of Benchmark 01
   (`Bench_01_diode_clipper_pvt`) across the continuous 2D PVT box `v_sup ∈ [3.0, 3.6] V ×
   vt ∈ [23.5 mV, 32.2 mV]` using rational scaling-and-squaring (`m = 7`, `2^7 = 128`) from
   `IntervalCheck.exp_ge_qrat_iterSq`!
2. `bench01_paving_certificate_proved`: a concrete two-leaf rational replay.
3. `bench06_rc_diode_glitch_filter_proved`: a checked backward-Euler barrier.
4. `bench09a_pcb_microstrip_dfm_proved`: a 23-box forward-bound certificate.
5. Guarded/unguarded bandgap zero-current component lemmas. These do not
   instantiate either generated bandgap target.
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

end SpiceSmtBench.Targets
