import SpiceSmtBench.StitchedBounds
import SpiceSmtBench.StitchedReplay
import SpiceSmtBench.TargetsGenerated

namespace SpiceSmtBench.Stitched
open Microstrip LineBounds Enclosed StoredEnergy LeanCert.Core
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 1600000

private theorem exp_value (x : Enclosed) : x.exp.val=Real.exp x.val := rfl

theorem certified : Targets.Bench_12b_pcb_stitched_return_fence_unsat realTF := by
  intro er_p er_n via_pitch thickness_log_bus_p su_bus_p eeff_bus_p seeff_bus_p lnz_bus_p Z0_bus_p wide_log_bus_p Ltot_bus_p Ctot_bus_p Rdc_bus_p thickness_log_bus_n su_bus_n eeff_bus_n seeff_bus_n lnz_bus_n Z0_bus_n wide_log_bus_n Ltot_bus_n Ctot_bus_n Rdc_bus_n kc_bus Zdiff_bus odd_factor_bus Cm_bus Lm_bus thickness_log_bus_seg1_p su_bus_seg1_p eeff_bus_seg1_p seeff_bus_seg1_p lnz_bus_seg1_p Z0_bus_seg1_p wide_log_bus_seg1_p Ltot_bus_seg1_p Ctot_bus_seg1_p Rdc_bus_seg1_p thickness_log_bus_seg1_n su_bus_seg1_n eeff_bus_seg1_n seeff_bus_seg1_n lnz_bus_seg1_n Z0_bus_seg1_n wide_log_bus_seg1_n Ltot_bus_seg1_n Ctot_bus_seg1_n Rdc_bus_seg1_n kc_bus_seg1 Zdiff_bus_seg1 odd_factor_bus_seg1 Cm_bus_seg1 Lm_bus_seg1 thickness_log_bus_seg2_p su_bus_seg2_p eeff_bus_seg2_p seeff_bus_seg2_p lnz_bus_seg2_p Z0_bus_seg2_p wide_log_bus_seg2_p Ltot_bus_seg2_p Ctot_bus_seg2_p Rdc_bus_seg2_p thickness_log_bus_seg2_n su_bus_seg2_n eeff_bus_seg2_n seeff_bus_seg2_n lnz_bus_seg2_n Z0_bus_seg2_n wide_log_bus_seg2_n Ltot_bus_seg2_n Ctot_bus_seg2_n Rdc_bus_seg2_n kc_bus_seg2 Zdiff_bus_seg2 odd_factor_bus_seg2 Cm_bus_seg2 Lm_bus_seg2 state sampleTime dx boxH equations
  obtain ⟨epB, enB, pitchB, _⟩ := boxH
  let epE := atPoint epBox er_p (by
    simpa [realTF,epBox,LineBounds.box,IntervalRat.mem_def] using epB)
  let enE := atPoint enBox er_n (by
    simpa [realTF,enBox,LineBounds.box,IntervalRat.mem_def] using enB)
  let pitchE := atPoint pitchBox via_pitch (by
    simpa [realTF,pitchBox,LineBounds.box,IntervalRat.mem_def] using pitchB)
  let mat := material epE enE pitchE
  rcases equations with ⟨⟨⟨⟨_, _, _, _, htbus_p, hs0bus_p, hssbus_p, heebus_p, _, hesbus_p, _, hwbus_p, hzbus_p, hlbus_p⟩, ⟨hcbus_p, hrbus_p, _, _, _, _, htbus_n, hs0bus_n, hssbus_n, heebus_n, _, hesbus_n, _, hwbus_n, hzbus_n⟩⟩, ⟨⟨hlbus_n, hcbus_n, hrbus_n, hkbus, _, _, _, hcmbus, hlmbus, _, _, _, _, htbus_seg1_p⟩, ⟨hs0bus_seg1_p, hssbus_seg1_p, heebus_seg1_p, _, hesbus_seg1_p, _, hwbus_seg1_p, hzbus_seg1_p, hlbus_seg1_p, hcbus_seg1_p, hrbus_seg1_p, _, _, _, _⟩⟩⟩, ⟨⟨⟨htbus_seg1_n, hs0bus_seg1_n, hssbus_seg1_n, heebus_seg1_n, _, hesbus_seg1_n, _, hwbus_seg1_n, hzbus_seg1_n, hlbus_seg1_n, hcbus_seg1_n, hrbus_seg1_n, hkbus_seg1, _⟩, ⟨_, _, hcmbus_seg1, hlmbus_seg1, _, _, _, _, htbus_seg2_p, hs0bus_seg2_p, hssbus_seg2_p, heebus_seg2_p, _, hesbus_seg2_p, _⟩⟩, ⟨⟨hwbus_seg2_p, hzbus_seg2_p, hlbus_seg2_p, hcbus_seg2_p, hrbus_seg2_p, _, _, _, _, htbus_seg2_n, hs0bus_seg2_n, hssbus_seg2_n, heebus_seg2_n, _⟩, ⟨hesbus_seg2_n, _, hwbus_seg2_n, hzbus_seg2_n, hlbus_seg2_n, hcbus_seg2_n, hrbus_seg2_n, hkbus_seg2, _, _, _, hcmbus_seg2, hlmbus_seg2, initial, step⟩⟩⟩⟩
  have ⟨Lbus_p, Cbus_p, Rbus_p⟩ : Ltot_bus_p=(components mat).lp ∧ Ctot_bus_p=(components mat).cp ∧ Rdc_bus_p=(components mat).r := by
    apply Microstrip.identify substrate epE thickness_log_bus_p su_bus_p eeff_bus_p seeff_bus_p wide_log_bus_p Z0_bus_p Ltot_bus_p Ctot_bus_p Rdc_bus_p (physical (by exact ep_ok))
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using htbus_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hs0bus_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hssbus_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using heebus_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hesbus_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hwbus_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hzbus_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hlbus_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hcbus_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hrbus_p
  have ⟨Lbus_n, Cbus_n, Rbus_n⟩ : Ltot_bus_n=(components mat).ln ∧ Ctot_bus_n=(components mat).cn ∧ Rdc_bus_n=(components mat).r := by
    apply Microstrip.identify substrate enE thickness_log_bus_n su_bus_n eeff_bus_n seeff_bus_n wide_log_bus_n Z0_bus_n Ltot_bus_n Ctot_bus_n Rdc_bus_n (physical (by exact en_ok))
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using htbus_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hs0bus_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hssbus_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using heebus_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hesbus_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hwbus_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hzbus_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hlbus_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hcbus_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hrbus_n
  have Kbus : kc_bus = (components mat).k := by
    norm_num [realTF,components,mat,material,exp_value,Enclosed.fraction] at hkbus ⊢
    exact hkbus
  have Cmbus : Cm_bus=(components mat).cm := by
    rw [Kbus,Cbus_p,Cbus_n] at hcmbus
    simpa [realTF,components,mat,material] using hcmbus
  have Lmbus : Lm_bus=(components mat).lm := by
    rw [Kbus,Lbus_p,Lbus_n] at hlmbus
    simpa [realTF,components,mat,material] using hlmbus
  have ⟨Lbus_seg1_p, Cbus_seg1_p, Rbus_seg1_p⟩ : Ltot_bus_seg1_p=(components mat).lp ∧ Ctot_bus_seg1_p=(components mat).cp ∧ Rdc_bus_seg1_p=(components mat).r := by
    apply Microstrip.identify substrate epE thickness_log_bus_seg1_p su_bus_seg1_p eeff_bus_seg1_p seeff_bus_seg1_p wide_log_bus_seg1_p Z0_bus_seg1_p Ltot_bus_seg1_p Ctot_bus_seg1_p Rdc_bus_seg1_p (physical (by exact ep_ok))
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using htbus_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hs0bus_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hssbus_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using heebus_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hesbus_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hwbus_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hzbus_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hlbus_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hcbus_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hrbus_seg1_p
  have ⟨Lbus_seg1_n, Cbus_seg1_n, Rbus_seg1_n⟩ : Ltot_bus_seg1_n=(components mat).ln ∧ Ctot_bus_seg1_n=(components mat).cn ∧ Rdc_bus_seg1_n=(components mat).r := by
    apply Microstrip.identify substrate enE thickness_log_bus_seg1_n su_bus_seg1_n eeff_bus_seg1_n seeff_bus_seg1_n wide_log_bus_seg1_n Z0_bus_seg1_n Ltot_bus_seg1_n Ctot_bus_seg1_n Rdc_bus_seg1_n (physical (by exact en_ok))
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using htbus_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hs0bus_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hssbus_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using heebus_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hesbus_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hwbus_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hzbus_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hlbus_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hcbus_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hrbus_seg1_n
  have Kbus_seg1 : kc_bus_seg1 = (components mat).k := by
    norm_num [realTF,components,mat,material,exp_value,Enclosed.fraction] at hkbus_seg1 ⊢
    exact hkbus_seg1
  have Cmbus_seg1 : Cm_bus_seg1=(components mat).cm := by
    rw [Kbus_seg1,Cbus_seg1_p,Cbus_seg1_n] at hcmbus_seg1
    simpa [realTF,components,mat,material] using hcmbus_seg1
  have Lmbus_seg1 : Lm_bus_seg1=(components mat).lm := by
    rw [Kbus_seg1,Lbus_seg1_p,Lbus_seg1_n] at hlmbus_seg1
    simpa [realTF,components,mat,material] using hlmbus_seg1
  have ⟨Lbus_seg2_p, Cbus_seg2_p, Rbus_seg2_p⟩ : Ltot_bus_seg2_p=(components mat).lp ∧ Ctot_bus_seg2_p=(components mat).cp ∧ Rdc_bus_seg2_p=(components mat).r := by
    apply Microstrip.identify substrate epE thickness_log_bus_seg2_p su_bus_seg2_p eeff_bus_seg2_p seeff_bus_seg2_p wide_log_bus_seg2_p Z0_bus_seg2_p Ltot_bus_seg2_p Ctot_bus_seg2_p Rdc_bus_seg2_p (physical (by exact ep_ok))
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using htbus_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hs0bus_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hssbus_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using heebus_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hesbus_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hwbus_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hzbus_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hlbus_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hcbus_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hrbus_seg2_p
  have ⟨Lbus_seg2_n, Cbus_seg2_n, Rbus_seg2_n⟩ : Ltot_bus_seg2_n=(components mat).ln ∧ Ctot_bus_seg2_n=(components mat).cn ∧ Rdc_bus_seg2_n=(components mat).r := by
    apply Microstrip.identify substrate enE thickness_log_bus_seg2_n su_bus_seg2_n eeff_bus_seg2_n seeff_bus_seg2_n wide_log_bus_seg2_n Z0_bus_seg2_n Ltot_bus_seg2_n Ctot_bus_seg2_n Rdc_bus_seg2_n (physical (by exact en_ok))
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using htbus_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hs0bus_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hssbus_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using heebus_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hesbus_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hwbus_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hzbus_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hlbus_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hcbus_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hrbus_seg2_n
  have Kbus_seg2 : kc_bus_seg2 = (components mat).k := by
    norm_num [realTF,components,mat,material,exp_value,Enclosed.fraction] at hkbus_seg2 ⊢
    exact hkbus_seg2
  have Cmbus_seg2 : Cm_bus_seg2=(components mat).cm := by
    rw [Kbus_seg2,Cbus_seg2_p,Cbus_seg2_n] at hcmbus_seg2
    simpa [realTF,components,mat,material] using hcmbus_seg2
  have Lmbus_seg2 : Lm_bus_seg2=(components mat).lm := by
    rw [Kbus_seg2,Lbus_seg2_p,Lbus_seg2_n] at hlmbus_seg2
    simpa [realTF,components,mat,material] using hlmbus_seg2
  let s : Nat → State 16 := fun k j => state k j.val
  have initialState (i : Fin 16) : s 0 i=0 := by
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := initial
    fin_cases i <;> assumption
  have raw (k : Nat) (i : Fin 16) : dx k i.val =
      rates (components mat) (s k) (SlotLine.drive k).val 0 0 i := by
    dsimp only [dx]
    simp only [Lbus_p, Cbus_p, Rbus_p, Lbus_n, Cbus_n, Rbus_n, Lbus_seg1_p, Cbus_seg1_p, Rbus_seg1_p, Lbus_seg1_n, Cbus_seg1_n, Rbus_seg1_n, Lbus_seg2_p, Cbus_seg2_p, Rbus_seg2_p, Lbus_seg2_n, Cbus_seg2_n, Rbus_seg2_n, Kbus, Cmbus, Lmbus, Kbus_seg1, Cmbus_seg1, Lmbus_seg1, Kbus_seg2, Cmbus_seg2, Lmbus_seg2]
    have via : (components mat).via = (1/5000000000:ℝ) := by norm_num [components,mat,material,fraction]
    have ret : (components mat).ret = (1/2000000:ℝ)*via_pitch := by norm_num [components,mat,material,fraction,pitchE,atPoint]
    have clock (l : Nat) : (SlotLine.sampleTime l).val=sampleTime l := rfl
    simp only [realTF,Int.cast_ofNat,Int.cast_one,Nat.cast_ofNat,Int.cast_neg,
      SlotLine.drive,SlotLine.driveAt,Enclosed.div_val,Enclosed.sub_val,Enclosed.add_val,Enclosed.neg_val,
      exp_value,clock,fraction,integer,← via,← ret]
    fin_cases i <;> rfl
  have good : materialCheck mat := material_ok _ _ _ _ _ _
  have M := safe_from_stamp epE enE pitchE good s initialState
  suffices law : ∀ k : Fin 80, ∀ i, s (k.val+1) i=s k.val i+(1/200000000000:ℝ)*
      (rates (components mat) (s k.val) (SlotLine.drive k.val).val 0 0 i+
       rates (components mat) (s (k.val+1)) (SlotLine.drive (k.val+1)).val 0 0 i) by
    rintro ⟨k,hk,violation⟩
    have out := M law step_verified receiver_verified k hk
    change -1/40 < state k 4 ∧ state k 4 < 1/40 at out
    norm_num [realTF] at violation
    rcases violation with h|h <;> linarith
  intro k i
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := step k.val k.isLt
  rw [← raw,← raw]
  simp only [realTF,Int.cast_one,Nat.cast_ofNat] at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  fin_cases i <;> assumption
end
end SpiceSmtBench.Stitched
