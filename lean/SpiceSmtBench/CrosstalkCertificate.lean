import SpiceSmtBench.CrosstalkGeometry
import SpiceSmtBench.CrosstalkBounds
import SpiceSmtBench.TargetsGenerated

namespace SpiceSmtBench.Crosstalk
open Microstrip LineBounds Enclosed StoredEnergy LeanCert.Core
noncomputable section
set_option maxRecDepth 30000

private theorem exp_value (x : Enclosed) : x.exp.val = Real.exp x.val := rfl

theorem certified : Targets.Bench_10_pcb_coupled_trace_esd_crosstalk_ode realTF := by
  intro er_agg er_vic ds_etch l_via thickness_log_xtalk_p su_xtalk_p eeff_xtalk_p seeff_xtalk_p lnz_xtalk_p Z0_xtalk_p wide_log_xtalk_p Ltot_xtalk_p Ctot_xtalk_p Rdc_xtalk_p thickness_log_xtalk_n su_xtalk_n eeff_xtalk_n seeff_xtalk_n lnz_xtalk_n Z0_xtalk_n wide_log_xtalk_n Ltot_xtalk_n Ctot_xtalk_n Rdc_xtalk_n kc_xtalk Zdiff_xtalk odd_factor_xtalk Cm_xtalk Lm_xtalk thickness_log_xtalk_seg1_p su_xtalk_seg1_p eeff_xtalk_seg1_p seeff_xtalk_seg1_p lnz_xtalk_seg1_p Z0_xtalk_seg1_p wide_log_xtalk_seg1_p Ltot_xtalk_seg1_p Ctot_xtalk_seg1_p Rdc_xtalk_seg1_p thickness_log_xtalk_seg1_n su_xtalk_seg1_n eeff_xtalk_seg1_n seeff_xtalk_seg1_n lnz_xtalk_seg1_n Z0_xtalk_seg1_n wide_log_xtalk_seg1_n Ltot_xtalk_seg1_n Ctot_xtalk_seg1_n Rdc_xtalk_seg1_n kc_xtalk_seg1 Zdiff_xtalk_seg1 odd_factor_xtalk_seg1 Cm_xtalk_seg1 Lm_xtalk_seg1 thickness_log_xtalk_seg2_p su_xtalk_seg2_p eeff_xtalk_seg2_p seeff_xtalk_seg2_p lnz_xtalk_seg2_p Z0_xtalk_seg2_p wide_log_xtalk_seg2_p Ltot_xtalk_seg2_p Ctot_xtalk_seg2_p Rdc_xtalk_seg2_p thickness_log_xtalk_seg2_n su_xtalk_seg2_n eeff_xtalk_seg2_n seeff_xtalk_seg2_n lnz_xtalk_seg2_n Z0_xtalk_seg2_n wide_log_xtalk_seg2_n Ltot_xtalk_seg2_n Ctot_xtalk_seg2_n Rdc_xtalk_seg2_n kc_xtalk_seg2 Zdiff_xtalk_seg2 odd_factor_xtalk_seg2 Cm_xtalk_seg2 Lm_xtalk_seg2 state sampleTime dx boxH equations
  obtain ⟨epB, enB, gapB, viaB, _⟩ := boxH
  let epE := atPoint epBox er_agg (by
    simpa [realTF,epBox,LineBounds.box,IntervalRat.mem_def] using epB)
  let enE := atPoint enBox er_vic (by
    simpa [realTF,enBox,LineBounds.box,IntervalRat.mem_def] using enB)
  let gapE := atPoint gapBox ds_etch (by
    simpa [realTF,gapBox,LineBounds.box,IntervalRat.mem_def] using gapB)
  let viaE := atPoint viaBox l_via (by
    simpa [realTF,viaBox,LineBounds.box,IntervalRat.mem_def] using viaB)
  let mat := material epE enE gapE viaE
  rcases equations with ⟨⟨⟨⟨_, _, _, _, htxtalk_p, hs0xtalk_p, hssxtalk_p, heextalk_p, _, hesxtalk_p, _, hwxtalk_p, hzxtalk_p, hlxtalk_p⟩, ⟨hcxtalk_p, hrxtalk_p, _, _, _, _, htxtalk_n, hs0xtalk_n, hssxtalk_n, heextalk_n, _, hesxtalk_n, _, hwxtalk_n, hzxtalk_n⟩⟩, ⟨⟨hlxtalk_n, hcxtalk_n, hrxtalk_n, hkxtalk, _, _, _, hcmxtalk, hlmxtalk, _, _, _, _, htxtalk_seg1_p⟩, ⟨hs0xtalk_seg1_p, hssxtalk_seg1_p, heextalk_seg1_p, _, hesxtalk_seg1_p, _, hwxtalk_seg1_p, hzxtalk_seg1_p, hlxtalk_seg1_p, hcxtalk_seg1_p, hrxtalk_seg1_p, _, _, _, _⟩⟩⟩, ⟨⟨⟨htxtalk_seg1_n, hs0xtalk_seg1_n, hssxtalk_seg1_n, heextalk_seg1_n, _, hesxtalk_seg1_n, _, hwxtalk_seg1_n, hzxtalk_seg1_n, hlxtalk_seg1_n, hcxtalk_seg1_n, hrxtalk_seg1_n, hkxtalk_seg1, _⟩, ⟨_, _, hcmxtalk_seg1, hlmxtalk_seg1, _, _, _, _, htxtalk_seg2_p, hs0xtalk_seg2_p, hssxtalk_seg2_p, heextalk_seg2_p, _, hesxtalk_seg2_p, _⟩⟩, ⟨⟨hwxtalk_seg2_p, hzxtalk_seg2_p, hlxtalk_seg2_p, hcxtalk_seg2_p, hrxtalk_seg2_p, _, _, _, _, htxtalk_seg2_n, hs0xtalk_seg2_n, hssxtalk_seg2_n, heextalk_seg2_n, _⟩, ⟨hesxtalk_seg2_n, _, hwxtalk_seg2_n, hzxtalk_seg2_n, hlxtalk_seg2_n, hcxtalk_seg2_n, hrxtalk_seg2_n, hkxtalk_seg2, _, _, _, hcmxtalk_seg2, hlmxtalk_seg2, initial, step⟩⟩⟩⟩
  have ⟨Lxtalk_p, Cxtalk_p, Rxtalk_p⟩ : Ltot_xtalk_p=(components mat).lp ∧ Ctot_xtalk_p=(components mat).cp ∧ Rdc_xtalk_p=(components mat).r := by
    apply Microstrip.identify substrate epE thickness_log_xtalk_p su_xtalk_p eeff_xtalk_p seeff_xtalk_p wide_log_xtalk_p Z0_xtalk_p Ltot_xtalk_p Ctot_xtalk_p Rdc_xtalk_p (physical (by exact ep_ok))
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using htxtalk_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hs0xtalk_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hssxtalk_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using heextalk_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hesxtalk_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hwxtalk_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hzxtalk_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hlxtalk_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hcxtalk_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hrxtalk_p
  have ⟨Lxtalk_n, Cxtalk_n, Rxtalk_n⟩ : Ltot_xtalk_n=(components mat).ln ∧ Ctot_xtalk_n=(components mat).cn ∧ Rdc_xtalk_n=(components mat).r := by
    apply Microstrip.identify substrate enE thickness_log_xtalk_n su_xtalk_n eeff_xtalk_n seeff_xtalk_n wide_log_xtalk_n Z0_xtalk_n Ltot_xtalk_n Ctot_xtalk_n Rdc_xtalk_n (physical (by exact en_ok))
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using htxtalk_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hs0xtalk_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hssxtalk_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using heextalk_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hesxtalk_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hwxtalk_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hzxtalk_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hlxtalk_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hcxtalk_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hrxtalk_n
  have Kxtalk : kc_xtalk = (components mat).k := by
    simpa [realTF,components,mat,material,exp_value,Enclosed.fraction,Enclosed.div_val,Enclosed.mul_val,gapE,atPoint] using hkxtalk
  have Cmxtalk : Cm_xtalk=(components mat).cm := by
    rw [Kxtalk,Cxtalk_p,Cxtalk_n] at hcmxtalk
    simpa [realTF,components,mat,material] using hcmxtalk
  have Lmxtalk : Lm_xtalk=(components mat).lm := by
    rw [Kxtalk,Lxtalk_p,Lxtalk_n] at hlmxtalk
    simpa [realTF,components,mat,material] using hlmxtalk
  have ⟨Lxtalk_seg1_p, Cxtalk_seg1_p, Rxtalk_seg1_p⟩ : Ltot_xtalk_seg1_p=(components mat).lp ∧ Ctot_xtalk_seg1_p=(components mat).cp ∧ Rdc_xtalk_seg1_p=(components mat).r := by
    apply Microstrip.identify substrate epE thickness_log_xtalk_seg1_p su_xtalk_seg1_p eeff_xtalk_seg1_p seeff_xtalk_seg1_p wide_log_xtalk_seg1_p Z0_xtalk_seg1_p Ltot_xtalk_seg1_p Ctot_xtalk_seg1_p Rdc_xtalk_seg1_p (physical (by exact ep_ok))
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using htxtalk_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hs0xtalk_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hssxtalk_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using heextalk_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hesxtalk_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hwxtalk_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hzxtalk_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hlxtalk_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hcxtalk_seg1_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hrxtalk_seg1_p
  have ⟨Lxtalk_seg1_n, Cxtalk_seg1_n, Rxtalk_seg1_n⟩ : Ltot_xtalk_seg1_n=(components mat).ln ∧ Ctot_xtalk_seg1_n=(components mat).cn ∧ Rdc_xtalk_seg1_n=(components mat).r := by
    apply Microstrip.identify substrate enE thickness_log_xtalk_seg1_n su_xtalk_seg1_n eeff_xtalk_seg1_n seeff_xtalk_seg1_n wide_log_xtalk_seg1_n Z0_xtalk_seg1_n Ltot_xtalk_seg1_n Ctot_xtalk_seg1_n Rdc_xtalk_seg1_n (physical (by exact en_ok))
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using htxtalk_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hs0xtalk_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hssxtalk_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using heextalk_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hesxtalk_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hwxtalk_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hzxtalk_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hlxtalk_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hcxtalk_seg1_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hrxtalk_seg1_n
  have Kxtalk_seg1 : kc_xtalk_seg1 = (components mat).k := by
    simpa [realTF,components,mat,material,exp_value,Enclosed.fraction,Enclosed.div_val,Enclosed.mul_val,gapE,atPoint] using hkxtalk_seg1
  have Cmxtalk_seg1 : Cm_xtalk_seg1=(components mat).cm := by
    rw [Kxtalk_seg1,Cxtalk_seg1_p,Cxtalk_seg1_n] at hcmxtalk_seg1
    simpa [realTF,components,mat,material] using hcmxtalk_seg1
  have Lmxtalk_seg1 : Lm_xtalk_seg1=(components mat).lm := by
    rw [Kxtalk_seg1,Lxtalk_seg1_p,Lxtalk_seg1_n] at hlmxtalk_seg1
    simpa [realTF,components,mat,material] using hlmxtalk_seg1
  have ⟨Lxtalk_seg2_p, Cxtalk_seg2_p, Rxtalk_seg2_p⟩ : Ltot_xtalk_seg2_p=(components mat).lp ∧ Ctot_xtalk_seg2_p=(components mat).cp ∧ Rdc_xtalk_seg2_p=(components mat).r := by
    apply Microstrip.identify substrate epE thickness_log_xtalk_seg2_p su_xtalk_seg2_p eeff_xtalk_seg2_p seeff_xtalk_seg2_p wide_log_xtalk_seg2_p Z0_xtalk_seg2_p Ltot_xtalk_seg2_p Ctot_xtalk_seg2_p Rdc_xtalk_seg2_p (physical (by exact ep_ok))
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using htxtalk_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hs0xtalk_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hssxtalk_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using heextalk_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hesxtalk_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hwxtalk_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hzxtalk_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hlxtalk_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hcxtalk_seg2_p
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,epE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hrxtalk_seg2_p
  have ⟨Lxtalk_seg2_n, Cxtalk_seg2_n, Rxtalk_seg2_n⟩ : Ltot_xtalk_seg2_n=(components mat).ln ∧ Ctot_xtalk_seg2_n=(components mat).cn ∧ Rdc_xtalk_seg2_n=(components mat).r := by
    apply Microstrip.identify substrate enE thickness_log_xtalk_seg2_n su_xtalk_seg2_n eeff_xtalk_seg2_n seeff_xtalk_seg2_n wide_log_xtalk_seg2_n Z0_xtalk_seg2_n Ltot_xtalk_seg2_n Ctot_xtalk_seg2_n Rdc_xtalk_seg2_n (physical (by exact en_ok))
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using htxtalk_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hs0xtalk_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hssxtalk_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using heextalk_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hesxtalk_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hwxtalk_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hzxtalk_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hlxtalk_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hcxtalk_seg2_n
    · simpa only [realTF,substrate,impedanceConstant,lightSpeed,fraction,integer,enE,atPoint,Int.cast_ofNat,Nat.cast_ofNat] using hrxtalk_seg2_n
  have Kxtalk_seg2 : kc_xtalk_seg2 = (components mat).k := by
    simpa [realTF,components,mat,material,exp_value,Enclosed.fraction,Enclosed.div_val,Enclosed.mul_val,gapE,atPoint] using hkxtalk_seg2
  have Cmxtalk_seg2 : Cm_xtalk_seg2=(components mat).cm := by
    rw [Kxtalk_seg2,Cxtalk_seg2_p,Cxtalk_seg2_n] at hcmxtalk_seg2
    simpa [realTF,components,mat,material] using hcmxtalk_seg2
  have Lmxtalk_seg2 : Lm_xtalk_seg2=(components mat).lm := by
    rw [Kxtalk_seg2,Lxtalk_seg2_p,Lxtalk_seg2_n] at hlmxtalk_seg2
    simpa [realTF,components,mat,material] using hlmxtalk_seg2
  let s : Nat → State 14 := fun k j => state k j.val
  have initialState (i : Fin 14) : s 0 i=0 := by
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := initial
    fin_cases i <;> assumption
  have raw (k : Nat) (i : Fin 14) : dx k i.val = rates (components mat) (s k) (driver k).val
      (upperDiode (s k 3)) (lowerDiode (s k 3)) i := by
    dsimp only [dx]
    simp only [Lxtalk_p, Cxtalk_p, Rxtalk_p, Lxtalk_n, Cxtalk_n, Rxtalk_n, Lxtalk_seg1_p, Cxtalk_seg1_p, Rxtalk_seg1_p, Lxtalk_seg1_n, Cxtalk_seg1_n, Rxtalk_seg1_n, Lxtalk_seg2_p, Cxtalk_seg2_p, Rxtalk_seg2_p, Lxtalk_seg2_n, Cxtalk_seg2_n, Rxtalk_seg2_n, Kxtalk, Cmxtalk, Lmxtalk, Kxtalk_seg1, Cmxtalk_seg1, Lmxtalk_seg1, Kxtalk_seg2, Cmxtalk_seg2, Lmxtalk_seg2]
    have clock (l : Nat) : (ETime l).val=sampleTime l := rfl
    simp only [realTF,Int.cast_ofNat,Int.cast_one,Nat.cast_ofNat,Nat.cast_one,driver,clock,exp_value,
      fraction,Enclosed.div_val,Enclosed.mul_val,Enclosed.sub_val,Enclosed.add_val,Enclosed.neg_val,numeral_val,
      upperDiode,lowerDiode]
    fin_cases i <;> rfl
  have good : check mat := material_ok _ _ _ _ _ _ _ _
  have M := safe_from_stamp mat good s initialState
  suffices law : ∀ k : Fin 5, ∀ i, s (k.val+1) i = s k.val i + (3/50000000000:ℝ) *
    rates (components mat) (s (k.val+1)) (driver (k.val+1)).val
      (upperDiode (s (k.val+1) 3)) (lowerDiode (s (k.val+1) 3)) i by
    rintro ⟨k,hk,violation⟩
    have out := M law k hk
    change -3/4 < state k 3 ∧ state k 3 < 13/20 at out
    norm_num [realTF] at violation
    rcases violation with h|h <;> linarith
  intro k i
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := step k.val k.isLt
  rw [← raw]
  fin_cases i <;> assumption
end
end SpiceSmtBench.Crosstalk
