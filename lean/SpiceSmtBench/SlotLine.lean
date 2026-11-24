import SpiceSmtBench.LinearTransient
import Mathlib.Data.List.GetD

namespace SpiceSmtBench.SlotLine
open Enclosed LinearTransient
noncomputable section

set_option maxRecDepth 30000

private def oneV : Enclosed := ⟨1,some (.singleton 1),by rintro _ ⟨⟩; simpa using LeanCert.Core.IntervalRat.mem_singleton 1⟩
private def zeroV : Enclosed := ⟨0,some (.singleton 0),by rintro _ ⟨⟩; simpa using LeanCert.Core.IntervalRat.mem_singleton 0⟩
private def atTime (v : List Enclosed) (k : Nat) : Enclosed := ⟨(v.map Enclosed.val).getD k zeroV.val,(v.getD k zeroV).box,by rw [List.getD_map]; exact (v.getD k zeroV).valid⟩
def er_p := (fraction 47 10)
def er_n := (fraction 19 5)
def slot_width := (fraction 3 250)
def thickness_log_bus_p_arg := (fraction 1142857142857143 200000000000000)
def thickness_log_bus_p := (log thickness_log_bus_p_arg)
def su_bus_p_arg := (oneV + ((integer 12) / (((fraction 1 6250) + ((fraction 348151438013521 31250000000000000000) * (oneV + thickness_log_bus_p))) / (fraction 1 10000))))
def su_bus_p := (sqrt su_bus_p_arg ((540268907477090631)/200000000000000000) ((2701344537385453157)/1000000000000000000))
def eeff_bus_p := (((er_p + oneV) / (integer 2)) + ((er_p - oneV) / ((integer 2) * su_bus_p)))
def seeff_bus_p_arg := eeff_bus_p
def seeff_bus_p := (sqrt seeff_bus_p_arg ((3760236241876869)/2000000000000000) ((18801181209384347)/10000000000000000))
def lnz_bus_p_arg := (((integer 8) / (((fraction 1 6250) + ((fraction 348151438013521 31250000000000000000) * (oneV + thickness_log_bus_p))) / (fraction 1 10000))) + ((((fraction 1 6250) + ((fraction 348151438013521 31250000000000000000) * (oneV + thickness_log_bus_p))) / (fraction 1 10000)) / (integer 4)))
def lnz_bus_p := (log lnz_bus_p_arg)
def wide_log_bus_p_arg := ((((fraction 1 6250) + ((fraction 348151438013521 31250000000000000000) * (oneV + thickness_log_bus_p))) / (fraction 1 10000)) + (fraction 361 250))
def wide_log_bus_p := (log wide_log_bus_p_arg)
def Z0_bus_p := ((fraction 7539822368615503 20000000000000) / (seeff_bus_p * (((((fraction 1 6250) + ((fraction 348151438013521 31250000000000000000) * (oneV + thickness_log_bus_p))) / (fraction 1 10000)) + (fraction 1393 1000)) + ((fraction 667 1000) * wide_log_bus_p))))
def Ltot_bus_p := (((fraction 6666666666666667 500000000000000000) * (Z0_bus_p * seeff_bus_p)) / (integer 299792458))
def Ctot_bus_p := ((((fraction 6666666666666667 500000000000000000) * seeff_bus_p) / (integer 299792458)) / Z0_bus_p)
def Rdc_bus_p := ((fraction 6666666666666667 500000000000000000) / (fraction 203 625))
def thickness_log_bus_n_arg := (fraction 1142857142857143 200000000000000)
def thickness_log_bus_n := (log thickness_log_bus_n_arg)
def su_bus_n_arg := (oneV + ((integer 12) / (((fraction 1 6250) + ((fraction 348151438013521 31250000000000000000) * (oneV + thickness_log_bus_n))) / (fraction 1 10000))))
def su_bus_n := (sqrt su_bus_n_arg ((540268907477090631)/200000000000000000) ((2701344537385453157)/1000000000000000000))
def eeff_bus_n := (((er_n + oneV) / (integer 2)) + ((er_n - oneV) / ((integer 2) * su_bus_n)))
def seeff_bus_n_arg := eeff_bus_n
def seeff_bus_n := (sqrt seeff_bus_n_arg ((1708291672062979)/1000000000000000) ((533841147519681)/312500000000000))
def lnz_bus_n_arg := (((integer 8) / (((fraction 1 6250) + ((fraction 348151438013521 31250000000000000000) * (oneV + thickness_log_bus_n))) / (fraction 1 10000))) + ((((fraction 1 6250) + ((fraction 348151438013521 31250000000000000000) * (oneV + thickness_log_bus_n))) / (fraction 1 10000)) / (integer 4)))
def lnz_bus_n := (log lnz_bus_n_arg)
def wide_log_bus_n_arg := ((((fraction 1 6250) + ((fraction 348151438013521 31250000000000000000) * (oneV + thickness_log_bus_n))) / (fraction 1 10000)) + (fraction 361 250))
def wide_log_bus_n := (log wide_log_bus_n_arg)
def Z0_bus_n := ((fraction 7539822368615503 20000000000000) / (seeff_bus_n * (((((fraction 1 6250) + ((fraction 348151438013521 31250000000000000000) * (oneV + thickness_log_bus_n))) / (fraction 1 10000)) + (fraction 1393 1000)) + ((fraction 667 1000) * wide_log_bus_n))))
def Ltot_bus_n := (((fraction 6666666666666667 500000000000000000) * (Z0_bus_n * seeff_bus_n)) / (integer 299792458))
def Ctot_bus_n := ((((fraction 6666666666666667 500000000000000000) * seeff_bus_n) / (integer 299792458)) / Z0_bus_n)
def Rdc_bus_n := ((fraction 6666666666666667 500000000000000000) / (fraction 203 625))
def kc_bus := (exp (fraction (-171) 50))
def odd_factor_bus_arg := ((oneV - kc_bus) / (oneV + kc_bus))
def odd_factor_bus := (sqrt odd_factor_bus_arg ((1935611059321461)/2000000000000000) ((9678055296607307)/10000000000000000))
def Zdiff_bus := ((Z0_bus_p + Z0_bus_n) * odd_factor_bus)
def Cm_bus := ((fraction 1 2) * (kc_bus * (Ctot_bus_p + Ctot_bus_n)))
def Lm_bus := ((fraction 1 2) * (kc_bus * (Ltot_bus_p + Ltot_bus_n)))

theorem thickness_log_bus_p_law : Real.exp thickness_log_bus_p.val = thickness_log_bus_p_arg.val :=
  Real.exp_log (Enclosed.pos (x := thickness_log_bus_p_arg) (by decide +kernel))
theorem su_bus_p_law : su_bus_p.val * su_bus_p.val = su_bus_p_arg.val :=
  Real.mul_self_sqrt (Enclosed.pos (x := su_bus_p_arg) (by decide +kernel)).le
theorem seeff_bus_p_law : seeff_bus_p.val * seeff_bus_p.val = seeff_bus_p_arg.val :=
  Real.mul_self_sqrt (Enclosed.pos (x := seeff_bus_p_arg) (by decide +kernel)).le
theorem lnz_bus_p_law : Real.exp lnz_bus_p.val = lnz_bus_p_arg.val :=
  Real.exp_log (Enclosed.pos (x := lnz_bus_p_arg) (by decide +kernel))
theorem wide_log_bus_p_law : Real.exp wide_log_bus_p.val = wide_log_bus_p_arg.val :=
  Real.exp_log (Enclosed.pos (x := wide_log_bus_p_arg) (by decide +kernel))
theorem Ctot_bus_p_law : Ctot_bus_p.val * Z0_bus_p.val = (((fraction 6666666666666667 500000000000000000) * seeff_bus_p) / (integer 299792458)).val :=
  div_mul_cancel₀ _ (Enclosed.pos (x := Z0_bus_p) (by decide +kernel)).ne'
theorem Rdc_bus_p_law : Rdc_bus_p.val * (fraction 203 625).val = (fraction 6666666666666667 500000000000000000).val :=
  div_mul_cancel₀ _ (Enclosed.pos (x := (fraction 203 625)) (by decide +kernel)).ne'
theorem thickness_log_bus_n_law : Real.exp thickness_log_bus_n.val = thickness_log_bus_n_arg.val :=
  Real.exp_log (Enclosed.pos (x := thickness_log_bus_n_arg) (by decide +kernel))
theorem su_bus_n_law : su_bus_n.val * su_bus_n.val = su_bus_n_arg.val :=
  Real.mul_self_sqrt (Enclosed.pos (x := su_bus_n_arg) (by decide +kernel)).le
theorem seeff_bus_n_law : seeff_bus_n.val * seeff_bus_n.val = seeff_bus_n_arg.val :=
  Real.mul_self_sqrt (Enclosed.pos (x := seeff_bus_n_arg) (by decide +kernel)).le
theorem lnz_bus_n_law : Real.exp lnz_bus_n.val = lnz_bus_n_arg.val :=
  Real.exp_log (Enclosed.pos (x := lnz_bus_n_arg) (by decide +kernel))
theorem wide_log_bus_n_law : Real.exp wide_log_bus_n.val = wide_log_bus_n_arg.val :=
  Real.exp_log (Enclosed.pos (x := wide_log_bus_n_arg) (by decide +kernel))
theorem Ctot_bus_n_law : Ctot_bus_n.val * Z0_bus_n.val = (((fraction 6666666666666667 500000000000000000) * seeff_bus_n) / (integer 299792458)).val :=
  div_mul_cancel₀ _ (Enclosed.pos (x := Z0_bus_n) (by decide +kernel)).ne'
theorem Rdc_bus_n_law : Rdc_bus_n.val * (fraction 203 625).val = (fraction 6666666666666667 500000000000000000).val :=
  div_mul_cancel₀ _ (Enclosed.pos (x := (fraction 203 625)) (by decide +kernel)).ne'
theorem odd_factor_bus_law : odd_factor_bus.val * odd_factor_bus.val = odd_factor_bus_arg.val :=
  Real.mul_self_sqrt (Enclosed.pos (x := odd_factor_bus_arg) (by decide +kernel)).le

def sampleTime (k : Nat) : Enclosed :=
  atTime ([zeroV,
    (fraction 1 100000000000),
    (fraction 1 50000000000),
    (fraction 3 100000000000),
    (fraction 1 25000000000),
    (fraction 9999999999999999 200000000000000000000000000),
    (fraction 3 50000000000),
    (fraction 6999999999999999 100000000000000000000000000),
    (fraction 1 12500000000),
    (fraction 9 100000000000),
    (fraction 9999999999999999 100000000000000000000000000),
    (fraction 11 100000000000),
    (fraction 3 25000000000),
    (fraction 13 100000000000),
    (fraction 6999999999999999 50000000000000000000000000),
    (fraction 3 20000000000),
    (fraction 1 6250000000),
    (fraction 8499999999999999 50000000000000000000000000),
    (fraction 9 50000000000),
    (fraction 19 100000000000),
    (fraction 9999999999999999 50000000000000000000000000),
    (fraction 21 100000000000),
    (fraction 11 50000000000),
    (fraction 11499999999999999 50000000000000000000000000),
    (fraction 3 12500000000),
    (fraction 6249999999999999 25000000000000000000000000),
    (fraction 13 50000000000),
    (fraction 27 100000000000),
    (fraction 6999999999999999 25000000000000000000000000),
    (fraction 29 100000000000),
    (fraction 3 10000000000),
    (fraction 7749999999999999 25000000000000000000000000),
    (fraction 1 3125000000),
    (fraction 33 100000000000),
    (fraction 8499999999999999 25000000000000000000000000),
    (fraction 7 20000000000),
    (fraction 9 25000000000),
    (fraction 9249999999999999 25000000000000000000000000),
    (fraction 19 50000000000),
    (fraction 39 100000000000),
    (fraction 9999999999999999 25000000000000000000000000),
    (fraction 41 100000000000),
    (fraction 21 50000000000),
    (fraction 10749999999999999 25000000000000000000000000),
    (fraction 11 25000000000),
    (fraction 9 20000000000),
    (fraction 11499999999999999 25000000000000000000000000),
    (fraction 4699999999999999 10000000000000000000000000),
    (fraction 3 6250000000),
    (fraction 49 100000000000),
    (fraction 4999999999999999 10000000000000000000000000),
    (fraction 51 100000000000),
    (fraction 13 25000000000),
    (fraction 5299999999999999 10000000000000000000000000),
    (fraction 27 50000000000),
    (fraction 11 20000000000),
    (fraction 5599999999999999 10000000000000000000000000),
    (fraction 57 100000000000),
    (fraction 29 50000000000),
    (fraction 5899999999999999 10000000000000000000000000),
    (fraction 3 5000000000),
    (fraction 61 100000000000),
    (fraction 6199999999999999 10000000000000000000000000),
    (fraction 63 100000000000),
    (fraction 1 1562500000),
    (fraction 6499999999999999 10000000000000000000000000),
    (fraction 33 50000000000),
    (fraction 67 100000000000),
    (fraction 6799999999999999 10000000000000000000000000),
    (fraction 69 100000000000),
    (fraction 7 10000000000),
    (fraction 7099999999999999 10000000000000000000000000),
    (fraction 9 12500000000),
    (fraction 73 100000000000),
    (fraction 7399999999999999 10000000000000000000000000),
    (fraction 3 4000000000),
    (fraction 19 25000000000),
    (fraction 7699999999999999 10000000000000000000000000),
    (fraction 39 50000000000),
    (fraction 79 100000000000),
    (fraction 7999999999999999 10000000000000000000000000)] : List Enclosed) k
def driveAt (t : Enclosed) := (((oneV / (oneV + (exp (-((t - (fraction 1 12500000000)) / (fraction 1 100000000000)))))) - (oneV / (oneV + (exp (integer 8))))) / (oneV - (oneV / (oneV + (exp (integer 8))))))
def drive (k : Nat) := driveAt (sampleTime k)

private def factor0 := (oneV - kc_bus)
private def factor1 := (Ctot_bus_p * factor0)
private def factor2 := ((fraction 1 2) * factor1)
private def factor3 := (factor2 + factor2)
private def factor4 := ((fraction 1 2) * Cm_bus)
private def factor5 := (factor4 + factor4)
private def factor6 := (factor3 + factor5)
private def factor7 := (Ctot_bus_n * factor0)
private def factor8 := ((fraction 1 2) * factor7)
private def factor9 := (factor8 + factor8)
private def factor10 := (factor9 * factor3)
private def factor11 := (factor9 + factor3)
private def factor12 := (factor5 * factor11)
private def factor13 := (factor10 + factor12)
private def factor14 := (factor9 + factor5)
private def factor15 := (factor8 + factor4)
private def factor16 := (factor2 + factor4)
private def factor17 := (factor15 * factor16)
private def factor18 := (-factor4)
private def factor19 := (factor18 * factor18)
private def factor20 := (factor17 - factor19)
private def factor21 := (-factor2)
private def factor22 := (factor21 * factor18)
private def factor23 := (-factor8)
private def factor24 := (factor23 * factor16)
private def factor25 := (factor22 - factor24)
private def factor26 := (factor23 * factor18)
private def factor27 := (factor15 * factor21)
private def factor28 := (factor26 - factor27)
private def factor29 := (factor8 + factor2)
private def factor30 := ((fraction 3 2000000000000) + factor29)
private def factor31 := (factor30 * factor20)
private def factor32 := (factor23 * factor25)
private def factor33 := (factor21 * factor28)
private def factor34 := (factor32 + factor33)
private def factor35 := (factor31 + factor34)
private def factor36 := (factor8 * factor2)
private def factor37 := (factor4 * factor29)
private def factor38 := (factor36 + factor37)
private def factor39 := (factor23 * factor21)
private def factor40 := (factor30 * factor18)
private def factor41 := (factor39 - factor40)
private def factor42 := (Ltot_bus_n + (fraction 1 5000000000))
private def factor43 := (Ltot_bus_p + (fraction 1 5000000000))
private def factor44 := (Lm_bus * Lm_bus)
private def factor45 := (Ltot_bus_p * Ltot_bus_n)
private def factor46 := (factor45 - factor44)
private def factor47 := (Ltot_bus_n * Ltot_bus_p)
private def factor48 := (factor47 - factor44)
private def derivative0 : Form 17 :=
  (Form.divide (Form.plus (Form.scale factor6 (Form.minus (Form.input 11) (Form.input 13))) (Form.scale factor5 (Form.minus (Form.input 10) (Form.input 12)))) factor13)
private def derivative1 : Form 17 :=
  (Form.divide (Form.plus (Form.scale factor6 (Form.minus (Form.input 13) (Form.input 15))) (Form.scale factor5 (Form.minus (Form.input 12) (Form.input 14)))) factor13)
private def derivative2 : Form 17 :=
  (Form.divide (Form.plus (Form.scale factor14 (Form.minus (Form.input 10) (Form.input 12))) (Form.scale factor5 (Form.minus (Form.input 11) (Form.input 13)))) factor13)
private def derivative3 : Form 17 :=
  (Form.divide (Form.plus (Form.scale factor14 (Form.minus (Form.input 12) (Form.input 14))) (Form.scale factor5 (Form.minus (Form.input 13) (Form.input 15)))) factor13)
private def derivative4 : Form 17 :=
  (Form.divide (Form.plus (Form.scale factor20 (Form.plus (Form.plus (Form.input 16) (Form.divide (Form.minus (Form.input 9) (Form.input 5)) (integer 50))) (Form.divide (Form.minus (Form.input 8) (Form.input 5)) (integer 50)))) (Form.plus (Form.scale factor25 (Form.minus (Form.input 15) (Form.divide (Form.minus (Form.input 8) (Form.input 5)) (integer 50)))) (Form.scale factor28 (Form.minus (Form.input 14) (Form.divide (Form.minus (Form.input 9) (Form.input 5)) (integer 50)))))) factor35)
private def derivative5 : Form 17 :=
  (Form.divide (Form.plus (Form.scale factor16 (Form.minus (Form.divide (Form.minus (Form.scale (integer (-1)) (Form.input 0)) (Form.input 6)) (integer 25)) (Form.input 11))) (Form.scale factor4 (Form.minus (Form.divide (Form.minus (Form.input 0) (Form.input 7)) (integer 25)) (Form.input 10)))) factor38)
private def derivative6 : Form 17 :=
  (Form.divide (Form.plus (Form.scale factor15 (Form.minus (Form.divide (Form.minus (Form.input 0) (Form.input 7)) (integer 25)) (Form.input 10))) (Form.scale factor4 (Form.minus (Form.divide (Form.minus (Form.scale (integer (-1)) (Form.input 0)) (Form.input 6)) (integer 25)) (Form.input 11)))) factor38)
private def derivative7 : Form 17 :=
  (Form.divide (Form.plus (Form.scale factor25 (Form.plus (Form.plus (Form.input 16) (Form.divide (Form.minus (Form.input 9) (Form.input 5)) (integer 50))) (Form.divide (Form.minus (Form.input 8) (Form.input 5)) (integer 50)))) (Form.plus (Form.scale ((factor30 * factor16) - (factor21 * factor21)) (Form.minus (Form.input 15) (Form.divide (Form.minus (Form.input 8) (Form.input 5)) (integer 50)))) (Form.scale factor41 (Form.minus (Form.input 14) (Form.divide (Form.minus (Form.input 9) (Form.input 5)) (integer 50)))))) factor35)
private def derivative8 : Form 17 :=
  (Form.divide (Form.plus (Form.scale factor28 (Form.plus (Form.plus (Form.input 16) (Form.divide (Form.minus (Form.input 9) (Form.input 5)) (integer 50))) (Form.divide (Form.minus (Form.input 8) (Form.input 5)) (integer 50)))) (Form.plus (Form.scale factor41 (Form.minus (Form.input 15) (Form.divide (Form.minus (Form.input 8) (Form.input 5)) (integer 50)))) (Form.scale ((factor30 * factor15) - (factor23 * factor23)) (Form.minus (Form.input 14) (Form.divide (Form.minus (Form.input 9) (Form.input 5)) (integer 50)))))) factor35)
private def derivative9 : Form 17 :=
  (Form.divide (Form.minus (Form.scale factor42 (Form.minus (Form.minus (Form.input 7) (Form.input 3)) (Form.scale Rdc_bus_p (Form.input 10)))) (Form.scale Lm_bus (Form.minus (Form.minus (Form.input 6) (Form.input 1)) (Form.scale Rdc_bus_n (Form.input 11))))) ((factor43 * factor42) - factor44))
private def derivative10 : Form 17 :=
  (Form.divide (Form.minus (Form.scale factor43 (Form.minus (Form.minus (Form.input 6) (Form.input 1)) (Form.scale Rdc_bus_n (Form.input 11)))) (Form.scale Lm_bus (Form.minus (Form.minus (Form.input 7) (Form.input 3)) (Form.scale Rdc_bus_p (Form.input 10))))) ((factor42 * factor43) - factor44))
private def derivative11 : Form 17 :=
  (Form.divide (Form.minus (Form.scale Ltot_bus_n (Form.minus (Form.minus (Form.input 3) (Form.input 4)) (Form.scale Rdc_bus_p (Form.input 12)))) (Form.scale Lm_bus (Form.minus (Form.minus (Form.input 1) (Form.input 2)) (Form.scale Rdc_bus_n (Form.input 13))))) factor46)
private def derivative12 : Form 17 :=
  (Form.divide (Form.minus (Form.scale Ltot_bus_p (Form.minus (Form.minus (Form.input 1) (Form.input 2)) (Form.scale Rdc_bus_n (Form.input 13)))) (Form.scale Lm_bus (Form.minus (Form.minus (Form.input 3) (Form.input 4)) (Form.scale Rdc_bus_p (Form.input 12))))) factor48)
private def derivative13 : Form 17 :=
  (Form.divide (Form.minus (Form.scale Ltot_bus_n (Form.minus (Form.minus (Form.input 4) (Form.input 9)) (Form.scale Rdc_bus_p (Form.input 14)))) (Form.scale Lm_bus (Form.minus (Form.minus (Form.input 2) (Form.input 8)) (Form.scale Rdc_bus_n (Form.input 15))))) factor46)
private def derivative14 : Form 17 :=
  (Form.divide (Form.minus (Form.scale Ltot_bus_p (Form.minus (Form.minus (Form.input 2) (Form.input 8)) (Form.scale Rdc_bus_n (Form.input 15)))) (Form.scale Lm_bus (Form.minus (Form.minus (Form.input 4) (Form.input 9)) (Form.scale Rdc_bus_p (Form.input 14))))) factor48)
private def derivative15 : Form 17 :=
  (Form.divide (Form.minus (Form.neg (Form.input 5)) (Form.scale (fraction 1 20) (Form.input 16))) ((fraction 1 2000000) * slot_width))
def rates (i : Fin 16) : Form 17 :=
  ![derivative0, derivative1, derivative2, derivative3, derivative4, derivative5, derivative6, derivative7, derivative8, derivative9, derivative10, derivative11, derivative12, derivative13, derivative14, derivative15] i
def flow (i : Fin 16) : Form 17 := Form.scale (fraction 1 200000000000) (rates i)
end
end SpiceSmtBench.SlotLine
