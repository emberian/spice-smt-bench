import SpiceSmtBench.CrosstalkLine
import SpiceSmtBench.LineBounds

namespace SpiceSmtBench.Crosstalk
open StoredEnergy
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false in
section
private def factor0 (p : Line) : ℝ := (p.lm * p.lm)
private def factor1 (p : Line) : ℝ := (p.lp * p.ln)
private def factor2 (p : Line) : ℝ := (p.ln * p.lp)
private def factor3 (p : Line) : ℝ := (1 - p.k)
private def factor4 (p : Line) : ℝ := (p.ln + p.via)
private def factor5 (p : Line) : ℝ := (p.lp + p.via)
private def factor6 (p : Line) : ℝ := ((1/2) * p.cm)
private def factor7 (p : Line) : ℝ := (p.cn * (factor3 p))
private def factor8 (p : Line) : ℝ := (p.cp * (factor3 p))
private def factor9 (p : Line) : ℝ := ((factor1 p) - (factor0 p))
private def factor10 (p : Line) : ℝ := ((factor2 p) - (factor0 p))
private def factor11 (p : Line) : ℝ := ((1/2) * (factor7 p))
private def factor12 (p : Line) : ℝ := ((1/2) * (factor8 p))
private def factor13 (p : Line) : ℝ := ((factor6 p) + (factor6 p))
private def factor14 (p : Line) : ℝ := ((factor11 p) + (1/400000000000))
private def factor15 (p : Line) : ℝ := ((factor12 p) + (1/500000000000))
private def factor16 (p : Line) : ℝ := ((factor12 p) * (factor11 p))
private def factor17 (p : Line) : ℝ := ((factor12 p) + (factor11 p))
private def factor18 (p : Line) : ℝ := ((factor12 p) + (factor12 p))
private def factor19 (p : Line) : ℝ := ((factor11 p) + (factor11 p))
private def factor20 (p : Line) : ℝ := ((factor6 p) * (factor17 p))
private def factor21 (p : Line) : ℝ := ((factor15 p) * (factor14 p))
private def factor22 (p : Line) : ℝ := ((factor15 p) + (factor14 p))
private def factor23 (p : Line) : ℝ := ((factor18 p) + (factor13 p))
private def factor24 (p : Line) : ℝ := ((factor19 p) + (factor13 p))
private def factor25 (p : Line) : ℝ := ((factor6 p) * (factor22 p))
private def factor26 (p : Line) : ℝ := ((factor19 p) * (factor18 p))
private def factor27 (p : Line) : ℝ := ((factor19 p) + (factor18 p))
private def factor28 (p : Line) : ℝ := ((factor16 p) + (factor20 p))
private def factor29 (p : Line) : ℝ := ((factor13 p) * (factor27 p))
private def factor30 (p : Line) : ℝ := ((factor21 p) + (factor25 p))
private def factor31 (p : Line) : ℝ := ((factor26 p) + (factor29 p))
def den0 (p : Line) : ℝ := (factor28 p)
def den1 (p : Line) : ℝ := (factor30 p)
def den2 (p : Line) : ℝ := (factor31 p)
def den3 (p : Line) : ℝ := (((factor5 p) * (factor4 p)) - (factor0 p))
def den4 (p : Line) : ℝ := (((factor4 p) * (factor5 p)) - (factor0 p))
def den5 (p : Line) : ℝ := (factor9 p)
def den6 (p : Line) : ℝ := (factor10 p)
private def row0 (p : Line) (s : State 14) (u hi lo : ℝ) : ℝ := (((((factor11 p) + (factor6 p)) * (((u - (s 0)) / 28) - (s 8))) + ((factor6 p) * ((-((s 2) / 50)) - (s 9)))) / (den0 p))
private def row1 (p : Line) (s : State 14) (u hi lo : ℝ) : ℝ := (((((factor14 p) + (factor6 p)) * ((s 12) - ((s 1) / 50))) + ((factor6 p) * (((s 13) - hi) + lo))) / (den1 p))
private def row2 (p : Line) (s : State 14) (u hi lo : ℝ) : ℝ := (((((factor12 p) + (factor6 p)) * ((-((s 2) / 50)) - (s 9))) + ((factor6 p) * (((u - (s 0)) / 28) - (s 8)))) / (den0 p))
private def row3 (p : Line) (s : State 14) (u hi lo : ℝ) : ℝ := (((((factor15 p) + (factor6 p)) * (((s 13) - hi) + lo)) + ((factor6 p) * ((s 12) - ((s 1) / 50)))) / (den1 p))
private def row4 (p : Line) (s : State 14) (u hi lo : ℝ) : ℝ := ((((factor23 p) * ((s 9) - (s 11))) + ((factor13 p) * ((s 8) - (s 10)))) / (den2 p))
private def row5 (p : Line) (s : State 14) (u hi lo : ℝ) : ℝ := ((((factor23 p) * ((s 11) - (s 13))) + ((factor13 p) * ((s 10) - (s 12)))) / (den2 p))
private def row6 (p : Line) (s : State 14) (u hi lo : ℝ) : ℝ := ((((factor24 p) * ((s 8) - (s 10))) + ((factor13 p) * ((s 9) - (s 11)))) / (den2 p))
private def row7 (p : Line) (s : State 14) (u hi lo : ℝ) : ℝ := ((((factor24 p) * ((s 10) - (s 12))) + ((factor13 p) * ((s 11) - (s 13)))) / (den2 p))
private def row8 (p : Line) (s : State 14) (u hi lo : ℝ) : ℝ := ((((factor4 p) * (((s 0) - (s 6)) - (p.r * (s 8)))) - (p.lm * (((s 2) - (s 4)) - (p.r * (s 9))))) / (den3 p))
private def row9 (p : Line) (s : State 14) (u hi lo : ℝ) : ℝ := ((((factor5 p) * (((s 2) - (s 4)) - (p.r * (s 9)))) - (p.lm * (((s 0) - (s 6)) - (p.r * (s 8))))) / (den4 p))
private def row10 (p : Line) (s : State 14) (u hi lo : ℝ) : ℝ := (((p.ln * (((s 6) - (s 7)) - (p.r * (s 10)))) - (p.lm * (((s 4) - (s 5)) - (p.r * (s 11))))) / (den5 p))
private def row11 (p : Line) (s : State 14) (u hi lo : ℝ) : ℝ := (((p.lp * (((s 4) - (s 5)) - (p.r * (s 11)))) - (p.lm * (((s 6) - (s 7)) - (p.r * (s 10))))) / (den6 p))
private def row12 (p : Line) (s : State 14) (u hi lo : ℝ) : ℝ := (((p.ln * (((s 7) - (s 1)) - (p.r * (s 12)))) - (p.lm * (((s 5) - (s 3)) - (p.r * (s 13))))) / (den5 p))
private def row13 (p : Line) (s : State 14) (u hi lo : ℝ) : ℝ := (((p.lp * (((s 5) - (s 3)) - (p.r * (s 13)))) - (p.lm * (((s 7) - (s 1)) - (p.r * (s 12))))) / (den6 p))
end
def rates (p : Line) (s : State 14) (u hi lo : ℝ) : State 14 :=
  ![row0 p s u hi lo, row1 p s u hi lo, row2 p s u hi lo, row3 p s u hi lo, row4 p s u hi lo, row5 p s u hi lo, row6 p s u hi lo, row7 p s u hi lo, row8 p s u hi lo, row9 p s u hi lo, row10 p s u hi lo, row11 p s u hi lo, row12 p s u hi lo, row13 p s u hi lo]
def regular (p : Line) := den0 p ≠ 0 ∧ den1 p ≠ 0 ∧ den2 p ≠ 0 ∧ den3 p ≠ 0 ∧ den4 p ≠ 0 ∧ den5 p ≠ 0 ∧ den6 p ≠ 0
private theorem equation0 (p : Line) (s : State 14) (u hi lo : ℝ) (ok : regular p) :
    (3/50000000000)*10^12*(((1/2)*(p.cp*(1-p.k)+p.cm)) * (row0 p s u hi lo) + (-((1/2)*p.cm)) * (row2 p s u hi lo)) = (6/5)*((-50/28) * (s 0) + (-1) * ((50 * s 8))) + (6/5)*(u*50/28) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ok
  dsimp only [row0,row2]
  field_simp [h0,h1,h2,h3,h4,h5,h6]
  simp only [den0,factor3,factor6,factor7,factor8,factor11,factor12,factor16,factor17,factor20,factor28]
  ring

private theorem equation1 (p : Line) (s : State 14) (u hi lo : ℝ) (ok : regular p) :
    (3/50000000000)*10^12*(((1/2)*(p.cp*(1-p.k)+p.cm)+(1/500000000000)) * (row1 p s u hi lo) + (-((1/2)*p.cm)) * (row3 p s u hi lo)) = (6/5)*((-1) * (s 1) + (1) * ((50 * s 12))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ok
  dsimp only [row1,row3]
  field_simp [h0,h1,h2,h3,h4,h5,h6]
  simp only [den1,factor3,factor6,factor7,factor8,factor11,factor12,factor14,factor15,factor21,factor22,factor25,factor30]
  ring

private theorem equation2 (p : Line) (s : State 14) (u hi lo : ℝ) (ok : regular p) :
    (3/50000000000)*10^12*((-((1/2)*p.cm)) * (row0 p s u hi lo) + ((1/2)*(p.cn*(1-p.k)+p.cm)) * (row2 p s u hi lo)) = (6/5)*((-1) * (s 2) + (-1) * ((50 * s 9))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ok
  dsimp only [row0,row2]
  field_simp [h0,h1,h2,h3,h4,h5,h6]
  simp only [den0,factor3,factor6,factor7,factor8,factor11,factor12,factor16,factor17,factor20,factor28]
  ring

private theorem equation3 (p : Line) (s : State 14) (u hi lo : ℝ) (ok : regular p) :
    (3/50000000000)*10^12*((-((1/2)*p.cm)) * (row1 p s u hi lo) + ((1/2)*(p.cn*(1-p.k)+p.cm)+(1/400000000000)) * (row3 p s u hi lo)) = (6/5)*((1) * ((50 * s 13))) + (6/5)*50*(-hi+lo) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ok
  dsimp only [row1,row3]
  field_simp [h0,h1,h2,h3,h4,h5,h6]
  simp only [den1,factor3,factor6,factor7,factor8,factor11,factor12,factor14,factor15,factor21,factor22,factor25,factor30]
  ring

private theorem equation4 (p : Line) (s : State 14) (u hi lo : ℝ) (ok : regular p) :
    (3/50000000000)*10^12*((1*(p.cn*(1-p.k)+p.cm)) * (row4 p s u hi lo) + (-(1*p.cm)) * (row6 p s u hi lo)) = (6/5)*((1) * ((50 * s 9)) + (-1) * ((50 * s 11))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ok
  dsimp only [row4,row6]
  field_simp [h0,h1,h2,h3,h4,h5,h6]
  simp only [den2,factor3,factor6,factor7,factor8,factor11,factor12,factor13,factor18,factor19,factor23,factor24,factor26,factor27,factor29,factor31]
  ring

private theorem equation5 (p : Line) (s : State 14) (u hi lo : ℝ) (ok : regular p) :
    (3/50000000000)*10^12*((1*(p.cn*(1-p.k)+p.cm)) * (row5 p s u hi lo) + (-(1*p.cm)) * (row7 p s u hi lo)) = (6/5)*((1) * ((50 * s 11)) + (-1) * ((50 * s 13))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ok
  dsimp only [row5,row7]
  field_simp [h0,h1,h2,h3,h4,h5,h6]
  simp only [den2,factor3,factor6,factor7,factor8,factor11,factor12,factor13,factor18,factor19,factor23,factor24,factor26,factor27,factor29,factor31]
  ring

private theorem equation6 (p : Line) (s : State 14) (u hi lo : ℝ) (ok : regular p) :
    (3/50000000000)*10^12*((-(1*p.cm)) * (row4 p s u hi lo) + (1*(p.cp*(1-p.k)+p.cm)) * (row6 p s u hi lo)) = (6/5)*((1) * ((50 * s 8)) + (-1) * ((50 * s 10))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ok
  dsimp only [row4,row6]
  field_simp [h0,h1,h2,h3,h4,h5,h6]
  simp only [den2,factor3,factor6,factor7,factor8,factor11,factor12,factor13,factor18,factor19,factor23,factor24,factor26,factor27,factor29,factor31]
  ring

private theorem equation7 (p : Line) (s : State 14) (u hi lo : ℝ) (ok : regular p) :
    (3/50000000000)*10^12*((-(1*p.cm)) * (row5 p s u hi lo) + (1*(p.cp*(1-p.k)+p.cm)) * (row7 p s u hi lo)) = (6/5)*((1) * ((50 * s 10)) + (-1) * ((50 * s 12))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ok
  dsimp only [row5,row7]
  field_simp [h0,h1,h2,h3,h4,h5,h6]
  simp only [den2,factor3,factor6,factor7,factor8,factor11,factor12,factor13,factor18,factor19,factor23,factor24,factor26,factor27,factor29,factor31]
  ring

private theorem equation8 (p : Line) (s : State 14) (u hi lo : ℝ) (ok : regular p) :
    (3/50000000000)*10^12*(((p.lp+p.via)/2500) * ((50 * row8 p s u hi lo)) + (p.lm/2500) * ((50 * row9 p s u hi lo))) = (6/5)*((1) * (s 0) + (-1) * (s 6) + (-p.r/50) * ((50 * s 8))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ok
  dsimp only [row8,row9]
  field_simp [h0,h1,h2,h3,h4,h5,h6]
  simp only [den3,den4,factor0,factor4,factor5]
  ring

private theorem equation9 (p : Line) (s : State 14) (u hi lo : ℝ) (ok : regular p) :
    (3/50000000000)*10^12*((p.lm/2500) * ((50 * row8 p s u hi lo)) + ((p.ln+p.via)/2500) * ((50 * row9 p s u hi lo))) = (6/5)*((1) * (s 2) + (-1) * (s 4) + (-p.r/50) * ((50 * s 9))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ok
  dsimp only [row8,row9]
  field_simp [h0,h1,h2,h3,h4,h5,h6]
  simp only [den3,den4,factor0,factor4,factor5]
  ring

private theorem equation10 (p : Line) (s : State 14) (u hi lo : ℝ) (ok : regular p) :
    (3/50000000000)*10^12*(((p.lp)/2500) * ((50 * row10 p s u hi lo)) + (p.lm/2500) * ((50 * row11 p s u hi lo))) = (6/5)*((1) * (s 6) + (-1) * (s 7) + (-p.r/50) * ((50 * s 10))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ok
  dsimp only [row10,row11]
  field_simp [h0,h1,h2,h3,h4,h5,h6]
  simp only [den5,den6,factor0,factor1,factor2,factor9,factor10]
  ring

private theorem equation11 (p : Line) (s : State 14) (u hi lo : ℝ) (ok : regular p) :
    (3/50000000000)*10^12*((p.lm/2500) * ((50 * row10 p s u hi lo)) + ((p.ln)/2500) * ((50 * row11 p s u hi lo))) = (6/5)*((1) * (s 4) + (-1) * (s 5) + (-p.r/50) * ((50 * s 11))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ok
  dsimp only [row10,row11]
  field_simp [h0,h1,h2,h3,h4,h5,h6]
  simp only [den5,den6,factor0,factor1,factor2,factor9,factor10]
  ring

private theorem equation12 (p : Line) (s : State 14) (u hi lo : ℝ) (ok : regular p) :
    (3/50000000000)*10^12*(((p.lp)/2500) * ((50 * row12 p s u hi lo)) + (p.lm/2500) * ((50 * row13 p s u hi lo))) = (6/5)*((-1) * (s 1) + (1) * (s 7) + (-p.r/50) * ((50 * s 12))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ok
  dsimp only [row12,row13]
  field_simp [h0,h1,h2,h3,h4,h5,h6]
  simp only [den5,den6,factor0,factor1,factor2,factor9,factor10]
  ring

private theorem equation13 (p : Line) (s : State 14) (u hi lo : ℝ) (ok : regular p) :
    (3/50000000000)*10^12*((p.lm/2500) * ((50 * row12 p s u hi lo)) + ((p.ln)/2500) * ((50 * row13 p s u hi lo))) = (6/5)*((-1) * (s 3) + (1) * (s 5) + (-p.r/50) * ((50 * s 13))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ok
  dsimp only [row12,row13]
  field_simp [h0,h1,h2,h3,h4,h5,h6]
  simp only [den5,den6,factor0,factor1,factor2,factor9,factor10]
  ring

theorem flux (p : Line) (s : State 14) (u hi lo : ℝ) (ok : regular p) (i : Fin 14) :
    (3/50000000000)*action (metric p) (coordinates (rates p s u hi lo)) i =
      halfStep*action (network p) (coordinates s) i + port u (-hi+lo) i := by
  fin_cases i
  · simpa [action,Fin.sum_univ_succ,metric,mass,network,coordinates,rates,halfStep,port,mul_add,mul_assoc,add_assoc] using equation0 p s u hi lo ok
  · simpa [action,Fin.sum_univ_succ,metric,mass,network,coordinates,rates,halfStep,port,mul_add,mul_assoc,add_assoc] using equation1 p s u hi lo ok
  · simpa [action,Fin.sum_univ_succ,metric,mass,network,coordinates,rates,halfStep,port,mul_add,mul_assoc,add_assoc] using equation2 p s u hi lo ok
  · simpa [action,Fin.sum_univ_succ,metric,mass,network,coordinates,rates,halfStep,port,mul_add,mul_assoc,add_assoc] using equation3 p s u hi lo ok
  · simpa [action,Fin.sum_univ_succ,metric,mass,network,coordinates,rates,halfStep,port,mul_add,mul_assoc,add_assoc] using equation4 p s u hi lo ok
  · simpa [action,Fin.sum_univ_succ,metric,mass,network,coordinates,rates,halfStep,port,mul_add,mul_assoc,add_assoc] using equation5 p s u hi lo ok
  · simpa [action,Fin.sum_univ_succ,metric,mass,network,coordinates,rates,halfStep,port,mul_add,mul_assoc,add_assoc] using equation6 p s u hi lo ok
  · simpa [action,Fin.sum_univ_succ,metric,mass,network,coordinates,rates,halfStep,port,mul_add,mul_assoc,add_assoc] using equation7 p s u hi lo ok
  · simpa [action,Fin.sum_univ_succ,metric,mass,network,coordinates,rates,halfStep,port,mul_add,mul_assoc,add_assoc] using equation8 p s u hi lo ok
  · simpa [action,Fin.sum_univ_succ,metric,mass,network,coordinates,rates,halfStep,port,mul_add,mul_assoc,add_assoc] using equation9 p s u hi lo ok
  · simpa [action,Fin.sum_univ_succ,metric,mass,network,coordinates,rates,halfStep,port,mul_add,mul_assoc,add_assoc] using equation10 p s u hi lo ok
  · simpa [action,Fin.sum_univ_succ,metric,mass,network,coordinates,rates,halfStep,port,mul_add,mul_assoc,add_assoc] using equation11 p s u hi lo ok
  · simpa [action,Fin.sum_univ_succ,metric,mass,network,coordinates,rates,halfStep,port,mul_add,mul_assoc,add_assoc] using equation12 p s u hi lo ok
  · simpa [action,Fin.sum_univ_succ,metric,mass,network,coordinates,rates,halfStep,port,mul_add,mul_assoc,add_assoc] using equation13 p s u hi lo ok


open LineBounds Enclosed

def components (p : Components) : Line := ⟨p.cp.val, p.cn.val, p.cm.val, p.lp.val, p.ln.val, p.lm.val, p.via.val, p.ret.val, p.k.val, p.r.val⟩
private def e_factor0 (p : Components) : Enclosed := (p.lm * p.lm)
@[local simp] private theorem value_factor0 (p : Components) : (e_factor0 p).val = factor0 (components p) := by
  simp [e_factor0,factor0,components]
private def e_factor1 (p : Components) : Enclosed := (p.lp * p.ln)
@[local simp] private theorem value_factor1 (p : Components) : (e_factor1 p).val = factor1 (components p) := by
  simp [e_factor1,factor1,components]
private def e_factor2 (p : Components) : Enclosed := (p.ln * p.lp)
@[local simp] private theorem value_factor2 (p : Components) : (e_factor2 p).val = factor2 (components p) := by
  simp [e_factor2,factor2,components]
private def e_factor3 (p : Components) : Enclosed := (1 - p.k)
@[local simp] private theorem value_factor3 (p : Components) : (e_factor3 p).val = factor3 (components p) := by
  simp [e_factor3,factor3,components]
private def e_factor4 (p : Components) : Enclosed := (p.ln + p.via)
@[local simp] private theorem value_factor4 (p : Components) : (e_factor4 p).val = factor4 (components p) := by
  simp [e_factor4,factor4,components]
private def e_factor5 (p : Components) : Enclosed := (p.lp + p.via)
@[local simp] private theorem value_factor5 (p : Components) : (e_factor5 p).val = factor5 (components p) := by
  simp [e_factor5,factor5,components]
private def e_factor6 (p : Components) : Enclosed := ((1/2) * p.cm)
@[local simp] private theorem value_factor6 (p : Components) : (e_factor6 p).val = factor6 (components p) := by
  simp [e_factor6,factor6,components]
private def e_factor7 (p : Components) : Enclosed := (p.cn * (e_factor3 p))
@[local simp] private theorem value_factor7 (p : Components) : (e_factor7 p).val = factor7 (components p) := by
  simp [e_factor7,factor7,components]
private def e_factor8 (p : Components) : Enclosed := (p.cp * (e_factor3 p))
@[local simp] private theorem value_factor8 (p : Components) : (e_factor8 p).val = factor8 (components p) := by
  simp [e_factor8,factor8,components]
private def e_factor9 (p : Components) : Enclosed := ((e_factor1 p) - (e_factor0 p))
@[local simp] private theorem value_factor9 (p : Components) : (e_factor9 p).val = factor9 (components p) := by
  simp [e_factor9,factor9,components]
private def e_factor10 (p : Components) : Enclosed := ((e_factor2 p) - (e_factor0 p))
@[local simp] private theorem value_factor10 (p : Components) : (e_factor10 p).val = factor10 (components p) := by
  simp [e_factor10,factor10,components]
private def e_factor11 (p : Components) : Enclosed := ((1/2) * (e_factor7 p))
@[local simp] private theorem value_factor11 (p : Components) : (e_factor11 p).val = factor11 (components p) := by
  simp [e_factor11,factor11,components]
private def e_factor12 (p : Components) : Enclosed := ((1/2) * (e_factor8 p))
@[local simp] private theorem value_factor12 (p : Components) : (e_factor12 p).val = factor12 (components p) := by
  simp [e_factor12,factor12,components]
private def e_factor13 (p : Components) : Enclosed := ((e_factor6 p) + (e_factor6 p))
@[local simp] private theorem value_factor13 (p : Components) : (e_factor13 p).val = factor13 (components p) := by
  simp [e_factor13,factor13,components]
private def e_factor14 (p : Components) : Enclosed := ((e_factor11 p) + (1/400000000000))
@[local simp] private theorem value_factor14 (p : Components) : (e_factor14 p).val = factor14 (components p) := by
  simp [e_factor14,factor14,components]
private def e_factor15 (p : Components) : Enclosed := ((e_factor12 p) + (1/500000000000))
@[local simp] private theorem value_factor15 (p : Components) : (e_factor15 p).val = factor15 (components p) := by
  simp [e_factor15,factor15,components]
private def e_factor16 (p : Components) : Enclosed := ((e_factor12 p) * (e_factor11 p))
@[local simp] private theorem value_factor16 (p : Components) : (e_factor16 p).val = factor16 (components p) := by
  simp [e_factor16,factor16,components]
private def e_factor17 (p : Components) : Enclosed := ((e_factor12 p) + (e_factor11 p))
@[local simp] private theorem value_factor17 (p : Components) : (e_factor17 p).val = factor17 (components p) := by
  simp [e_factor17,factor17,components]
private def e_factor18 (p : Components) : Enclosed := ((e_factor12 p) + (e_factor12 p))
@[local simp] private theorem value_factor18 (p : Components) : (e_factor18 p).val = factor18 (components p) := by
  simp [e_factor18,factor18,components]
private def e_factor19 (p : Components) : Enclosed := ((e_factor11 p) + (e_factor11 p))
@[local simp] private theorem value_factor19 (p : Components) : (e_factor19 p).val = factor19 (components p) := by
  simp [e_factor19,factor19,components]
private def e_factor20 (p : Components) : Enclosed := ((e_factor6 p) * (e_factor17 p))
@[local simp] private theorem value_factor20 (p : Components) : (e_factor20 p).val = factor20 (components p) := by
  simp [e_factor20,factor20,components]
private def e_factor21 (p : Components) : Enclosed := ((e_factor15 p) * (e_factor14 p))
@[local simp] private theorem value_factor21 (p : Components) : (e_factor21 p).val = factor21 (components p) := by
  simp [e_factor21,factor21,components]
private def e_factor22 (p : Components) : Enclosed := ((e_factor15 p) + (e_factor14 p))
@[local simp] private theorem value_factor22 (p : Components) : (e_factor22 p).val = factor22 (components p) := by
  simp [e_factor22,factor22,components]
private def e_factor23 (p : Components) : Enclosed := ((e_factor18 p) + (e_factor13 p))
@[local simp] private theorem value_factor23 (p : Components) : (e_factor23 p).val = factor23 (components p) := by
  simp [e_factor23,factor23,components]
private def e_factor24 (p : Components) : Enclosed := ((e_factor19 p) + (e_factor13 p))
@[local simp] private theorem value_factor24 (p : Components) : (e_factor24 p).val = factor24 (components p) := by
  simp [e_factor24,factor24,components]
private def e_factor25 (p : Components) : Enclosed := ((e_factor6 p) * (e_factor22 p))
@[local simp] private theorem value_factor25 (p : Components) : (e_factor25 p).val = factor25 (components p) := by
  simp [e_factor25,factor25,components]
private def e_factor26 (p : Components) : Enclosed := ((e_factor19 p) * (e_factor18 p))
@[local simp] private theorem value_factor26 (p : Components) : (e_factor26 p).val = factor26 (components p) := by
  simp [e_factor26,factor26,components]
private def e_factor27 (p : Components) : Enclosed := ((e_factor19 p) + (e_factor18 p))
@[local simp] private theorem value_factor27 (p : Components) : (e_factor27 p).val = factor27 (components p) := by
  simp [e_factor27,factor27,components]
private def e_factor28 (p : Components) : Enclosed := ((e_factor16 p) + (e_factor20 p))
@[local simp] private theorem value_factor28 (p : Components) : (e_factor28 p).val = factor28 (components p) := by
  simp [e_factor28,factor28,components]
private def e_factor29 (p : Components) : Enclosed := ((e_factor13 p) * (e_factor27 p))
@[local simp] private theorem value_factor29 (p : Components) : (e_factor29 p).val = factor29 (components p) := by
  simp [e_factor29,factor29,components]
private def e_factor30 (p : Components) : Enclosed := ((e_factor21 p) + (e_factor25 p))
@[local simp] private theorem value_factor30 (p : Components) : (e_factor30 p).val = factor30 (components p) := by
  simp [e_factor30,factor30,components]
private def e_factor31 (p : Components) : Enclosed := ((e_factor26 p) + (e_factor29 p))
@[local simp] private theorem value_factor31 (p : Components) : (e_factor31 p).val = factor31 (components p) := by
  simp [e_factor31,factor31,components]
def e_den0 (p : Components) : Enclosed := (e_factor28 p)
@[local simp] private theorem value_den0 (p : Components) : (e_den0 p).val = den0 (components p) := by
  simp [e_den0,den0,components]
def e_den1 (p : Components) : Enclosed := (e_factor30 p)
@[local simp] private theorem value_den1 (p : Components) : (e_den1 p).val = den1 (components p) := by
  simp [e_den1,den1,components]
def e_den2 (p : Components) : Enclosed := (e_factor31 p)
@[local simp] private theorem value_den2 (p : Components) : (e_den2 p).val = den2 (components p) := by
  simp [e_den2,den2,components]
def e_den3 (p : Components) : Enclosed := (((e_factor5 p) * (e_factor4 p)) - (e_factor0 p))
@[local simp] private theorem value_den3 (p : Components) : (e_den3 p).val = den3 (components p) := by
  simp [e_den3,den3,components]
def e_den4 (p : Components) : Enclosed := (((e_factor4 p) * (e_factor5 p)) - (e_factor0 p))
@[local simp] private theorem value_den4 (p : Components) : (e_den4 p).val = den4 (components p) := by
  simp [e_den4,den4,components]
def e_den5 (p : Components) : Enclosed := (e_factor9 p)
@[local simp] private theorem value_den5 (p : Components) : (e_den5 p).val = den5 (components p) := by
  simp [e_den5,den5,components]
def e_den6 (p : Components) : Enclosed := (e_factor10 p)
@[local simp] private theorem value_den6 (p : Components) : (e_den6 p).val = den6 (components p) := by
  simp [e_den6,den6,components]
def regularCheck (p : Components) := (e_den0 p).positive && (e_den1 p).positive && (e_den2 p).positive && (e_den3 p).positive && (e_den4 p).positive && (e_den5 p).positive && (e_den6 p).positive
theorem regular_of_check (p : Components) (ok : regularCheck p) : regular (components p) := by
  simp only [regularCheck,Bool.and_eq_true] at ok
  simp only [regular]
  repeat' apply And.intro
  · exact (value_den0 p ▸ Enclosed.pos (x := e_den0 p) (by tauto)).ne'
  · exact (value_den1 p ▸ Enclosed.pos (x := e_den1 p) (by tauto)).ne'
  · exact (value_den2 p ▸ Enclosed.pos (x := e_den2 p) (by tauto)).ne'
  · exact (value_den3 p ▸ Enclosed.pos (x := e_den3 p) (by tauto)).ne'
  · exact (value_den4 p ▸ Enclosed.pos (x := e_den4 p) (by tauto)).ne'
  · exact (value_den5 p ▸ Enclosed.pos (x := e_den5 p) (by tauto)).ne'
  · exact (value_den6 p ▸ Enclosed.pos (x := e_den6 p) (by tauto)).ne'

def e_mass (p : Components) : Fin 14 → Fin 14 → Enclosed :=
  ![![(1/2)*(p.cp*(1-p.k)+p.cm), 0, -((1/2)*p.cm), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, (1/2)*(p.cp*(1-p.k)+p.cm)+(1/500000000000), 0, -((1/2)*p.cm), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-((1/2)*p.cm), 0, (1/2)*(p.cn*(1-p.k)+p.cm), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -((1/2)*p.cm), 0, (1/2)*(p.cn*(1-p.k)+p.cm)+(1/400000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1*(p.cn*(1-p.k)+p.cm), 0, -(1*p.cm), 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1*(p.cn*(1-p.k)+p.cm), 0, -(1*p.cm), 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -(1*p.cm), 0, 1*(p.cp*(1-p.k)+p.cm), 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, -(1*p.cm), 0, 1*(p.cp*(1-p.k)+p.cm), 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, (p.lp+p.via)/2500, p.lm/2500, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, p.lm/2500, (p.ln+p.via)/2500, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (p.lp)/2500, p.lm/2500, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, p.lm/2500, (p.ln)/2500, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (p.lp)/2500, p.lm/2500],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, p.lm/2500, (p.ln)/2500]]
@[simp] theorem value_mass (p : Components) (i j : Fin 14) : (e_mass p i j).val = mass (components p) i j := by
  fin_cases i <;> fin_cases j <;> simp [e_mass,mass,components]

def e_network (p : Components) : Fin 14 → Fin 14 → Enclosed :=
  ![![-50/28, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    ![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0],
    ![1, 0, 0, 0, 0, 0, -1, 0, -p.r/50, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, -1, 0, 0, 0, 0, -p.r/50, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, -1, 0, 0, -p.r/50, 0, 0, 0],
    ![0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, -p.r/50, 0, 0],
    ![0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -p.r/50, 0],
    ![0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -p.r/50]]
@[simp] theorem value_network (p : Components) (i j : Fin 14) : (e_network p i j).val = network (components p) i j := by
  fin_cases i <;> fin_cases j <;> simp [e_network,network,components]
def e_metric (p : Components) (i j : Fin 14) : Enclosed := 1000000000000*e_mass p i j
@[simp] theorem value_metric (p : Components) (i j) : (e_metric p i j).val = metric (components p) i j := by
  norm_num [e_metric,metric]
end
end SpiceSmtBench.Crosstalk
