import SpiceSmtBench.StitchedLine
import SpiceSmtBench.LineBounds

namespace SpiceSmtBench.Stitched
open StoredEnergy
noncomputable section
set_option maxRecDepth 20000
set_option linter.unusedVariables false in
section
private def factor0 (p : Line) : ℝ := (p.lm * p.lm)
private def factor1 (p : Line) : ℝ := (p.lp * p.ln)
private def factor2 (p : Line) : ℝ := (p.ln * p.lp)
private def factor3 (p : Line) : ℝ := (1 - p.k)
private def factor4 (p : Line) : ℝ := (p.ln + p.via)
private def factor5 (p : Line) : ℝ := (p.lp + p.via)
private def factor6 (p : Line) : ℝ := ((1/2) * p.cm)
private def factor7 (p : Line) : ℝ := (p.cp * (factor3 p))
private def factor8 (p : Line) : ℝ := (p.cn * (factor3 p))
private def factor9 (p : Line) : ℝ := (-(factor6 p))
private def factor10 (p : Line) : ℝ := ((factor1 p) - (factor0 p))
private def factor11 (p : Line) : ℝ := ((factor2 p) - (factor0 p))
private def factor12 (p : Line) : ℝ := ((1/2) * (factor7 p))
private def factor13 (p : Line) : ℝ := ((1/2) * (factor8 p))
private def factor14 (p : Line) : ℝ := (-(factor12 p))
private def factor15 (p : Line) : ℝ := (-(factor13 p))
private def factor16 (p : Line) : ℝ := ((factor6 p) + (factor6 p))
private def factor17 (p : Line) : ℝ := ((factor9 p) * (factor9 p))
private def factor18 (p : Line) : ℝ := ((factor13 p) + (factor6 p))
private def factor19 (p : Line) : ℝ := ((factor12 p) + (factor6 p))
private def factor20 (p : Line) : ℝ := ((factor14 p) * (factor9 p))
private def factor21 (p : Line) : ℝ := ((factor15 p) * (factor9 p))
private def factor22 (p : Line) : ℝ := ((factor12 p) + (factor12 p))
private def factor23 (p : Line) : ℝ := ((factor13 p) + (factor13 p))
private def factor24 (p : Line) : ℝ := ((factor13 p) + (factor12 p))
private def factor25 (p : Line) : ℝ := ((factor13 p) * (factor12 p))
private def factor26 (p : Line) : ℝ := ((factor15 p) * (factor14 p))
private def factor27 (p : Line) : ℝ := ((3/2000000000000) + (factor24 p))
private def factor28 (p : Line) : ℝ := ((factor6 p) * (factor24 p))
private def factor29 (p : Line) : ℝ := ((factor15 p) * (factor19 p))
private def factor30 (p : Line) : ℝ := ((factor18 p) * (factor14 p))
private def factor31 (p : Line) : ℝ := ((factor22 p) + (factor16 p))
private def factor32 (p : Line) : ℝ := ((factor23 p) + (factor16 p))
private def factor33 (p : Line) : ℝ := ((factor18 p) * (factor19 p))
private def factor34 (p : Line) : ℝ := ((factor27 p) * (factor9 p))
private def factor35 (p : Line) : ℝ := ((factor23 p) * (factor22 p))
private def factor36 (p : Line) : ℝ := ((factor23 p) + (factor22 p))
private def factor37 (p : Line) : ℝ := ((factor20 p) - (factor29 p))
private def factor38 (p : Line) : ℝ := ((factor21 p) - (factor30 p))
private def factor39 (p : Line) : ℝ := ((factor33 p) - (factor17 p))
private def factor40 (p : Line) : ℝ := ((factor25 p) + (factor28 p))
private def factor41 (p : Line) : ℝ := ((factor16 p) * (factor36 p))
private def factor42 (p : Line) : ℝ := ((factor26 p) - (factor34 p))
private def factor43 (p : Line) : ℝ := ((factor15 p) * (factor37 p))
private def factor44 (p : Line) : ℝ := ((factor14 p) * (factor38 p))
private def factor45 (p : Line) : ℝ := ((factor27 p) * (factor39 p))
private def factor46 (p : Line) : ℝ := ((factor35 p) + (factor41 p))
private def factor47 (p : Line) : ℝ := ((factor43 p) + (factor44 p))
private def factor48 (p : Line) : ℝ := ((factor45 p) + (factor47 p))
def den0 (p : Line) : ℝ := (factor46 p)
def den1 (p : Line) : ℝ := (factor48 p)
def den2 (p : Line) : ℝ := (factor40 p)
def den3 (p : Line) : ℝ := (((factor5 p) * (factor4 p)) - (factor0 p))
def den4 (p : Line) : ℝ := (((factor4 p) * (factor5 p)) - (factor0 p))
def den5 (p : Line) : ℝ := (factor10 p)
def den6 (p : Line) : ℝ := (factor11 p)
def den7 (p : Line) : ℝ := p.ret
private def row0 (p : Line) (s : State 16) (u hi lo : ℝ) : ℝ := ((((factor31 p) * ((s 10) - (s 12))) + ((factor16 p) * ((s 9) - (s 11)))) / (den0 p))
private def row1 (p : Line) (s : State 16) (u hi lo : ℝ) : ℝ := ((((factor31 p) * ((s 12) - (s 14))) + ((factor16 p) * ((s 11) - (s 13)))) / (den0 p))
private def row2 (p : Line) (s : State 16) (u hi lo : ℝ) : ℝ := ((((factor32 p) * ((s 9) - (s 11))) + ((factor16 p) * ((s 10) - (s 12)))) / (den0 p))
private def row3 (p : Line) (s : State 16) (u hi lo : ℝ) : ℝ := ((((factor32 p) * ((s 11) - (s 13))) + ((factor16 p) * ((s 12) - (s 14)))) / (den0 p))
private def row4 (p : Line) (s : State 16) (u hi lo : ℝ) : ℝ := ((((factor39 p) * (((s 15) + (((s 8) - (s 4)) / 50)) + (((s 7) - (s 4)) / 50))) + (((factor37 p) * ((s 14) - (((s 7) - (s 4)) / 50))) + ((factor38 p) * ((s 13) - (((s 8) - (s 4)) / 50))))) / (den1 p))
private def row5 (p : Line) (s : State 16) (u hi lo : ℝ) : ℝ := ((((factor19 p) * (((((-1) * u) - (s 5)) / 25) - (s 10))) + ((factor6 p) * (((u - (s 6)) / 25) - (s 9)))) / (den2 p))
private def row6 (p : Line) (s : State 16) (u hi lo : ℝ) : ℝ := ((((factor18 p) * (((u - (s 6)) / 25) - (s 9))) + ((factor6 p) * (((((-1) * u) - (s 5)) / 25) - (s 10)))) / (den2 p))
private def row7 (p : Line) (s : State 16) (u hi lo : ℝ) : ℝ := ((((factor37 p) * (((s 15) + (((s 8) - (s 4)) / 50)) + (((s 7) - (s 4)) / 50))) + (((((factor27 p) * (factor19 p)) - ((factor14 p) * (factor14 p))) * ((s 14) - (((s 7) - (s 4)) / 50))) + ((factor42 p) * ((s 13) - (((s 8) - (s 4)) / 50))))) / (den1 p))
private def row8 (p : Line) (s : State 16) (u hi lo : ℝ) : ℝ := ((((factor38 p) * (((s 15) + (((s 8) - (s 4)) / 50)) + (((s 7) - (s 4)) / 50))) + (((factor42 p) * ((s 14) - (((s 7) - (s 4)) / 50))) + ((((factor27 p) * (factor18 p)) - ((factor15 p) * (factor15 p))) * ((s 13) - (((s 8) - (s 4)) / 50))))) / (den1 p))
private def row9 (p : Line) (s : State 16) (u hi lo : ℝ) : ℝ := ((((factor4 p) * (((s 6) - (s 2)) - (p.r * (s 9)))) - (p.lm * (((s 5) - (s 0)) - (p.r * (s 10))))) / (den3 p))
private def row10 (p : Line) (s : State 16) (u hi lo : ℝ) : ℝ := ((((factor5 p) * (((s 5) - (s 0)) - (p.r * (s 10)))) - (p.lm * (((s 6) - (s 2)) - (p.r * (s 9))))) / (den4 p))
private def row11 (p : Line) (s : State 16) (u hi lo : ℝ) : ℝ := (((p.ln * (((s 2) - (s 3)) - (p.r * (s 11)))) - (p.lm * (((s 0) - (s 1)) - (p.r * (s 12))))) / (den5 p))
private def row12 (p : Line) (s : State 16) (u hi lo : ℝ) : ℝ := (((p.lp * (((s 0) - (s 1)) - (p.r * (s 12)))) - (p.lm * (((s 2) - (s 3)) - (p.r * (s 11))))) / (den6 p))
private def row13 (p : Line) (s : State 16) (u hi lo : ℝ) : ℝ := (((p.ln * (((s 3) - (s 8)) - (p.r * (s 13)))) - (p.lm * (((s 1) - (s 7)) - (p.r * (s 14))))) / (den5 p))
private def row14 (p : Line) (s : State 16) (u hi lo : ℝ) : ℝ := (((p.lp * (((s 1) - (s 7)) - (p.r * (s 14)))) - (p.lm * (((s 3) - (s 8)) - (p.r * (s 13))))) / (den6 p))
private def row15 (p : Line) (s : State 16) (u hi lo : ℝ) : ℝ := (((-(s 4)) - ((1/100) * (s 15))) / (den7 p))
end
def rates (p : Line) (s : State 16) (u hi lo : ℝ) : State 16 :=
  ![row0 p s u hi lo, row1 p s u hi lo, row2 p s u hi lo, row3 p s u hi lo, row4 p s u hi lo, row5 p s u hi lo, row6 p s u hi lo, row7 p s u hi lo, row8 p s u hi lo, row9 p s u hi lo, row10 p s u hi lo, row11 p s u hi lo, row12 p s u hi lo, row13 p s u hi lo, row14 p s u hi lo, row15 p s u hi lo]
def regular (p : Line) := den0 p ≠ 0 ∧ den1 p ≠ 0 ∧ den2 p ≠ 0 ∧ den3 p ≠ 0 ∧ den4 p ≠ 0 ∧ den5 p ≠ 0 ∧ den6 p ≠ 0 ∧ den7 p ≠ 0
private theorem equation0 (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) :
    (1/200000000000)*10^12*((1*(p.cn*(1-p.k)+p.cm)) * (row0 p s u hi lo) + (-(1*p.cm)) * (row2 p s u hi lo)) = (1/10)*((1) * ((50 * s 10)) + (-1) * ((50 * s 12))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok
  dsimp only [row0,row2]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [den0,factor3,factor6,factor7,factor8,factor12,factor13,factor16,factor22,factor23,factor31,factor32,factor35,factor36,factor41,factor46]
  ring

private theorem equation1 (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) :
    (1/200000000000)*10^12*((1*(p.cn*(1-p.k)+p.cm)) * (row1 p s u hi lo) + (-(1*p.cm)) * (row3 p s u hi lo)) = (1/10)*((1) * ((50 * s 12)) + (-1) * ((50 * s 14))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok
  dsimp only [row1,row3]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [den0,factor3,factor6,factor7,factor8,factor12,factor13,factor16,factor22,factor23,factor31,factor32,factor35,factor36,factor41,factor46]
  ring

private theorem equation2 (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) :
    (1/200000000000)*10^12*((-(1*p.cm)) * (row0 p s u hi lo) + (1*(p.cp*(1-p.k)+p.cm)) * (row2 p s u hi lo)) = (1/10)*((1) * ((50 * s 9)) + (-1) * ((50 * s 11))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok
  dsimp only [row0,row2]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [den0,factor3,factor6,factor7,factor8,factor12,factor13,factor16,factor22,factor23,factor31,factor32,factor35,factor36,factor41,factor46]
  ring

private theorem equation3 (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) :
    (1/200000000000)*10^12*((-(1*p.cm)) * (row1 p s u hi lo) + (1*(p.cp*(1-p.k)+p.cm)) * (row3 p s u hi lo)) = (1/10)*((1) * ((50 * s 11)) + (-1) * ((50 * s 13))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok
  dsimp only [row1,row3]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [den0,factor3,factor6,factor7,factor8,factor12,factor13,factor16,factor22,factor23,factor31,factor32,factor35,factor36,factor41,factor46]
  ring

private theorem equation4 (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) :
    (1/200000000000)*10^12*((3/2000000000000) * (row4 p s u hi lo)) = (1/10)*((1) * ((50 * s 13)) + (1) * ((50 * s 14)) + (1) * ((50 * s 15))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok
  dsimp only [row4]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [den1,factor3,factor6,factor7,factor8,factor9,factor12,factor13,factor14,factor15,factor17,factor18,factor19,factor20,factor21,factor24,factor27,factor29,factor30,factor33,factor37,factor38,factor39,factor43,factor44,factor45,factor47,factor48]
  ring

private theorem equation5 (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) :
    (1/200000000000)*10^12*(((1/2)*(p.cn*(1-p.k)+p.cm)) * (row5 p s u hi lo) + (-((1/2)*p.cm)) * (row6 p s u hi lo)) = (1/10)*((-2) * (s 5) + (-1) * ((50 * s 10))) + -(1/10)*2*u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok
  dsimp only [row5,row6]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [den2,factor3,factor6,factor7,factor8,factor12,factor13,factor18,factor19,factor24,factor25,factor28,factor40]
  ring

private theorem equation6 (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) :
    (1/200000000000)*10^12*((-((1/2)*p.cm)) * (row5 p s u hi lo) + ((1/2)*(p.cp*(1-p.k)+p.cm)) * (row6 p s u hi lo)) = (1/10)*((-2) * (s 6) + (-1) * ((50 * s 9))) + (1/10)*2*u := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok
  dsimp only [row5,row6]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [den2,factor3,factor6,factor7,factor8,factor12,factor13,factor18,factor19,factor24,factor25,factor28,factor40]
  ring

private theorem equation7 (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) :
    (1/200000000000)*10^12*(((1/2)*(p.cn*(1-p.k)+p.cm)) * ((row7 p s u hi lo-row4 p s u hi lo)) + (-((1/2)*p.cm)) * ((row8 p s u hi lo-row4 p s u hi lo))) = (1/10)*((-1) * ((s 7-s 4)) + (1) * ((50 * s 14))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok
  dsimp only [row4,row7,row8]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [den1,factor3,factor6,factor7,factor8,factor9,factor12,factor13,factor14,factor15,factor17,factor18,factor19,factor20,factor21,factor24,factor26,factor27,factor29,factor30,factor33,factor34,factor37,factor38,factor39,factor42,factor43,factor44,factor45,factor47,factor48]
  ring

private theorem equation8 (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) :
    (1/200000000000)*10^12*((-((1/2)*p.cm)) * ((row7 p s u hi lo-row4 p s u hi lo)) + ((1/2)*(p.cp*(1-p.k)+p.cm)) * ((row8 p s u hi lo-row4 p s u hi lo))) = (1/10)*((-1) * ((s 8-s 4)) + (1) * ((50 * s 13))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok
  dsimp only [row4,row7,row8]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [den1,factor3,factor6,factor7,factor8,factor9,factor12,factor13,factor14,factor15,factor17,factor18,factor19,factor20,factor21,factor24,factor26,factor27,factor29,factor30,factor33,factor34,factor37,factor38,factor39,factor42,factor43,factor44,factor45,factor47,factor48]
  ring

private theorem equation9 (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) :
    (1/200000000000)*10^12*(((p.lp+p.via)/2500) * ((50 * row9 p s u hi lo)) + (p.lm/2500) * ((50 * row10 p s u hi lo))) = (1/10)*((-1) * (s 2) + (1) * (s 6) + (-p.r/50) * ((50 * s 9))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok
  dsimp only [row9,row10]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [den3,den4,factor0,factor4,factor5]
  ring

private theorem equation10 (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) :
    (1/200000000000)*10^12*((p.lm/2500) * ((50 * row9 p s u hi lo)) + ((p.ln+p.via)/2500) * ((50 * row10 p s u hi lo))) = (1/10)*((-1) * (s 0) + (1) * (s 5) + (-p.r/50) * ((50 * s 10))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok
  dsimp only [row9,row10]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [den3,den4,factor0,factor4,factor5]
  ring

private theorem equation11 (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) :
    (1/200000000000)*10^12*(((p.lp)/2500) * ((50 * row11 p s u hi lo)) + (p.lm/2500) * ((50 * row12 p s u hi lo))) = (1/10)*((1) * (s 2) + (-1) * (s 3) + (-p.r/50) * ((50 * s 11))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok
  dsimp only [row11,row12]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [den5,den6,factor0,factor1,factor2,factor10,factor11]
  ring

private theorem equation12 (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) :
    (1/200000000000)*10^12*((p.lm/2500) * ((50 * row11 p s u hi lo)) + ((p.ln)/2500) * ((50 * row12 p s u hi lo))) = (1/10)*((1) * (s 0) + (-1) * (s 1) + (-p.r/50) * ((50 * s 12))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok
  dsimp only [row11,row12]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [den5,den6,factor0,factor1,factor2,factor10,factor11]
  ring

private theorem equation13 (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) :
    (1/200000000000)*10^12*(((p.lp)/2500) * ((50 * row13 p s u hi lo)) + (p.lm/2500) * ((50 * row14 p s u hi lo))) = (1/10)*((1) * (s 3) + (-1) * (s 4) + (-1) * ((s 8-s 4)) + (-p.r/50) * ((50 * s 13))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok
  dsimp only [row13,row14]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [den5,den6,factor0,factor1,factor2,factor10,factor11]
  ring

private theorem equation14 (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) :
    (1/200000000000)*10^12*((p.lm/2500) * ((50 * row13 p s u hi lo)) + ((p.ln)/2500) * ((50 * row14 p s u hi lo))) = (1/10)*((1) * (s 1) + (-1) * (s 4) + (-1) * ((s 7-s 4)) + (-p.r/50) * ((50 * s 14))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok
  dsimp only [row13,row14]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [den5,den6,factor0,factor1,factor2,factor10,factor11]
  ring

private theorem equation15 (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) :
    (1/200000000000)*10^12*((p.ret/2500) * ((50 * row15 p s u hi lo))) = (1/10)*((-1) * (s 4) + (-1/5000) * ((50 * s 15))) + 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ok
  dsimp only [row15]
  field_simp [h0,h1,h2,h3,h4,h5,h6,h7]
  simp only [den7]
  ring

theorem flux (p : Line) (s : State 16) (u hi lo : ℝ) (ok : regular p) (i : Fin 16) :
    (1/200000000000)*action (metric p) (coordinates (rates p s u hi lo)) i =
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
  · simpa [action,Fin.sum_univ_succ,metric,mass,network,coordinates,rates,halfStep,port,mul_add,mul_assoc,add_assoc] using equation14 p s u hi lo ok
  · simpa [action,Fin.sum_univ_succ,metric,mass,network,coordinates,rates,halfStep,port,mul_add,mul_assoc,add_assoc] using equation15 p s u hi lo ok


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
private def e_factor7 (p : Components) : Enclosed := (p.cp * (e_factor3 p))
@[local simp] private theorem value_factor7 (p : Components) : (e_factor7 p).val = factor7 (components p) := by
  simp [e_factor7,factor7,components]
private def e_factor8 (p : Components) : Enclosed := (p.cn * (e_factor3 p))
@[local simp] private theorem value_factor8 (p : Components) : (e_factor8 p).val = factor8 (components p) := by
  simp [e_factor8,factor8,components]
private def e_factor9 (p : Components) : Enclosed := (-(e_factor6 p))
@[local simp] private theorem value_factor9 (p : Components) : (e_factor9 p).val = factor9 (components p) := by
  simp [e_factor9,factor9,components]
private def e_factor10 (p : Components) : Enclosed := ((e_factor1 p) - (e_factor0 p))
@[local simp] private theorem value_factor10 (p : Components) : (e_factor10 p).val = factor10 (components p) := by
  simp [e_factor10,factor10,components]
private def e_factor11 (p : Components) : Enclosed := ((e_factor2 p) - (e_factor0 p))
@[local simp] private theorem value_factor11 (p : Components) : (e_factor11 p).val = factor11 (components p) := by
  simp [e_factor11,factor11,components]
private def e_factor12 (p : Components) : Enclosed := ((1/2) * (e_factor7 p))
@[local simp] private theorem value_factor12 (p : Components) : (e_factor12 p).val = factor12 (components p) := by
  simp [e_factor12,factor12,components]
private def e_factor13 (p : Components) : Enclosed := ((1/2) * (e_factor8 p))
@[local simp] private theorem value_factor13 (p : Components) : (e_factor13 p).val = factor13 (components p) := by
  simp [e_factor13,factor13,components]
private def e_factor14 (p : Components) : Enclosed := (-(e_factor12 p))
@[local simp] private theorem value_factor14 (p : Components) : (e_factor14 p).val = factor14 (components p) := by
  simp [e_factor14,factor14,components]
private def e_factor15 (p : Components) : Enclosed := (-(e_factor13 p))
@[local simp] private theorem value_factor15 (p : Components) : (e_factor15 p).val = factor15 (components p) := by
  simp [e_factor15,factor15,components]
private def e_factor16 (p : Components) : Enclosed := ((e_factor6 p) + (e_factor6 p))
@[local simp] private theorem value_factor16 (p : Components) : (e_factor16 p).val = factor16 (components p) := by
  simp [e_factor16,factor16,components]
private def e_factor17 (p : Components) : Enclosed := ((e_factor9 p) * (e_factor9 p))
@[local simp] private theorem value_factor17 (p : Components) : (e_factor17 p).val = factor17 (components p) := by
  simp [e_factor17,factor17,components]
private def e_factor18 (p : Components) : Enclosed := ((e_factor13 p) + (e_factor6 p))
@[local simp] private theorem value_factor18 (p : Components) : (e_factor18 p).val = factor18 (components p) := by
  simp [e_factor18,factor18,components]
private def e_factor19 (p : Components) : Enclosed := ((e_factor12 p) + (e_factor6 p))
@[local simp] private theorem value_factor19 (p : Components) : (e_factor19 p).val = factor19 (components p) := by
  simp [e_factor19,factor19,components]
private def e_factor20 (p : Components) : Enclosed := ((e_factor14 p) * (e_factor9 p))
@[local simp] private theorem value_factor20 (p : Components) : (e_factor20 p).val = factor20 (components p) := by
  simp [e_factor20,factor20,components]
private def e_factor21 (p : Components) : Enclosed := ((e_factor15 p) * (e_factor9 p))
@[local simp] private theorem value_factor21 (p : Components) : (e_factor21 p).val = factor21 (components p) := by
  simp [e_factor21,factor21,components]
private def e_factor22 (p : Components) : Enclosed := ((e_factor12 p) + (e_factor12 p))
@[local simp] private theorem value_factor22 (p : Components) : (e_factor22 p).val = factor22 (components p) := by
  simp [e_factor22,factor22,components]
private def e_factor23 (p : Components) : Enclosed := ((e_factor13 p) + (e_factor13 p))
@[local simp] private theorem value_factor23 (p : Components) : (e_factor23 p).val = factor23 (components p) := by
  simp [e_factor23,factor23,components]
private def e_factor24 (p : Components) : Enclosed := ((e_factor13 p) + (e_factor12 p))
@[local simp] private theorem value_factor24 (p : Components) : (e_factor24 p).val = factor24 (components p) := by
  simp [e_factor24,factor24,components]
private def e_factor25 (p : Components) : Enclosed := ((e_factor13 p) * (e_factor12 p))
@[local simp] private theorem value_factor25 (p : Components) : (e_factor25 p).val = factor25 (components p) := by
  simp [e_factor25,factor25,components]
private def e_factor26 (p : Components) : Enclosed := ((e_factor15 p) * (e_factor14 p))
@[local simp] private theorem value_factor26 (p : Components) : (e_factor26 p).val = factor26 (components p) := by
  simp [e_factor26,factor26,components]
private def e_factor27 (p : Components) : Enclosed := ((3/2000000000000) + (e_factor24 p))
@[local simp] private theorem value_factor27 (p : Components) : (e_factor27 p).val = factor27 (components p) := by
  simp [e_factor27,factor27,components]
private def e_factor28 (p : Components) : Enclosed := ((e_factor6 p) * (e_factor24 p))
@[local simp] private theorem value_factor28 (p : Components) : (e_factor28 p).val = factor28 (components p) := by
  simp [e_factor28,factor28,components]
private def e_factor29 (p : Components) : Enclosed := ((e_factor15 p) * (e_factor19 p))
@[local simp] private theorem value_factor29 (p : Components) : (e_factor29 p).val = factor29 (components p) := by
  simp [e_factor29,factor29,components]
private def e_factor30 (p : Components) : Enclosed := ((e_factor18 p) * (e_factor14 p))
@[local simp] private theorem value_factor30 (p : Components) : (e_factor30 p).val = factor30 (components p) := by
  simp [e_factor30,factor30,components]
private def e_factor31 (p : Components) : Enclosed := ((e_factor22 p) + (e_factor16 p))
@[local simp] private theorem value_factor31 (p : Components) : (e_factor31 p).val = factor31 (components p) := by
  simp [e_factor31,factor31,components]
private def e_factor32 (p : Components) : Enclosed := ((e_factor23 p) + (e_factor16 p))
@[local simp] private theorem value_factor32 (p : Components) : (e_factor32 p).val = factor32 (components p) := by
  simp [e_factor32,factor32,components]
private def e_factor33 (p : Components) : Enclosed := ((e_factor18 p) * (e_factor19 p))
@[local simp] private theorem value_factor33 (p : Components) : (e_factor33 p).val = factor33 (components p) := by
  simp [e_factor33,factor33,components]
private def e_factor34 (p : Components) : Enclosed := ((e_factor27 p) * (e_factor9 p))
@[local simp] private theorem value_factor34 (p : Components) : (e_factor34 p).val = factor34 (components p) := by
  simp [e_factor34,factor34,components]
private def e_factor35 (p : Components) : Enclosed := ((e_factor23 p) * (e_factor22 p))
@[local simp] private theorem value_factor35 (p : Components) : (e_factor35 p).val = factor35 (components p) := by
  simp [e_factor35,factor35,components]
private def e_factor36 (p : Components) : Enclosed := ((e_factor23 p) + (e_factor22 p))
@[local simp] private theorem value_factor36 (p : Components) : (e_factor36 p).val = factor36 (components p) := by
  simp [e_factor36,factor36,components]
private def e_factor37 (p : Components) : Enclosed := ((e_factor20 p) - (e_factor29 p))
@[local simp] private theorem value_factor37 (p : Components) : (e_factor37 p).val = factor37 (components p) := by
  simp [e_factor37,factor37,components]
private def e_factor38 (p : Components) : Enclosed := ((e_factor21 p) - (e_factor30 p))
@[local simp] private theorem value_factor38 (p : Components) : (e_factor38 p).val = factor38 (components p) := by
  simp [e_factor38,factor38,components]
private def e_factor39 (p : Components) : Enclosed := ((e_factor33 p) - (e_factor17 p))
@[local simp] private theorem value_factor39 (p : Components) : (e_factor39 p).val = factor39 (components p) := by
  simp [e_factor39,factor39,components]
private def e_factor40 (p : Components) : Enclosed := ((e_factor25 p) + (e_factor28 p))
@[local simp] private theorem value_factor40 (p : Components) : (e_factor40 p).val = factor40 (components p) := by
  simp [e_factor40,factor40,components]
private def e_factor41 (p : Components) : Enclosed := ((e_factor16 p) * (e_factor36 p))
@[local simp] private theorem value_factor41 (p : Components) : (e_factor41 p).val = factor41 (components p) := by
  simp [e_factor41,factor41,components]
private def e_factor42 (p : Components) : Enclosed := ((e_factor26 p) - (e_factor34 p))
@[local simp] private theorem value_factor42 (p : Components) : (e_factor42 p).val = factor42 (components p) := by
  simp [e_factor42,factor42,components]
private def e_factor43 (p : Components) : Enclosed := ((e_factor15 p) * (e_factor37 p))
@[local simp] private theorem value_factor43 (p : Components) : (e_factor43 p).val = factor43 (components p) := by
  simp [e_factor43,factor43,components]
private def e_factor44 (p : Components) : Enclosed := ((e_factor14 p) * (e_factor38 p))
@[local simp] private theorem value_factor44 (p : Components) : (e_factor44 p).val = factor44 (components p) := by
  simp [e_factor44,factor44,components]
private def e_factor45 (p : Components) : Enclosed := ((e_factor27 p) * (e_factor39 p))
@[local simp] private theorem value_factor45 (p : Components) : (e_factor45 p).val = factor45 (components p) := by
  simp [e_factor45,factor45,components]
private def e_factor46 (p : Components) : Enclosed := ((e_factor35 p) + (e_factor41 p))
@[local simp] private theorem value_factor46 (p : Components) : (e_factor46 p).val = factor46 (components p) := by
  simp [e_factor46,factor46,components]
private def e_factor47 (p : Components) : Enclosed := ((e_factor43 p) + (e_factor44 p))
@[local simp] private theorem value_factor47 (p : Components) : (e_factor47 p).val = factor47 (components p) := by
  simp [e_factor47,factor47,components]
private def e_factor48 (p : Components) : Enclosed := ((e_factor45 p) + (e_factor47 p))
@[local simp] private theorem value_factor48 (p : Components) : (e_factor48 p).val = factor48 (components p) := by
  simp [e_factor48,factor48,components]
def e_den0 (p : Components) : Enclosed := (e_factor46 p)
@[local simp] private theorem value_den0 (p : Components) : (e_den0 p).val = den0 (components p) := by
  simp [e_den0,den0,components]
def e_den1 (p : Components) : Enclosed := (e_factor48 p)
@[local simp] private theorem value_den1 (p : Components) : (e_den1 p).val = den1 (components p) := by
  simp [e_den1,den1,components]
def e_den2 (p : Components) : Enclosed := (e_factor40 p)
@[local simp] private theorem value_den2 (p : Components) : (e_den2 p).val = den2 (components p) := by
  simp [e_den2,den2,components]
def e_den3 (p : Components) : Enclosed := (((e_factor5 p) * (e_factor4 p)) - (e_factor0 p))
@[local simp] private theorem value_den3 (p : Components) : (e_den3 p).val = den3 (components p) := by
  simp [e_den3,den3,components]
def e_den4 (p : Components) : Enclosed := (((e_factor4 p) * (e_factor5 p)) - (e_factor0 p))
@[local simp] private theorem value_den4 (p : Components) : (e_den4 p).val = den4 (components p) := by
  simp [e_den4,den4,components]
def e_den5 (p : Components) : Enclosed := (e_factor10 p)
@[local simp] private theorem value_den5 (p : Components) : (e_den5 p).val = den5 (components p) := by
  simp [e_den5,den5,components]
def e_den6 (p : Components) : Enclosed := (e_factor11 p)
@[local simp] private theorem value_den6 (p : Components) : (e_den6 p).val = den6 (components p) := by
  simp [e_den6,den6,components]
def e_den7 (p : Components) : Enclosed := p.ret
@[local simp] private theorem value_den7 (p : Components) : (e_den7 p).val = den7 (components p) := by
  simp [e_den7,den7,components]
def regularCheck (p : Components) := (e_den0 p).positive && (e_den1 p).positive && (e_den2 p).positive && (e_den3 p).positive && (e_den4 p).positive && (e_den5 p).positive && (e_den6 p).positive && (e_den7 p).positive
theorem regular_of_check (p : Components) (ok : regularCheck p) : regular (components p) := by
  simp only [regularCheck,Bool.and_eq_true] at ok
  simp only [regular]
  repeat' apply And.intro
  · exact (value_den0 p ▸ Enclosed.pos (x := e_den0 p) ok.1.1.1.1.1.1.1).ne'
  · exact (value_den1 p ▸ Enclosed.pos (x := e_den1 p) ok.1.1.1.1.1.1.2).ne'
  · exact (value_den2 p ▸ Enclosed.pos (x := e_den2 p) ok.1.1.1.1.1.2).ne'
  · exact (value_den3 p ▸ Enclosed.pos (x := e_den3 p) ok.1.1.1.1.2).ne'
  · exact (value_den4 p ▸ Enclosed.pos (x := e_den4 p) ok.1.1.1.2).ne'
  · exact (value_den5 p ▸ Enclosed.pos (x := e_den5 p) ok.1.1.2).ne'
  · exact (value_den6 p ▸ Enclosed.pos (x := e_den6 p) ok.1.2).ne'
  · exact (value_den7 p ▸ Enclosed.pos (x := e_den7 p) ok.2).ne'

def e_mass (p : Components) : Fin 16 → Fin 16 → Enclosed :=
  ![![1*(p.cn*(1-p.k)+p.cm), 0, -(1*p.cm), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1*(p.cn*(1-p.k)+p.cm), 0, -(1*p.cm), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-(1*p.cm), 0, 1*(p.cp*(1-p.k)+p.cm), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -(1*p.cm), 0, 1*(p.cp*(1-p.k)+p.cm), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 3/2000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, (1/2)*(p.cn*(1-p.k)+p.cm), -((1/2)*p.cm), 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, -((1/2)*p.cm), (1/2)*(p.cp*(1-p.k)+p.cm), 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, (1/2)*(p.cn*(1-p.k)+p.cm), -((1/2)*p.cm), 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -((1/2)*p.cm), (1/2)*(p.cp*(1-p.k)+p.cm), 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, (p.lp+p.via)/2500, p.lm/2500, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, p.lm/2500, (p.ln+p.via)/2500, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (p.lp)/2500, p.lm/2500, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, p.lm/2500, (p.ln)/2500, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (p.lp)/2500, p.lm/2500, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, p.lm/2500, (p.ln)/2500, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, p.ret/2500]]
set_option maxHeartbeats 600000 in
@[simp] theorem value_mass (p : Components) (i j : Fin 16) : (e_mass p i j).val = mass (components p) i j := by
  fin_cases i <;> fin_cases j <;> simp [e_mass,mass,components]

def e_network (p : Components) : Fin 16 → Fin 16 → Enclosed :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, -1, 0, 0, 0, 1, 0, 0, -p.r/50, 0, 0, 0, 0, 0, 0],
    ![-1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -p.r/50, 0, 0, 0, 0, 0],
    ![0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, -p.r/50, 0, 0, 0, 0],
    ![1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -p.r/50, 0, 0, 0],
    ![0, 0, 0, 1, -1, 0, 0, 0, -1, 0, 0, 0, 0, -p.r/50, 0, 0],
    ![0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -p.r/50, 0],
    ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1/5000]]
set_option maxHeartbeats 400000 in
@[simp] theorem value_network (p : Components) (i j : Fin 16) : (e_network p i j).val = network (components p) i j := by
  fin_cases i <;> fin_cases j <;> simp [e_network,network,components]
def e_metric (p : Components) (i j : Fin 16) : Enclosed := 1000000000000*e_mass p i j
@[simp] theorem value_metric (p : Components) (i j) : (e_metric p i j).val = metric (components p) i j := by
  norm_num [e_metric,metric]
end
end SpiceSmtBench.Stitched
