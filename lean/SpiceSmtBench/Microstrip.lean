import SpiceSmtBench.Enclosed

namespace SpiceSmtBench.Microstrip
open Enclosed

noncomputable section

structure Geometry where
  width : Enclosed
  length : Enclosed
  resistanceFactor : Enclosed
  rootLo : ℚ
  rootHi : ℚ

def impedanceConstant := fraction 7539822368615503 20000000000000
def lightSpeed := integer 299792458
def thickness := log (fraction 1142857142857143 200000000000000)
def aspect (g : Geometry) (t : Enclosed) :=
  (g.width + fraction 348151438013521 31250000000000000000 * (integer 1+t)) / fraction 1 10000
def rootArg (g : Geometry) := integer 1 + integer 12 / aspect g thickness
def root (g : Geometry) := sqrt (rootArg g) g.rootLo g.rootHi
def wideArg (g : Geometry) := aspect g thickness + fraction 361 250
def shape (g : Geometry) := aspect g thickness + fraction 1393 1000 + fraction 667 1000 * log (wideArg g)
def effective (g : Geometry) (er : Enclosed) := (er+integer 1)/integer 2 + (er-integer 1)/(integer 2*root g)
def inductance (g : Geometry) := g.length * impedanceConstant / shape g / lightSpeed
def capacitance (g : Geometry) (er : Enclosed) :=
  g.length * effective g er * shape g / lightSpeed / impedanceConstant
def resistance (g : Geometry) := g.length/g.resistanceFactor

/-- Recover the physical line constants from the implicit logarithm, square
root and impedance equations of a single microstrip section. -/
theorem identify (g : Geometry) (er : Enclosed) (t su ee se wl z L C R : ℝ)
    (good : 0 < (rootArg g).val ∧ 0 < (wideArg g).val ∧ 0 < (shape g).val ∧
      0 < g.resistanceFactor.val ∧ 0 < (effective g er).val)
    (logt : Real.exp t = (fraction 1142857142857143 200000000000000).val)
    (su0 : 0 ≤ su)
    (su2 : su*su = 1+12/((g.width.val + (fraction 348151438013521 31250000000000000000).val*(1+t)) /
      (fraction 1 10000).val))
    (eff : ee = (er.val+1)/2+(er.val-1)/(2*su))
    (se2 : se*se=ee)
    (wide : Real.exp wl = (g.width.val + (fraction 348151438013521 31250000000000000000).val*(1+t)) /
      (fraction 1 10000).val + (fraction 361 250).val)
    (imp : z = impedanceConstant.val / (se * (((g.width.val +
      (fraction 348151438013521 31250000000000000000).val*(1+t)) / (fraction 1 10000).val +
      (fraction 1393 1000).val) + (fraction 667 1000).val*wl)))
    (ind : L = g.length.val*(z*se)/lightSpeed.val)
    (cap : C*z = g.length.val*se/lightSpeed.val)
    (res : R*g.resistanceFactor.val=g.length.val) :
    L=(inductance g).val ∧ C=(capacitance g er).val ∧ R=(resistance g).val := by
  obtain ⟨a,b,c,r,e⟩ := good
  have tEq : t=thickness.val := (Real.exp_injective (logt.trans
    (Real.exp_log (by norm_num [fraction])).symm))
  subst t
  have argEq : su*su=(rootArg g).val := by simpa [rootArg,aspect,integer] using su2
  have root2 : (root g).val*(root g).val = (rootArg g).val := Real.mul_self_sqrt a.le
  have root0 : 0 ≤ (root g).val := Real.sqrt_nonneg _
  have sEq : su = (root g).val := by nlinarith only [argEq,root2,root0,su0]
  subst su
  have eeEq : ee=(effective g er).val := by simpa [effective,integer] using eff
  rw [eeEq] at se2
  have seN : se ≠ 0 := by intro h; rw [h,zero_mul] at se2; linarith
  have expWide : Real.exp wl = (wideArg g).val := by simpa [wideArg,aspect,integer] using wide
  have wEq : wl=Real.log (wideArg g).val := Real.exp_injective (expWide.trans (Real.exp_log b).symm)
  subst wl
  have imp' : z=impedanceConstant.val/(se*(shape g).val) := by
    simpa [shape,aspect,integer,Enclosed.log] using imp
  rw [imp'] at ind cap
  have zpos : 0 < impedanceConstant.val := by norm_num [impedanceConstant,fraction]
  have speed : 0 < lightSpeed.val := by norm_num [lightSpeed,integer]
  refine ⟨?_,?_,?_⟩
  · rw [ind]; simp only [inductance,div_val,mul_val]; field_simp [seN,c.ne']
  · simp only [capacitance,div_val,mul_val]
    field_simp [seN,c.ne',speed.ne',zpos.ne'] at cap ⊢
    linear_combination cap + g.length.val*(shape g).val*se2
  · exact (eq_div_iff r.ne').mpr res

end
end SpiceSmtBench.Microstrip
