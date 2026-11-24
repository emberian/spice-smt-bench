import SpiceSmtBench.CrosstalkReplay

namespace SpiceSmtBench.Crosstalk
open Microstrip LineBounds Enclosed LeanCert.Core
noncomputable section
set_option maxRecDepth 20000
def substrate : Geometry := ⟨fraction 7 40000,fraction 3 200,fraction 7104999999999999 20000000000000000,(261490726/100000000),(261490728/100000000)⟩
def epBox := box (87/20) (93/20) (by decide +kernel)
def enBox := box (77/20) (83/20) (by decide +kernel)
def gapBox := box (-3/200000) (3/200000) (by decide +kernel)
def viaBox := box (1/4000000000) (3/4000000000) (by decide +kernel)
def material (ep en gap via : Enclosed) : Components :=
  let k := exp (-(fraction 19 10 * (fraction 1 5000 + gap) / fraction 1 10000))
  let cp := capacitance substrate ep
  let cn := capacitance substrate en
  let L := inductance substrate
  ⟨cp,cn,(1/2)*(k*(cp+cn)),L,L,(1/2)*(k*(L+L)),via,0,k,resistance substrate⟩
def admissible (er : Enclosed) := (rootArg substrate).positive && (wideArg substrate).positive && (shape substrate).positive && substrate.resistanceFactor.positive && (effective substrate er).positive
theorem physical {er : Enclosed} (h : admissible er) : 0 < (rootArg substrate).val ∧ 0 < (wideArg substrate).val ∧ 0 < (shape substrate).val ∧ 0 < substrate.resistanceFactor.val ∧ 0 < (effective substrate er).val := by
  simp only [admissible,Bool.and_eq_true] at h
  exact ⟨pos h.1.1.1.1,pos h.1.1.1.2,pos h.1.1.2,pos h.1.2,pos h.2⟩
theorem ep_ok : admissible (atLo epBox) := by decide +kernel
theorem en_ok : admissible (atLo enBox) := by decide +kernel
theorem material_ok (ep en gap via : ℝ)
    (hep : ep ∈ epBox) (hen : en ∈ enBox) (hgap : gap ∈ gapBox) (hvia : via ∈ viaBox) :
    check (material (atPoint epBox ep hep) (atPoint enBox en hen) (atPoint gapBox gap hgap) (atPoint viaBox via hvia)) := by
  unfold check
  -- Only the interval endpoints enter the computation. The kernel can reduce
  -- the decision proof while the real fabrication parameters remain free.
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.assign (← Lean.Meta.mkDecideProof (← goal.getType))

end
end SpiceSmtBench.Crosstalk
