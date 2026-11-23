import SpiceSmtBench.StitchedStamp

namespace SpiceSmtBench.Stitched
open Microstrip LineBounds Enclosed LeanCert.Core
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
def substrate : Geometry := ⟨fraction 1 6250,fraction 6666666666666667 500000000000000000,fraction 203 625,(270134453/100000000),(270134455/100000000)⟩
def epBox := box (22/5) (47/10) (by decide +kernel)
def enBox := box (19/5) (81/20) (by decide +kernel)
def pitchBox := box (1/10000) (3/12500) (by decide +kernel)
def material (ep en pitch : Enclosed) : Components :=
  let k := exp (fraction (-171) 50)
  let cp := capacitance substrate ep
  let cn := capacitance substrate en
  let L := inductance substrate
  ⟨cp,cn,(1/2)*(k*(cp+cn)),L,L,(1/2)*(k*(L+L)),fraction 1 5000000000,fraction 1 2000000*pitch,k,resistance substrate⟩
def admissible (er : Enclosed) := (rootArg substrate).positive && (wideArg substrate).positive && (shape substrate).positive && substrate.resistanceFactor.positive && (effective substrate er).positive
theorem physical {er : Enclosed} (h : admissible er) : 0 < (rootArg substrate).val ∧ 0 < (wideArg substrate).val ∧ 0 < (shape substrate).val ∧ 0 < substrate.resistanceFactor.val ∧ 0 < (effective substrate er).val := by
  simp only [admissible,Bool.and_eq_true] at h
  exact ⟨pos h.1.1.1.1,pos h.1.1.1.2,pos h.1.1.2,pos h.1.2,pos h.2⟩
theorem ep_ok : admissible (atLo epBox) := by decide +kernel
theorem en_ok : admissible (atLo enBox) := by decide +kernel
end
end SpiceSmtBench.Stitched
