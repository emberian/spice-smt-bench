import SpiceSmtBench.StitchedResidualData

namespace SpiceSmtBench.Stitched

set_option maxRecDepth 30000

private abbrev StepChunk (base : Nat) := ∀ i : Fin 8, stepCheck (base + i.val)

private theorem step0 : StepChunk 0 := by intro i; fin_cases i <;> decide +kernel
private theorem step1 : StepChunk 8 := by intro i; fin_cases i <;> decide +kernel
private theorem step2 : StepChunk 16 := by intro i; fin_cases i <;> decide +kernel
private theorem step3 : StepChunk 24 := by intro i; fin_cases i <;> decide +kernel
private theorem step4 : StepChunk 32 := by intro i; fin_cases i <;> decide +kernel
private theorem step5 : StepChunk 40 := by intro i; fin_cases i <;> decide +kernel
private theorem step6 : StepChunk 48 := by intro i; fin_cases i <;> decide +kernel
private theorem step7 : StepChunk 56 := by intro i; fin_cases i <;> decide +kernel
private theorem step8 : StepChunk 64 := by intro i; fin_cases i <;> decide +kernel
private theorem step9 : StepChunk 72 := by intro i; fin_cases i <;> decide +kernel

/-- Each sample is checked independently so replay can release the intermediate integer products. -/
theorem step_verified (k : Fin 80) : stepCheck k.val := by
  have hk := k.isLt
  have h (q r : Nat) (hq : k.val / 8 = q) (hr : k.val % 8 = r) (hr8 : r < 8)
      (hc : StepChunk (8 * q)) : stepCheck k.val := by
    have eq : 8 * q + r = k.val := by omega
    simpa [eq] using hc ⟨r, hr8⟩
  have hr8 : k.val % 8 < 8 := Nat.mod_lt _ (by decide)
  have hq10 : k.val / 8 < 10 := Nat.div_lt_of_lt_mul hk
  rcases hq0 : k.val / 8 with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  · exact h 0 (k.val % 8) hq0 rfl hr8 step0
  · exact h 1 (k.val % 8) hq0 rfl hr8 step1
  · exact h 2 (k.val % 8) hq0 rfl hr8 step2
  · exact h 3 (k.val % 8) hq0 rfl hr8 step3
  · exact h 4 (k.val % 8) hq0 rfl hr8 step4
  · exact h 5 (k.val % 8) hq0 rfl hr8 step5
  · exact h 6 (k.val % 8) hq0 rfl hr8 step6
  · exact h 7 (k.val % 8) hq0 rfl hr8 step7
  · exact h 8 (k.val % 8) hq0 rfl hr8 step8
  · exact h 9 (k.val % 8) hq0 rfl hr8 step9
  · omega

theorem receiver_verified : ∀ k : Fin 81, receiverCheck k.val := by decide +kernel

end SpiceSmtBench.Stitched
