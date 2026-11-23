import SpiceSmtBench.StitchedResidualData

namespace SpiceSmtBench.Stitched

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-- Each sample is checked independently so replay can release the intermediate integer products. -/
theorem step_verified (k : Fin 80) : stepCheck k.val := by
  fin_cases k <;> decide +kernel

theorem receiver_verified : ∀ k : Fin 81, receiverCheck k.val := by decide +kernel

end SpiceSmtBench.Stitched
