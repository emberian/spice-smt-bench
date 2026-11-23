import SpiceSmtBench.SlotWindows
import SpiceSmtBench.SlotCoefficients
import SpiceSmtBench.TransferBox

namespace SpiceSmtBench.SlotLine
open Enclosed LinearTransient TransientWindows TransferBox

set_option maxRecDepth 50000
set_option maxHeartbeats 30000000

private theorem invariant : ∀ (i : Fin 16) (j : Fin 17),
    contained (image halfStepBoxes coefficientBox i j) (coefficientBox i j) = true := by decide +kernel

theorem transfer_exists : ∃ P : Grid 16 17,
    (∀ i j, holds (coefficientBox i j) (P i j).val) ∧
    ∀ i k, ∑ j, (lhs flow i j).val*(P j k).val = (rhs flow i k).val :=
  exists_transfer flow halfStepBoxes coefficientBox
    (fun i j => holds_of_fits (checked_half_step i j)) (by decide +kernel) invariant

theorem drive_verified (k : Fin 81) : fits (drive k) (driveBox k) := by
  revert k; decide +kernel

end SpiceSmtBench.SlotLine
