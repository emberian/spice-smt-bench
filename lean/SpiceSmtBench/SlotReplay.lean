import SpiceSmtBench.SlotWindows
import SpiceSmtBench.SlotCoefficients
import SpiceSmtBench.TransferBox

namespace SpiceSmtBench.SlotLine
open Enclosed LinearTransient TransientWindows TransferBox

set_option maxRecDepth 50000

private theorem invariant : ∀ (i : Fin 16) (j : Fin 17),
    contained (image halfStepBoxes coefficientBox i j) (coefficientBox i j) = true := by decide +kernel

theorem transfer_exists : ∃ P : Grid 16 17,
    (∀ i j, holds (coefficientBox i j) (P i j).val) ∧
    ∀ i k, ∑ j, (lhs flow i j).val*(P j k).val = (rhs flow i k).val :=
  exists_transfer flow halfStepBoxes coefficientBox
    (fun i j => holds_of_fits (checked_half_step i j)) (by decide +kernel) invariant

private abbrev DriveChunk (base : Nat) :=
  ∀ i : Fin 9, fits (drive (base + i.val)) (driveBox (base + i.val))

private theorem drive0 : DriveChunk 0 := by decide +kernel
private theorem drive1 : DriveChunk 9 := by decide +kernel
private theorem drive2 : DriveChunk 18 := by decide +kernel
private theorem drive3 : DriveChunk 27 := by decide +kernel
private theorem drive4 : DriveChunk 36 := by decide +kernel
private theorem drive5 : DriveChunk 45 := by decide +kernel
private theorem drive6 : DriveChunk 54 := by decide +kernel
private theorem drive7 : DriveChunk 63 := by decide +kernel
private theorem drive8 : DriveChunk 72 := by decide +kernel

theorem drive_verified (k : Fin 81) : fits (drive k) (driveBox k) := by
  have hk := k.isLt
  have h (q r : Nat) (hq : k.val / 9 = q) (hr : k.val % 9 = r) (hr9 : r < 9)
      (hc : DriveChunk (9 * q)) : fits (drive k.val) (driveBox k.val) := by
    have eq : 9 * q + r = k.val := by omega
    simpa [eq] using hc ⟨r, hr9⟩
  have hk9 : k.val % 9 < 9 := Nat.mod_lt _ (by decide)
  have hq9 : k.val / 9 < 9 := Nat.div_lt_of_lt_mul hk
  rcases hq0 : k.val / 9 with _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  · exact h 0 (k.val % 9) hq0 rfl hk9 drive0
  · exact h 1 (k.val % 9) hq0 rfl hk9 drive1
  · exact h 2 (k.val % 9) hq0 rfl hk9 drive2
  · exact h 3 (k.val % 9) hq0 rfl hk9 drive3
  · exact h 4 (k.val % 9) hq0 rfl hk9 drive4
  · exact h 5 (k.val % 9) hq0 rfl hk9 drive5
  · exact h 6 (k.val % 9) hq0 rfl hk9 drive6
  · exact h 7 (k.val % 9) hq0 rfl hk9 drive7
  · exact h 8 (k.val % 9) hq0 rfl hk9 drive8
  · omega

end SpiceSmtBench.SlotLine
