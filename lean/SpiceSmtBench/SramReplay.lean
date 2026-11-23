import SpiceSmtBench.SramTrajectory

namespace SpiceSmtBench.SramTrajectory

-- Each row certifies all four boundary signs for one implicit step. Separate
-- kernel reductions release the Taylor arithmetic for earlier steps.
set_option Elab.async false
set_option maxRecDepth 32000
set_option maxHeartbeats 10000000

private abbrev Row (k : Nat) := ∀ s h : Bool, faceCheck k s h = true

private theorem row0 : Row 0 := by decide +kernel
private theorem row1 : Row 1 := by decide +kernel
private theorem row2 : Row 2 := by decide +kernel
private theorem row3 : Row 3 := by decide +kernel
private theorem row4 : Row 4 := by decide +kernel
private theorem row5 : Row 5 := by decide +kernel
private theorem row6 : Row 6 := by decide +kernel
private theorem row7 : Row 7 := by decide +kernel
private theorem row8 : Row 8 := by decide +kernel
private theorem row9 : Row 9 := by decide +kernel
private theorem row10 : Row 10 := by decide +kernel
private theorem row11 : Row 11 := by decide +kernel
private theorem row12 : Row 12 := by decide +kernel
private theorem row13 : Row 13 := by decide +kernel
private theorem row14 : Row 14 := by decide +kernel
private theorem row15 : Row 15 := by decide +kernel
private theorem row16 : Row 16 := by decide +kernel
private theorem row17 : Row 17 := by decide +kernel
private theorem row18 : Row 18 := by decide +kernel
private theorem row19 : Row 19 := by decide +kernel

theorem checkedFaces (k : Fin 20) : Row k := by
  fin_cases k
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row16
  · exact row17
  · exact row18
  · exact row19

end SpiceSmtBench.SramTrajectory
