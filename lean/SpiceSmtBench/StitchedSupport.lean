import SpiceSmtBench.StitchedMatrices

namespace SpiceSmtBench.Stitched
open TransientWindows
private def support0 : Fin 16 → List (Fin 16) :=
  ![[0, 2], [1, 3], [0, 2], [1, 3], [4], [5, 6], [5, 6], [7, 8], [7, 8], [9, 10], [9, 10], [11, 12], [11, 12], [13, 14], [13, 14], [15]]
private def support1 : Fin 16 → List (Fin 16) :=
  ![[0, 2], [1, 3], [0, 2], [1, 3], [], [5, 6], [5, 6], [7, 8], [7, 8], [], [], [], [], [], [], []]
private def support2 : Fin 16 → List (Fin 16) :=
  ![[0, 2], [1, 3], [0, 2], [1, 3], [], [5, 6], [5, 6], [7, 8], [7, 8], [], [], [], [], [], [], []]
private def support3 : Fin 16 → List (Fin 16) :=
  ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [15]]
private def support4 : Fin 16 → List (Fin 16) :=
  ![[10, 12], [12, 14], [9, 11], [11, 13], [13, 14, 15], [5, 10], [6, 9], [7, 14], [8, 13], [2, 6, 9], [0, 5, 10], [2, 3, 11], [0, 1, 12], [3, 4, 8, 13], [1, 4, 7, 14], [4, 15]]
def massSupport : Fin 4 → Fin 16 → List (Fin 16) := ![support0,support1,support2,support3]
def networkSupport := support4

def supported (s : List (Fin 16)) (r : Fin 16 → Window) : Prop :=
  s.Nodup ∧ ∀ j : Fin 16, j ∉ s → -10000000 ≤ (r j).lo ∧ (r j).hi ≤ 10000000
theorem supports_valid : (∀ a i, supported (massSupport a i) (massWindows a i)) ∧
    ∀ i, supported (networkSupport i) (networkWindows i) := by unfold supported; decide +kernel
end SpiceSmtBench.Stitched
