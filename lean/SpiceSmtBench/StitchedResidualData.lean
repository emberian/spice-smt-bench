import SpiceSmtBench.StitchedSupport
import SpiceSmtBench.StitchedReference
import SpiceSmtBench.SlotWindows

namespace SpiceSmtBench.Stitched
open TransientWindows PolynomialEnvelope StoredEnergy
set_option maxRecDepth 30000

def zeroW : Window := ⟨0,0⟩
def negW (w : Window) : Window := ⟨-w.hi,-w.lo⟩
def pointW (z : Int) : Window := ⟨z*1000000000,z*1000000000⟩
def sumW : List Window → Window
  | [] => zeroW
  | b :: bs => add b (sumW bs)
def magnitudeW (b : Window) := max (-b.lo) b.hi
noncomputable def referenceValue (k : Nat) (b : Fin 10) (j : Fin 16) : ℝ := (traceData k b j : ℝ)/1000000000
def deltaW (k : Nat) (b : Fin 10) (j : Fin 16) :=
  pointW (traceData (k+1) b j - traceData k b j)
def plusW (k : Nat) (b : Fin 10) (j : Fin 16) :=
  pointW (traceData (k+1) b j + traceData k b j)
def srcW (k : Nat) : Window :=
  applyRow (fun _ : Fin 1 => ⟨200000000000000000,200000000000000000⟩)
    (fun _ => add (SlotLine.driveBox k) (SlotLine.driveBox (k+1)))
def inputW (k : Nat) (i : Fin 16) := if i=5 then negW (srcW k) else if i=6 then srcW k else zeroW
/-- The omitted entries contribute at most 16 · 4 · 10⁻¹¹. -/
def sparseDot (support : List (Fin 16)) (matrix vec : Fin 16 → Window) : Window :=
  add ⟨-1000000000,1000000000⟩
    (sumW (support.map fun j => applyRow (fun _ : Fin 1 => matrix j) (fun _ => vec j)))
def valueW (k : Nat) (i : Fin 16) (b : Fin 10) :=
  add (sparseDot (networkSupport i) (networkWindows i) (plusW k b)) (if b=0 then inputW k i else zeroW)
def productW (k : Nat) (i : Fin 16) (t : Fin 4 × Fin 10) :=
  sparseDot (massSupport t.1 i) (massWindows t.1 i) (deltaW k t.2)
def cubicW (k : Nat) (i : Fin 16) (t : Fin 20) :=
  add (if h : t.val<10 then valueW k i ⟨t.val,h⟩ else zeroW)
    (negW (sumW ((products t).map (productW k i))))
/-- Rowwise residual allowances in units of 10⁻¹⁸ in the normalized charge/flux balance. -/
def limits : Fin 16 → Int :=
  ![25000000000000,25000000000000,25000000000000,25000000000000,1000000000000,
    10000000000000,10000000000000,10000000000000,10000000000000,
    1000000000000,1000000000000,1000000000000,1000000000000,1000000000000,1000000000000,10500000000000]
def stepCheck (k : Nat) := ∀ i : Fin 16, ∑ t : Fin 20, magnitudeW (cubicW k i t) ≤ limits i
set_option maxHeartbeats 550000 in
instance (k : Nat) : Decidable (stepCheck k) := inferInstanceAs (Decidable (∀ _ : Fin 16, _))
def receiverCheck (k : Nat) := ∑ b : Fin 10, |traceData k b 4| ≤ 5000000
instance (k : Nat) : Decidable (receiverCheck k) := inferInstanceAs (Decidable (_ ≤ (_ : Int)))

end SpiceSmtBench.Stitched
