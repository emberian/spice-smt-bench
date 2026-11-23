import SpiceSmtBench.StitchedGeometry
import SpiceSmtBench.StitchedMatrices
import SpiceSmtBench.PolynomialEnvelope

namespace SpiceSmtBench.Stitched
open LineBounds Enclosed Microstrip StoredEnergy TransientWindows PolynomialEnvelope
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

def weights : Fin 16 → Enclosed :=
  ![1,1,1,1,6/5,4/5,4/5,4/5,4/5,6/5,6/5,6/5,6/5,6/5,6/5,7/50]

def centered (a b c : Enclosed) : Components :=
  let k := exp (fraction (-171) 50)
  let L := inductance substrate
  let cp := ((831/500)+(27/500)*a)/1000000000000
  let cn := ((291/200)+(9/200)*b)/1000000000000
  let ret := ((17/200)+(9/250)*c)/1000000000
  ⟨cp,cn,(1/2)*(k*(cp+cn)),L,L,(1/2)*(k*(L+L)),fraction 1 5000000000,ret,k,resistance substrate⟩

def origin := centered 0 0 0
def baseMass (i : Fin 4) (j l : Fin 16) : Enclosed :=
  ![e_metric origin j l,
    e_metric (centered 1 0 0) j l - e_metric origin j l,
    e_metric (centered 0 1 0) j l - e_metric origin j l,
    e_metric (centered 0 0 1) j l - e_metric origin j l] i
def baseNetwork (i j : Fin 16) : Enclosed := (1/10)*e_network origin i j

theorem matrix_check :
    (∀ (i : Fin 4) (j l : Fin 16), fits (baseMass i j l) (massWindows i j l) = true) ∧
    ∀ i j, fits (baseNetwork i j) (networkWindows i j) = true := by decide +kernel

def normP (p : Components) := (1000000000000*p.cp-831/500)/(27/500)
def normN (p : Components) := (1000000000000*p.cn-291/200)/(9/200)
def normL (p : Components) := (1000000000*p.ret-17/200)/(9/250)

def materialCheck (p : Components) : Prop :=
  regularCheck p = true ∧ p.r.positive = true ∧
  (normP p).inside (-1) 1 = true ∧ (normN p).inside (-1) 1 = true ∧
  (normL p).inside (-1) 1 = true ∧
  ∀ i : Fin 16, (margin (e_metric p) weights i).positive = true

theorem material_ok (ep en pitch : ℝ)
    (hep : ep ∈ epBox) (hen : en ∈ enBox) (hpitch : pitch ∈ pitchBox) :
    materialCheck (material (atPoint epBox ep hep) (atPoint enBox en hen) (atPoint pitchBox pitch hpitch)) := by
  unfold materialCheck
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.assign (← Lean.Meta.mkDecideProof (← goal.getType))

end
end SpiceSmtBench.Stitched
