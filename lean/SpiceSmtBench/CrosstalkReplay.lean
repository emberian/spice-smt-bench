import SpiceSmtBench.CrosstalkStamp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.List.GetD

namespace SpiceSmtBench.Crosstalk
open Enclosed LinearTransient StoredEnergy LineBounds LeanCert.Core
noncomputable section
set_option maxRecDepth 16000

def reference (k : Nat) : Fin 14 → Enclosed :=
  (![![const 0, const 0, const 0, const 0, const 0, const 0, const 0, const 0, const 0, const 0, const 0, const 0, const 0, const 0],
    ![const (11340719/50000000), const (1963463/1000000000), const (1389811/500000000), const (-371/200000000), const (715907/1000000000), const (10309/62500000), const (12617571/250000000), const (11984109/1000000000), const (53931857/500000000), const (-451853/500000000), const (26212757/1000000000), const (-26359/125000000), const (6824661/1000000000), const (-38999/1000000000)],
    ![const (121419203/200000000), const (12836467/1000000000), const (1375887/200000000), const (-18389/1000000000), const (2626157/1000000000), const (777059/1000000000), const (197995953/1000000000), const (61195483/1000000000), const (447559/1250000), const (-3325533/1000000000), const (14921689/125000000), const (-258611/250000000), const (19878133/500000000), const (-11679/50000000)],
    ![const (934429181/1000000000), const (8942123/200000000), const (10016123/1000000000), const (-81901/1000000000), const (2659029/500000000), const (973447/500000000), const (26729649/62500000), const (16788977/100000000), const (667842071/1000000000), const (-6671031/1000000000), const (296248227/1000000000), const (-2692727/1000000000), const (61813053/500000000), const (-145409/200000000)],
    ![const (68308801/62500000), const (110042819/1000000000), const (11386239/1000000000), const (-47077/200000000), const (7826879/1000000000), const (1705897/500000000), const (335845823/500000000), const (327705183/1000000000), const (925177649/1000000000), const (-9657861/1000000000), const (530373109/1000000000), const (-4919167/1000000000), const (271795717/1000000000), const (-1555759/1000000000)],
    ![const (1134789083/1000000000), const (214756451/1000000000), const (2960791/250000000), const (-252033/500000000), const (589593/62500000), const (4663057/1000000000), const (867195687/1000000000), const (255952809/500000000), const (1088386237/1000000000), const (-11456273/1000000000), const (96507393/125000000), const (-3535699/500000000), const (94802469/200000000), const (-511467/200000000)]]) (Fin.ofNat 6 k)

def weights : Fin 14 → Enclosed :=
  ![4/5,8/5,4/5,7/4,6/5,6/5,6/5,6/5,5/4,5/4,5/4,5/4,5/4,5/4]

def ETime (k : Nat) : Enclosed :=
  let b : List Enclosed := [0,fraction 3 50000000000,fraction 3 25000000000,
    fraction 9 50000000000,fraction 3 12500000000,fraction 3 10000000000]
  let t : ℝ := ([realTF.zero,realTF.ofRat 3 50000000000,realTF.ofRat 3 25000000000,
    realTF.ofRat 9 50000000000,realTF.ofRat 3 12500000000,realTF.ofRat 3 10000000000] : List ℝ).getD k 0
  ⟨t,(b.getD k 0).box,by
    intro z h; have m := (b.getD k 0).valid h
    rw [← List.getD_map b (0 : Enclosed) Enclosed.val] at m
    convert m using 1
    simp [b,t,realTF,Enclosed.fraction,LineBounds.numeral_val]⟩

def driver (k : Nat) :=
  let t := ETime k
  let one := (1 : Enclosed)
  let base := one/(one+exp 2)
  fraction 9 5 * ((one/(one+exp (-((t-fraction 1 10000000000)/fraction 1 20000000000)))-base)/(one-base))

def diode (v : ℝ) := (1/1250000000000:ℝ) *
  (Real.exp ((-v)/(135723/5000000))-Real.exp ((v-9/5)/(135723/5000000)))

theorem diode_antitone : Antitone diode := by
  intro v w h
  have a : Real.exp ((-w)/(135723/5000000)) ≤ Real.exp ((-v)/(135723/5000000)) :=
    Real.exp_le_exp.mpr (by linarith)
  have b : Real.exp ((v-9/5)/(135723/5000000)) ≤ Real.exp ((w-9/5)/(135723/5000000)) :=
    Real.exp_le_exp.mpr (by linarith)
  unfold diode; linarith

private theorem diode_range {v : ℝ} (h : -1/100 ≤ v ∧ v ≤ 1/100) :
    -1/10000000000 ≤ diode v ∧ diode v ≤ 1/10000000000 := by
  have a := Real.exp_le_exp.mpr (show (-v)/(135723/5000000) ≤ 1 by linarith [h.1])
  have b := Real.exp_le_exp.mpr (show (v-9/5)/(135723/5000000) ≤ 1 by linarith [h.2])
  have hi := Real.exp_one_lt_d9
  have ap := Real.exp_pos ((-v)/(135723/5000000))
  have bp := Real.exp_pos ((v-9/5)/(135723/5000000))
  unfold diode; constructor <;> linarith

private def diodeBox : IntervalRat := ⟨-1/10000000000,1/10000000000,by decide +kernel⟩
theorem small_ref : ∀ k : Fin 6, (reference k.val 3).inside (-1/100) (1/100) := by decide +kernel
def refDiode (k : Fin 6) : Enclosed :=
  atPoint diodeBox (diode (reference k.val 3).val) (by
    have h := bounds (small_ref k)
    norm_num at h
    simpa [diodeBox,IntervalRat.mem_def] using diode_range (by constructor <;> linarith [h.1,h.2]))

def e_port (u d : Enclosed) : Fin 14 → Enclosed :=
  ![(6/5)*(u*50/28),0,0,(6/5)*50*d,0,0,0,0,0,0,0,0,0,0]

@[simp] theorem e_port_val (u d : Enclosed) (i : Fin 14) :
    (e_port u d i).val = port u.val d.val i := by fin_cases i <;> norm_num [e_port,port]

def residual (p : Components) (k : Fin 5) (i : Fin 14) : Enclosed :=
  let y := reference (k.val+1)
  (6/5) * dot (e_network p i) y +
    e_port (driver (k.val+1)) (refDiode k.succ) i -
    dot (e_metric p i) (fun j => y j - reference k.val j)

def budget (p : Components) (k : Fin 5) :=
  total (fun i => magnitude (residual p k i)/weights i)

def check (p : Components) : Prop :=
  regularCheck p = true ∧ p.r.positive = true ∧
  (∀ i : Fin 14, (margin (e_metric p) weights i).positive = true) ∧
  ∀ k : Fin 5, (budget p k).inside 0 (1/10) = true

end
end SpiceSmtBench.Crosstalk
