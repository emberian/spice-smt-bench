import SpiceSmtBench.StitchedAffine
import SpiceSmtBench.StitchedResidual

namespace SpiceSmtBench.Stitched
open LineBounds Enclosed StoredEnergy PolynomialEnvelope TransientWindows
noncomputable section
set_option maxRecDepth 16000

def approximation (p : Components) (k : Nat) : State 16 := fun i =>
  evaluate (mon2 (normP p).val (normN p).val (normL p).val) (fun b => referenceValue k b i)

private theorem action_left {n q} (w : Fin q → ℝ) (m : Fin q → Coeff n) (x : State n) (i) :
    action (fun i j => evaluate w (fun a => m a i j)) x i =
      evaluate w (fun a => action (m a) x i) := by
  simp only [action,evaluate,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro j _; ring

private theorem expand_balance (ep en pitch : Enclosed) (k : Nat) (i : Fin 16) :
    let p := material ep en pitch
    let y := approximation p
    let a := (normP p).val
    let b := (normN p).val
    let c := (normL p).val
    evaluate (mon3 a b c) (coefficient (forceTerm k i) (massTerm k i)) =
      halfStep*action (network (components p)) (fun j => y (k+1) j+y k j) i + source k i -
      action (metric (components p)) (fun j => y (k+1) j-y k j) i := by
  dsimp only
  let p := material ep en pitch
  let v := mon2 (normP p).val (normN p).val (normL p).val
  let w := mon1 (normP p).val (normN p).val (normL p).val
  have src : evaluate v (fun b : Fin 10 => if b=0 then source k i else 0) = source k i := by
    simp [evaluate,mul_ite,v,mon2]
  have plus (j : Fin 16) : approximation p (k+1) j + approximation p k j =
      evaluate v (fun t => referenceValue (k+1) t j+referenceValue k t j) := (evaluate_add ..).symm
  have sub (j : Fin 16) : approximation p (k+1) j - approximation p k j =
      evaluate v (fun t => referenceValue (k+1) t j-referenceValue k t j) := (evaluate_sub ..).symm
  rw [collect]
  change evaluate v (forceTerm k i) - evaluate w (fun t => evaluate v (massTerm k i t)) = _
  change _ = halfStep*action (network (components p)) (fun j => approximation p (k+1) j+approximation p k j) i +
    source k i-action (metric (components p)) (fun j => approximation p (k+1) j-approximation p k j) i
  simp_rw [plus,sub]
  unfold forceTerm massTerm
  rw [evaluate_add,src,← action_evaluate]
  have network_eq (x : State 16) : action (fun i j => (baseNetwork i j).val) x i =
      halfStep*action (network (components p)) x i := by
    simp only [action,fixed_network ep en pitch,Finset.mul_sum,mul_assoc,p]
  rw [network_eq]
  congr 1
  have mEq : metric (components p) = fun i j => evaluate w (fun t => (baseMass t i j).val) := by
    funext j l; exact affine_metric ep en pitch j l
  rw [mEq,action_left]
  apply Finset.sum_congr rfl; intro t _
  apply congrArg (w t * ·)
  exact (action_evaluate _ v (fun b j => referenceValue (k+1) b j-referenceValue k b j) i).symm

theorem model_residual (ep en pitch : Enclosed) (ok : materialCheck (material ep en pitch))
    (k : Fin 80) (i : Fin 16) (h : stepCheck k.val) :
    let p := material ep en pitch
    let y := approximation p
    |halfStep*action (network (components p)) (fun j => y (k.val+1) j+y k.val j) i + source k.val i -
      action (metric (components p)) (fun j => y (k.val+1) j-y k.val j) i| ≤ (limits i:ℝ)/scale := by
  dsimp only
  rw [← expand_balance]
  apply residual_bound k i h
  all_goals apply abs_le.mpr
  · simpa using bounds ok.2.2.1
  · simpa using bounds ok.2.2.2.1
  · simpa using bounds ok.2.2.2.2.1

theorem receiver_approximation (p : Components) (ok : materialCheck p) (k : Nat) (h : receiverCheck k) :
    |approximation p k 4| ≤ 1/200 := by
  have ha : |(normP p).val|≤1 := abs_le.mpr (by simpa using bounds ok.2.2.1)
  have hb : |(normN p).val|≤1 := abs_le.mpr (by simpa using bounds ok.2.2.2.1)
  have hc : |(normL p).val|≤1 := abs_le.mpr (by simpa using bounds ok.2.2.2.2.1)
  apply (eval_abs_le _ _ (fun i => ?_)).trans
  · simp only [referenceValue,abs_div,show |(1000000000:ℝ)| = 1000000000 by norm_num,← Finset.sum_div,
      ← Int.cast_abs,← Int.cast_sum]
    have b : ((∑ t, |traceData k t 4| : Int):ℝ) ≤ 5000000 := by exact_mod_cast h
    linarith
  · exact mon3_le ha hb hc (i.castLE (by decide : 10≤20)) |> fun h => by
      fin_cases i <;> exact h

end
end SpiceSmtBench.Stitched
