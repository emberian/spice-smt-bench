import SpiceSmtBench.StitchedBalance

namespace SpiceSmtBench.Stitched
open LineBounds Enclosed StoredEnergy PolynomialEnvelope TransientWindows
noncomputable section
set_option maxRecDepth 16000

private abbrev weight (i : Fin 16) := (weights i).val
private abbrev allowance (i : Fin 16) := (limits i : ℝ)/scale
private theorem weight_pos : ∀ i, 0 < weight i := by
  intro i; fin_cases i <;> norm_num [weight,weights]
private theorem allowance_nonneg : ∀ i, 0 ≤ allowance i := by
  intro i; fin_cases i <;> norm_num [allowance,limits,scale]
private theorem budget : ∑ i, allowance i / weight i ≤ 1/4000 := by
  norm_num [allowance,weight,limits,weights,scale,Fin.sum_univ_succ]
private theorem symmetric (p : Line) (i j : Fin 16) : metric p i j=metric p j i :=
  congrArg ((10:ℝ)^12 * ·) (mass_symmetric p i j)
set_option maxHeartbeats 420000 in
private theorem lossless (p : Line) (hr : 0 ≤ p.r) (x : State 16) : work x (action (network p) x) ≤ 0 := by
  apply passive
  · intro i; fin_cases i <;> norm_num [network] <;> linarith
  · intro i j h; fin_cases i <;> fin_cases j <;> norm_num [network] at *

private theorem lower_bound (p : Components) (ok : materialCheck p) (x : State 16) (i : Fin 16) :
    (weight i*x i)^2 ≤ energy (metric (components p)) x := by
  apply lower _ weight x (symmetric _)
  intro j; simpa only [value_metric,weight] using margin_ok _ _ _ (ok.2.2.2.2.2 j)

private theorem advance (p : Components) (ok : materialCheck p) (x y r : State 16)
    (h : ∀ i, |r i|≤allowance i)
    (law : ∀ i, action (metric (components p)) (fun j => y j-x j) i =
      halfStep*action (network (components p)) (fun j => y j+x j) i + r i) :
    amplitude (metric (components p)) y ≤ amplitude (metric (components p)) x+1/4000 := by
  let m := metric (components p)
  let f := fun i => y i+x i
  let a := amplitude m y + amplitude m x
  have coordinate (z : State 16) (i : Fin 16) := coord m weight z i (weight_pos i).le (lower_bound p ok z i)
  have bound (i) : weight i*|f i|≤a := by
    apply (mul_le_mul_of_nonneg_left (abs_add_le ..) (weight_pos i).le).trans
    rw [mul_add]; exact add_le_add (coordinate y i) (coordinate x i)
  have workR : work f r ≤ a*(1/4000) := by
    apply (summand_budget f r weight (fun i => allowance i / weight i) a bound _ _).trans
    · apply mul_le_mul_of_nonneg_left budget (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    · intro i; simpa [mul_div_cancel₀, (weight_pos i).ne',mul_div_assoc'] using h i
    · intro i; exact div_nonneg (allowance_nonneg i) (weight_pos i).le
  apply trapezoidal_bound m x y _ (symmetric _)
  · intro z; exact (sq_nonneg _).trans (lower_bound p ok z 0)
  · change work f (action m (fun j => y j-x j)) ≤ a*(1/4000)
    unfold work
    change ∀ i, action m (fun j => y j-x j) i=halfStep*action (network (components p)) f i+r i at law
    simp only [law,mul_add,Finset.sum_add_distrib]
    have rearrange (i) : f i*(halfStep*action (network (components p)) f i) =
        halfStep*(f i*action (network (components p)) f i) := by ring
    change (∑ i, f i*(halfStep*action (network (components p)) f i)) + work f r ≤ _
    simp_rw [rearrange,← Finset.mul_sum]
    have hf := lossless (components p) (pos ok.2.1).le f
    change halfStep*work f (action (network (components p)) f) + work f r ≤ _
    dsimp only [halfStep]; linarith only [hf,workR]
  · norm_num

theorem safe_of_model (ep en pitch : Enclosed) (ok : materialCheck (material ep en pitch))
    (states : Nat → State 16) (init : ∀ j, states 0 j=0)
    (steps : ∀ k : Fin 80, ∀ i, action (metric (components (material ep en pitch)))
      (fun j => states (k.val+1) j-states k.val j) i =
      halfStep*action (network (components (material ep en pitch))) (fun j => states (k.val+1) j+states k.val j) i +
        source k.val i)
    (rc : ∀ k : Fin 80, stepCheck k.val) (vc : ∀ k : Fin 81, receiverCheck k.val) :
    ∀ k ≤ 80, -1/40 < states k 4 ∧ states k 4 < 1/40 := by
  let p := material ep en pitch
  let m := metric (components p)
  let K := network (components p)
  let y := approximation p
  let e := fun k i => states k i-y k i
  have energy_bound (k : Nat) (hk : k≤80) : amplitude m (e k) ≤ (k:ℝ)/4000 := by
    induction k with
    | zero =>
      have z : ∀ (b : Fin 10) (i : Fin 16), traceData 0 b i=0 := by decide +kernel
      simp [e,init,y,approximation,evaluate,referenceValue,z,amplitude,energy,work,action]
    | succ k ih =>
      let r := fun i => halfStep*action K (fun j => y (k+1) j+y k j) i + source k i -
        action m (fun j => y (k+1) j-y k j) i
      have law (i) : action m (fun j => e (k+1) j-e k j) i =
          halfStep*action K (fun j => e (k+1) j+e k j) i + r i := by
        have st := steps ⟨k,by omega⟩ i
        change action m (fun j => states (k+1) j-states k j) i =
          halfStep*action K (fun j => states (k+1) j+states k j) i + source k i at st
        simp only [r,e,action,mul_sub,mul_add,Finset.sum_add_distrib,Finset.sum_sub_distrib] at st ⊢
        linear_combination st
      have next := advance p ok (e k) (e (k+1)) r
        (fun i => model_residual ep en pitch ok ⟨k,by omega⟩ i (rc ⟨k,by omega⟩)) law
      change amplitude m (e (k+1)) ≤ amplitude m (e k)+1/4000 at next
      push_cast; linarith [ih (by omega)]
  intro k hk
  have a := energy_bound k hk
  have co := coord m weight (e k) 4 (weight_pos 4).le (lower_bound p ok (e k) 4)
  have re := receiver_approximation p ok k (vc ⟨k,by omega⟩)
  have w : weight 4=6/5 := by norm_num [weight,weights]
  rw [w] at co
  have high := le_abs_self (e k 4)
  have low := neg_le_abs (e k 4)
  have q : (k:ℝ)≤80 := by exact_mod_cast hk
  change |y k 4| ≤ _ at re
  obtain ⟨u,v⟩ := abs_le.mp re
  dsimp only [e] at high low
  constructor <;> linarith only [q,a,co,high,low,u,v]

private theorem coord_sum (u v : State 16) (i : Fin 16) :
    coordinates (fun j => u j+v j) i = coordinates u i+coordinates v i := by
  fin_cases i <;> simp [coordinates] <;> ring

theorem safe_from_stamp (ep en pitch : Enclosed) (ok : materialCheck (material ep en pitch))
    (s : Nat → State 16) (init : ∀ i, s 0 i=0)
    (step : ∀ k : Fin 80, ∀ i, s (k.val+1) i=s k.val i+(1/200000000000:ℝ)*
      (rates (components (material ep en pitch)) (s k.val) (SlotLine.drive k.val).val 0 0 i+
       rates (components (material ep en pitch)) (s (k.val+1)) (SlotLine.drive (k.val+1)).val 0 0 i))
    (rc : ∀ k : Fin 80, stepCheck k.val) (vc : ∀ k : Fin 81, receiverCheck k.val) :
    ∀ k ≤ 80, -1/40 < s k 4 ∧ s k 4 < 1/40 := by
  apply safe_of_model ep en pitch ok (fun k => coordinates (s k)) _ _ rc vc
  · intro i; fin_cases i <;> simp [coordinates,init]
  · intro k i
    let p := components (material ep en pitch)
    let R := fun k => rates p (s k) (SlotLine.drive k).val 0 0
    let t : ℝ := 1/200000000000
    have cd (j : Fin 16) : coordinates (s (k.val+1)) j-coordinates (s k.val) j =
        t*(coordinates (R k.val) j+coordinates (R (k.val+1)) j) :=
      (coordinate_delta _ _ (fun j => R k.val j+R (k.val+1) j) t (step k) j).trans
        (congrArg (t * ·) (coord_sum ..))
    have h (l : Nat) := flux p (s l) (SlotLine.drive l).val 0 0 (regular_of_check _ ok.1) i
    have add (a b : State 16) (m : Coeff 16) :
        action m (fun j => a j+b j) i=action m a i+action m b i := by simp [action,mul_add,Finset.sum_add_distrib]
    have scale_act (m : Coeff 16) (a : State 16) :
        action m (fun j => t*a j) i = t*action m a i := by
      simp only [action,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    have ps (u v : ℝ) : port u (-(0:ℝ)+0) i + port v (-(0:ℝ)+0) i=port (u+v) 0 i := by
      fin_cases i <;> simp [port] <;> ring
    simp_rw [cd]
    rw [scale_act,add,add,mul_add]
    change t * action (metric p) (coordinates (R k.val)) i +
        t * action (metric p) (coordinates (R (k.val+1))) i = _
    rw [show t*action (metric p) (coordinates (R k.val)) i = _ from h k.val,
        show t*action (metric p) (coordinates (R (k.val+1))) i = _ from h (k.val+1)]
    unfold source
    rw [← ps]
    ring


end
end SpiceSmtBench.Stitched
