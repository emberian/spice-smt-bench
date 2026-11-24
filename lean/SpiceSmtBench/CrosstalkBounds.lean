import SpiceSmtBench.CrosstalkReplay

namespace SpiceSmtBench.Crosstalk
open Enclosed LinearTransient StoredEnergy LineBounds LeanCert.Core
noncomputable section
set_option maxRecDepth 16000
private abbrev weight (i : Fin 14) := (weights i).val
private theorem weight_pos : ∀ i, 0 < weight i := by intro i; fin_cases i <;> norm_num [weight,weights]
private def nominal (k : Nat) : State 14 := fun i => (reference k i).val

private theorem symmetric (p : Line) (i j : Fin 14) : metric p i j = metric p j i := by
  exact congrArg ((10:ℝ)^12 * ·) (mass_symmetric p i j)

set_option maxHeartbeats 260000 in
private theorem lossless (p : Line) (hp : 0 ≤ p.r) (x : State 14) :
    work x (action (network p) x) ≤ 0 := by
  apply passive
  · intro i; fin_cases i <;> norm_num [network] <;> linarith
  · intro i j h; fin_cases i <;> fin_cases j <;> norm_num [network] at *

private theorem residual_val (p : Components) (k : Fin 5) (i : Fin 14) :
    (residual p k i).val =
    halfStep * action (network (components p)) (nominal (k.val+1)) i +
    port (driver (k.val+1)).val (diode (nominal (k.val+1) 3)) i -
    action (metric (components p)) (fun j => nominal (k.val+1) j-nominal k.val j) i := by
  simp only [residual,sub_val,add_val,mul_val,div_val,LineBounds.numeral_val,dot_val,
    value_network,value_metric,e_port_val,action,halfStep,nominal,refDiode,atPoint]
  rfl

private theorem power_bound (p : Components) (ck : check p) (k : Fin 5) (x y : State 14)
    (model : ∀ i, action (metric (components p)) (fun j => y j-x j) i =
      halfStep * action (network (components p)) y i + port (driver (k.val+1)).val (diode (y 3)) i) :
    let e := fun i => x i - nominal k.val i
    let f := fun i => y i - nominal (k.val+1) i
    amplitude (metric (components p)) f ≤ amplitude (metric (components p)) e + 1/5 := by
  obtain ⟨_,hr,hmargin,hbudget⟩ := ck
  let m := metric (components p)
  let K := network (components p)
  let e := fun i => x i-nominal k.val i
  let f := fun i => y i-nominal (k.val+1) i
  let r := fun i => (residual p k i).val
  let d := (6/5:ℝ)*50*(diode (y 3)-diode (nominal (k.val+1) 3))
  have equation (i) : action m (fun j => f j-e j) i = halfStep*action K f i + (if i=3 then d else 0) + r i := by
    have base := model i
    have correction := residual_val p k i
    change r i = _ at correction
    have shape (j) : f j-e j = (y j-x j)-(nominal (k.val+1) j-nominal k.val j) := by dsimp [f,e]; ring
    have add_port : port (driver (k.val+1)).val (diode (y 3)) i =
        port (driver (k.val+1)).val (diode (nominal (k.val+1) 3)) i + (if i=3 then d else 0) := by
      fin_cases i <;> simp [port,d]; ring
    rw [add_port] at base
    simp only [shape,action,mul_sub,Finset.sum_sub_distrib,f] at base correction ⊢
    dsimp only [m,K]
    linear_combination base - correction
  have mag (z : State 14) (i : Fin 14) : (weight i*z i)^2 ≤ energy m z := by
    apply lower m weight z (symmetric _) _ i
    intro j
    have H := margin_ok _ _ _ (hmargin j)
    simpa only [value_metric,weight,m] using H
  have zn (z : State 14) : 0 ≤ energy m z := (sq_nonneg _).trans (mag z 0)
  have amp := fun i => coord m weight f i (weight_pos i).le (mag f i)
  have rbound : work f r ≤ amplitude m f*(1/10) := by
    let b := fun i => |r i| / weight i
    have cost : (∑ i, b i) ≤ 1/10 := by
      have B := (bounds (hbudget k)).2
      simpa [b,r,weight,budget,total_val] using B
    apply (summand_budget f r weight b _ amp _ _).trans (mul_le_mul_of_nonneg_left cost (Real.sqrt_nonneg _))
    · intro i; dsimp [b]; field_simp [(weight_pos i).ne']; rfl
    · intro i; exact div_nonneg (abs_nonneg _) (weight_pos i).le
  have pd : f 3*d ≤ 0 := by
    rcases le_total (y 3) (nominal (k.val+1) 3) with h|h
    · have a := diode_antitone h
      dsimp [f,d]; exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (by positivity [sub_nonneg.mpr a])
    · have a := diode_antitone h
      dsimp [f,d]; apply mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h)
      linarith
  have damp := lossless (components p) (pos hr).le f
  have W : work f (action m (fun j => f j-e j)) ≤ amplitude m f*(1/10) := by
    unfold work
    simp_rw [equation,mul_add]
    simp only [Finset.sum_add_distrib,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    have eq (i) : f i*(halfStep*action K f i) = halfStep*(f i*action K f i) := by ring
    simp_rw [eq,← Finset.mul_sum]
    change halfStep*work f (action K f) + f 3*d + work f r ≤ _
    dsimp only [K,halfStep] at *
    linarith only [rbound,damp,pd]
  have T := euler_bound m e f (1/10) (symmetric _) zn W (by norm_num)
  convert T using 1; ring

theorem safe_of_model (p : Components) (ok : check p) (x : Nat → State 14)
    (init : ∀ i, x 0 i = 0)
    (step : ∀ k : Fin 5, ∀ i, action (metric (components p)) (fun j => x (k.val+1) j-x k.val j) i =
      halfStep*action (network (components p)) (x (k.val+1)) i +
        port (driver (k.val+1)).val (diode (x (k.val+1) 3)) i) :
    ∀ k ≤ 5, -3/4 < x k 3 ∧ x k 3 < 13/20 := by
  let m := metric (components p)
  let err := fun k i => x k i-nominal k i
  have A (k : Nat) (hk : k≤5) : amplitude m (err k) ≤ (k:ℝ)/5 := by
    induction k with
    | zero =>
      have z (i : Fin 14) : nominal 0 i = 0 := by fin_cases i <;> norm_num [nominal,reference]
      simp [err,init,z,amplitude,energy,work,action]
    | succ k ih =>
      have a := power_bound p ok ⟨k,by omega⟩ (x k) (x (k+1)) (step ⟨k,by omega⟩)
      change amplitude m (err (k+1)) ≤ amplitude m (err k) + 1/5 at a
      push_cast
      linarith [ih (by omega)]
  intro k hk
  have mag : (weight 3*err k 3)^2 ≤ energy m (err k) := by
    apply lower m weight _ (symmetric _)
    intro j; simpa only [value_metric,weight,m] using margin_ok _ _ _ (ok.2.2.1 j)
  have c := coord m weight (err k) 3 (weight_pos 3).le mag
  have cur := (bounds (small_ref ⟨k,by omega⟩))
  change _ ≤ nominal k 3 ∧ nominal k 3 ≤ _ at cur
  norm_num at cur
  have w : weight 3 = 7/4 := by norm_num [weight,weights]
  rw [w] at c; dsimp only [err] at c
  have a := A k hk
  have lh := neg_le_abs (x k 3-nominal k 3)
  have uh := le_abs_self (x k 3-nominal k 3)
  have kk : (k:ℝ) ≤ 5 := by exact_mod_cast hk
  constructor <;> linarith only [cur.1,cur.2,kk,a,c,lh,uh]

def upperDiode (v : ℝ) := (1/1250000000000:ℝ)*(Real.exp ((v-9/5)/(135723/5000000))-1)
def lowerDiode (v : ℝ) := (1/1250000000000:ℝ)*(Real.exp ((-v)/(135723/5000000))-1)

theorem safe_from_stamp (p : Components) (ok : check p) (s : Nat → State 14)
    (init : ∀ i, s 0 i=0)
    (step : ∀ k : Fin 5, ∀ i, s (k.val+1) i = s k.val i + (3/50000000000:ℝ) *
      rates (components p) (s (k.val+1)) (driver (k.val+1)).val
        (upperDiode (s (k.val+1) 3)) (lowerDiode (s (k.val+1) 3)) i) :
    ∀ k ≤ 5, -3/4 < s k 3 ∧ s k 3 < 13/20 := by
  apply safe_of_model p ok (fun k => coordinates (s k))
  · intro i; fin_cases i <;> simp [coordinates,init]
  · intro k i
    let R := rates (components p) (s (k.val+1)) (driver (k.val+1)).val
      (upperDiode (s (k.val+1) 3)) (lowerDiode (s (k.val+1) 3))
    have cd (j : Fin 14) : coordinates (s (k.val+1)) j - coordinates (s k.val) j =
        (3/50000000000:ℝ)*coordinates R j := coordinate_delta _ _ R _ (step k) j
    simp_rw [cd]
    have scalar : action (metric (components p)) (fun j => (3/50000000000:ℝ)*coordinates R j) i =
        (3/50000000000:ℝ)*action (metric (components p)) (coordinates R) i := by
      simp only [action,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    rw [scalar]
    have h := flux (components p) (s (k.val+1)) (driver (k.val+1)).val
      (upperDiode (s (k.val+1) 3)) (lowerDiode (s (k.val+1) 3)) (regular_of_check p ok.1) i
    have D (v : ℝ) : -upperDiode v + lowerDiode v = diode v := by
      unfold upperDiode lowerDiode diode; ring
    rw [D] at h
    exact h

end
end SpiceSmtBench.Crosstalk
