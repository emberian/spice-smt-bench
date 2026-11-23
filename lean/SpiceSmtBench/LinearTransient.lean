import SpiceSmtBench.Enclosed

namespace SpiceSmtBench.LinearTransient
open Enclosed

abbrev Grid (n m : Nat) := Fin n → Fin m → Enclosed

noncomputable def dot {n : Nat} (a b : Fin n → Enclosed) : Enclosed :=
  match n with
  | 0 => const 0
  | n+1 => a 0*b 0 + dot (fun i : Fin n => a i.succ) (fun i => b i.succ)

theorem dot_val {n} (a b : Fin n → Enclosed) :
    (dot a b).val = ∑ i, (a i).val*(b i).val := by
  induction n with
  | zero => simp [dot]
  | succ n ih => rw [Fin.sum_univ_succ]; simp only [dot,add_val,mul_val,ih]

/-- A linear stamped expression, together with the coefficient of each input. -/
structure Form (n : Nat) where
  eval : (Fin n → ℝ) → ℝ
  coeff : Fin n → Enclosed
  sound : ∀ x, eval x = ∑ j, (coeff j).val*x j

noncomputable section
namespace Form
def input {n} (i : Fin n) : Form n where
  eval x := x i
  coeff j := if i=j then const 1 else const 0
  sound x := by simp [apply_ite]

def plus {n} (a b : Form n) : Form n where
  eval x := a.eval x + b.eval x
  coeff j := a.coeff j + b.coeff j
  sound x := by simp only [add_val,add_mul,Finset.sum_add_distrib,a.sound,b.sound]

def minus {n} (a b : Form n) : Form n where
  eval x := a.eval x - b.eval x
  coeff j := a.coeff j - b.coeff j
  sound x := by simp only [sub_val,sub_mul,Finset.sum_sub_distrib,a.sound,b.sound]

def neg {n} (a : Form n) : Form n where
  eval x := -a.eval x
  coeff j := -a.coeff j
  sound x := by simp only [neg_val,neg_mul,Finset.sum_neg_distrib,a.sound]

def scale {n} (a : Enclosed) (b : Form n) : Form n where
  eval x := a.val * b.eval x
  coeff j := a * b.coeff j
  sound x := by simp only [mul_val,mul_assoc,Finset.mul_sum,b.sound]

def rightScale {n} (b : Form n) (a : Enclosed) : Form n where
  eval x := b.eval x * a.val
  coeff := (scale a b).coeff
  sound x := (mul_comm ..).trans ((scale a b).sound x)

def divide {n} (b : Form n) (a : Enclosed) : Form n where
  eval x := b.eval x / a.val
  coeff j := b.coeff j / a
  sound x := by simp only [div_val,div_mul_eq_mul_div,Finset.sum_div,b.sound]
end Form

/-- Input zero is the time-dependent drive. The remaining inputs are state coordinates. -/
abbrev Flow (n : Nat) := Fin n → Form (n+1)

def lhs {n} (F : Flow n) : Grid n n := fun i j =>
  (if i=j then const 1 else const 0) - (F i).coeff j.succ

def rhs {n} (F : Flow n) : Grid n (n+1) := fun i =>
  Fin.cases ((F i).coeff 0) fun j =>
    (if i=j then const 1 else const 0) + (F i).coeff j.succ

def trajectory {n} (P : Grid n (n+1)) (u : Nat → Enclosed) : Nat → Fin n → Enclosed
  | 0 => fun _ => const 0
  | k+1 =>
    let prev := trajectory P u k
    let next := Vector.ofFn fun i =>
      dot (fun j => P i j.succ) prev + P i 0*(u k+u (k+1))
    fun i => next[i]

private theorem advance {n} (P : Grid n (n+1)) (u : Nat → Enclosed) (k : Nat) (i) :
    (trajectory P u (k+1) i).val =
    (∑ j, (P i j.succ).val*(trajectory P u k j).val) + (P i 0).val*((u k).val+(u (k+1)).val) := by
  simp [trajectory,dot_val]

/-- A positive-pivot factorization yields an exact trajectory of the implicit
trapezoidal stamp. The forms include the factor of half a time step. -/
theorem balance {n} (F : Flow n) (P : Grid n (n+1)) (u : Nat → Enclosed)
    (certificate : ∀ i k, ∑ j, (lhs F i j).val*(P j k).val = (rhs F i k).val)
    (k : Nat) (i : Fin n) :
    let x := trajectory P u
    let input := fun t => Fin.cases (u t).val (fun j => (x t j).val)
    (x (k+1) i).val = (x k i).val + ((F i).eval (input k) + (F i).eval (input (k+1))) := by
  dsimp only
  let x := trajectory P u
  let v := (u k).val+(u (k+1)).val
  have evolve (j) : (x (k+1) j).val = (∑ z, (P j z.succ).val*(x k z).val) + (P j 0).val*v := advance ..
  have matrix : ∑ j, (lhs F i j).val*(x (k+1) j).val =
      (∑ z : Fin n, (rhs F i z.succ).val*(x k z).val) + (rhs F i 0).val*v := by
    simp_rw [evolve, mul_add, Finset.sum_add_distrib, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,certificate]
  simp only [lhs,rhs,Fin.cases_zero,Fin.cases_succ,sub_val,add_val,sub_mul,add_mul,
    Finset.sum_sub_distrib,Finset.sum_add_distrib] at matrix
  simp [apply_ite,ite_mul] at matrix
  simp only [(F i).sound]
  conv_rhs => enter [2,1]; rw [Fin.sum_univ_succ]
  conv_rhs => enter [2,2]; rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ]
  dsimp only [v,x] at matrix
  linear_combination matrix

end
end SpiceSmtBench.LinearTransient
