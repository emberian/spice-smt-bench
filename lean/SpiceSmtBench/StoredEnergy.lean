import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace SpiceSmtBench.StoredEnergy

abbrev State (n : Nat) := Fin n → ℝ
abbrev Coeff (n : Nat) := Fin n → Fin n → ℝ
noncomputable section

def action {n} (m : Coeff n) (x : State n) (i : Fin n) := ∑ j, m i j*x j
def work {n} (x y : State n) := ∑ i, x i*y i
def energy {n} (m : Coeff n) (x : State n) := work x (action m x)
def amplitude {n} (m : Coeff n) (x : State n) := Real.sqrt (energy m x)

theorem swap {n} (m : Coeff n) (x y : State n) (hs : ∀ i j, m i j = m j i) :
    work x (action m y) = work y (action m x) := by
  simp_rw [work,action,Finset.mul_sum]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; rw [hs i j]; ring

private theorem sub_left {n} (x y z : State n) :
    work (fun i => x i-y i) z = work x z - work y z := by simp [work,sub_mul,Finset.sum_sub_distrib]
private theorem sub_right {n} (x y z : State n) :
    work x (fun i => y i-z i) = work x y - work x z := by simp [work,mul_sub,Finset.sum_sub_distrib]
private theorem apply_sub {n} (m : Coeff n) (x y : State n) :
    action m (fun i => x i-y i) = fun i => action m x i - action m y i := by
  funext i; simp [action,mul_sub,Finset.sum_sub_distrib]

/-- A lower bound on each row's diagonal-dominance margin also bounds the
energy of every coordinate. -/
theorem lower {n} (m : Coeff n) (w x : State n) (sym : ∀ i j, m i j=m j i)
    (h : ∀ i, w i ^ 2 + (∑ j, if i=j then 0 else |m i j|) ≤ m i i) (i : Fin n) :
    (w i*x i)^2 ≤ energy m x := by
  let off := fun a b => if a=b then 0 else |m a b|
  have os (a b) : off a b=off b a := by simp [off,eq_comm,sym a b]
  have diag (a) : (w a*x a)^2 + (∑ j, off a j) * (x a)^2 ≤ m a a*(x a)^2 := by
    simpa only [add_mul,mul_pow] using mul_le_mul_of_nonneg_right (h a) (sq_nonneg (x a))
  have cell (a b) : -(off a b)*((x a)^2+(x b)^2) ≤
      2*(m a b*x a*x b - (if a=b then m a a*(x a)^2 else 0)) := by
    by_cases e : a=b
    · subst b; simp [off]; nlinarith
    · simp only [off,e,reduceIte,sub_zero]
      by_cases P : 0 ≤ m a b
      · rw [abs_of_nonneg P]; nlinarith only [mul_nonneg P (sq_nonneg (x a+x b))]
      · rw [abs_of_neg (lt_of_not_ge P)]
        nlinarith only [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge P) (sq_nonneg (x a-x b))]
  have C := Finset.sum_le_sum (s := Finset.univ) fun a _ =>
    Finset.sum_le_sum (s := Finset.univ) fun b _ => cell a b
  have D := Finset.sum_le_sum (s := Finset.univ) fun a _ => diag a
  have comm : ∑ a, ∑ b, off a b * x b ^ 2 = ∑ a, (∑ j, off a j)*x a ^ 2 := by
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; rw [os]
  simp only [neg_mul,mul_add,Finset.sum_neg_distrib,Finset.sum_add_distrib,← Finset.sum_mul,
    ← Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true] at C
  have form : (∑ a, ∑ b, m a b*x a*x b) = energy m x := by
    simp only [energy,work,action,Finset.mul_sum]; congr 1; funext a; congr 1; funext b; ring
  simp only [Finset.sum_add_distrib] at D
  rw [comm,form] at C
  have single := Finset.single_le_sum (s := Finset.univ) (f := fun j => (w j*x j)^2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  linarith only [C,D,single]

theorem coord {n} (m : Coeff n) (w x : State n) (i : Fin n) (hw : 0 ≤ w i)
    (h : (w i*x i)^2 ≤ energy m x) : w i*|x i| ≤ amplitude m x := by
  simpa only [amplitude,Real.sqrt_sq_eq_abs,abs_mul,abs_of_nonneg hw] using Real.sqrt_le_sqrt h

private theorem energy_nonneg {n} [Nonempty (Fin n)] (m : Coeff n) (w x : State n)
    (h : ∀ i, (w i*x i)^2 ≤ energy m x) : 0 ≤ energy m x := by
  obtain ⟨i⟩ := ‹Nonempty (Fin n)›; exact (sq_nonneg _).trans (h i)

theorem euler_bound {n} (m : Coeff n) (x y : State n) (loss : ℝ) (sym : ∀ i j, m i j=m j i)
    (pos : ∀ z, 0 ≤ energy m z) (dissipation : work y (action m (fun i => y i-x i)) ≤ amplitude m y * loss)
    (hl : 0 ≤ loss) : amplitude m y ≤ amplitude m x + 2*loss := by
  have q := pos (fun i => y i-x i)
  simp only [energy,apply_sub,sub_left,sub_right] at q
  rw [swap m x y sym] at q
  rw [apply_sub,sub_right] at dissipation
  have a : (amplitude m x)^2 = work x (action m x) := Real.sq_sqrt (pos x)
  have b : (amplitude m y)^2 = work y (action m y) := Real.sq_sqrt (pos y)
  have xp : 0 ≤ amplitude m x := Real.sqrt_nonneg _
  by_contra! bad
  have m1 := mul_pos (sub_pos.mpr bad) (show 0 < amplitude m y by linarith)
  nlinarith only [q,dissipation,a,b,m1,mul_nonneg xp (by linarith : 0 ≤ amplitude m y-amplitude m x)]

theorem trapezoidal_bound {n} (m : Coeff n) (x y : State n) (loss : ℝ) (sym : ∀ i j, m i j=m j i)
    (pos : ∀ z, 0 ≤ energy m z)
    (dissipation : work (fun i => y i+x i) (action m (fun i => y i-x i)) ≤
      (amplitude m y+amplitude m x)*loss) (hl : 0 ≤ loss) :
    amplitude m y ≤ amplitude m x+loss := by
  have plus (z : State n) : work (fun i => y i+x i) z = work y z + work x z := by
    simp [work,add_mul,Finset.sum_add_distrib]
  rw [apply_sub,plus,sub_right,sub_right,swap m x y sym] at dissipation
  have a : (amplitude m x)^2 = work x (action m x) := Real.sq_sqrt (pos x)
  have b : (amplitude m y)^2 = work y (action m y) := Real.sq_sqrt (pos y)
  by_contra! bad
  have xp : 0 ≤ amplitude m x := Real.sqrt_nonneg _
  have h := mul_pos (sub_pos.mpr bad) (show 0 < amplitude m x+amplitude m y by linarith)
  nlinarith only [h,a,b,dissipation]

theorem passive {n} (k : Coeff n) (x : State n) (diag : ∀ i, k i i ≤ 0)
    (skew : ∀ i j, i≠j → k i j = -k j i) : work x (action k x) ≤ 0 := by
  let cell := fun i j => x i*(k i j*x j)
  have crossed : ∑ i, ∑ j, cell j i = ∑ i, ∑ j, cell i j := Finset.sum_comm
  have term (i j) : cell i j + cell j i ≤ 0 := by
    dsimp [cell]
    by_cases e : i=j
    · subst j; nlinarith only [mul_nonpos_of_nonpos_of_nonneg (diag i) (sq_nonneg (x i))]
    · rw [skew i j e]; ring_nf; rfl
  have h := Finset.sum_nonpos (s := Finset.univ) fun i _ =>
    Finset.sum_nonpos (s := Finset.univ) fun j _ => term i j
  simp only [Finset.sum_add_distrib,crossed] at h
  simp only [work,action,Finset.mul_sum]
  change ∑ i, ∑ j, cell i j ≤ 0
  linarith

theorem summand_budget {n} (x r w b : State n) (A : ℝ)
    (hx : ∀ i, w i*|x i| ≤ A) (hr : ∀ i, |r i| ≤ w i*b i) (hb : ∀ i, 0 ≤ b i) :
    work x r ≤ A * ∑ i, b i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  calc x i*r i ≤ |x i| *|r i| := (le_abs_self _).trans_eq (abs_mul ..)
       _ ≤ |x i| *(w i*b i) := mul_le_mul_of_nonneg_left (hr i) (abs_nonneg _)
       _ = (w i*|x i|)*b i := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right (hx i) (hb i)

end
end SpiceSmtBench.StoredEnergy
