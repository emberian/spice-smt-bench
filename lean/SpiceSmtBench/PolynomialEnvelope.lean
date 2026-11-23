import SpiceSmtBench.StoredEnergy
import SpiceSmtBench.TransientWindows

namespace SpiceSmtBench.PolynomialEnvelope
open StoredEnergy TransientWindows
noncomputable section

def mon1 (a b c : ℝ) : Fin 4 → ℝ := ![1, a, b, c]
def mon2 (a b c : ℝ) : Fin 10 → ℝ := ![1, a, b, c, a*a, a*b, a*c, b*b, b*c, c*c]
def mon3 (a b c : ℝ) : Fin 20 → ℝ := ![1, a, b, c, a*a, a*b, a*c, b*b, b*c, c*c, a*a*a, a*a*b, a*a*c, a*b*b, a*b*c, a*c*c, b*b*b, b*b*c, b*c*c, c*c*c]

def evaluate {m} (v f : Fin m → ℝ) := ∑ i, v i*f i

theorem evaluate_add {m} (v f g : Fin m → ℝ) :
    evaluate v (fun i => f i+g i) = evaluate v f + evaluate v g := by
  simp [evaluate,mul_add,Finset.sum_add_distrib]

theorem evaluate_sub {m} (v f g : Fin m → ℝ) :
    evaluate v (fun i => f i-g i) = evaluate v f - evaluate v g := by
  simp [evaluate,mul_sub,Finset.sum_sub_distrib]

theorem action_evaluate {n m} (A : Coeff n) (v : Fin m → ℝ) (f : Fin m → State n) (i) :
    action A (fun j => evaluate v (fun b => f b j)) i =
      evaluate v (fun b => action A (f b) i) := by
  simp only [action,evaluate,Finset.mul_sum]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro b _; ring

/-- Pairs of affine and quadratic monomials contributing to each cubic coefficient. -/
def products : Fin 20 → List (Fin 4 × Fin 10) :=
  ![[(0,0)], [(0,1), (1,0)], [(0,2), (2,0)], [(0,3), (3,0)], [(0,4), (1,1)], [(0,5), (1,2), (2,1)], [(0,6), (1,3), (3,1)], [(0,7), (2,2)], [(0,8), (2,3), (3,2)], [(0,9), (3,3)], [(1,4)], [(1,5), (2,4)], [(1,6), (3,4)], [(1,7), (2,5)], [(1,8), (2,6), (3,5)], [(1,9), (3,6)], [(2,7)], [(2,8), (3,7)], [(2,9), (3,8)], [(3,9)]]

def coefficient (f : Fin 10 → ℝ) (z : Fin 4 → Fin 10 → ℝ) (i : Fin 20) :=
  (if h : i.val<10 then f ⟨i.val,h⟩ else 0) - ((products i).map (fun p => z p.1 p.2)).sum

theorem collect (a b c : ℝ) (f : Fin 10 → ℝ) (z : Fin 4 → Fin 10 → ℝ) :
    evaluate (mon3 a b c) (coefficient f z) =
    evaluate (mon2 a b c) f - evaluate (mon1 a b c) (fun i => evaluate (mon2 a b c) (z i)) := by
  simp [evaluate,mon1,mon2,mon3,coefficient,products,Fin.sum_univ_succ]
  ring

theorem mon3_le {a b c : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1) (i : Fin 20) :
    |mon3 a b c i| ≤ 1 := by
  have prod {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x*y| ≤ 1 := by
    rw [abs_mul]; simpa using mul_le_mul hx hy (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  fin_cases i
  · exact (by norm_num : |(1:ℝ)|≤1)
  · exact ha
  · exact hb
  · exact hc
  · exact (prod ha ha)
  · exact (prod ha hb)
  · exact (prod ha hc)
  · exact (prod hb hb)
  · exact (prod hb hc)
  · exact (prod hc hc)
  · exact (prod (prod ha ha) ha)
  · exact (prod (prod ha ha) hb)
  · exact (prod (prod ha ha) hc)
  · exact (prod (prod ha hb) hb)
  · exact (prod (prod ha hb) hc)
  · exact (prod (prod ha hc) hc)
  · exact (prod (prod hb hb) hb)
  · exact (prod (prod hb hb) hc)
  · exact (prod (prod hb hc) hc)
  · exact (prod (prod hc hc) hc)

theorem eval_abs_le {n} (v f : Fin n → ℝ) (h : ∀ i, |v i| ≤ 1) :
    |evaluate v f| ≤ ∑ i, |f i| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum; intro i _
  rw [abs_mul]; simpa using mul_le_mul_of_nonneg_right (h i) (abs_nonneg (f i))

end
end SpiceSmtBench.PolynomialEnvelope
