import Mathlib.Tactic

namespace SpiceSmtBench.FinMesh

abbrev Grid (R : Type) := Nat → Nat → R

-- Upper potentials in volts, indexed from the source contact. Each row of
-- the 3 by 3 interior satisfies the Poisson supersolution inequality.
def barrier : Grid ℚ
  | 0, _ => 13/25
  | 1, 1 => 0.03420 | 1, _ => 0.01061
  | 2, 1 => -0.02993 | 2, _ => -0.04560
  | 3, 1 => 0.18295 | 3, _ => 0.13693
  | _, _ => 61/50

def axial {R} [Ring R] (p : Grid R) (i j : Nat) := p (i-1) j + p (i+1) j - 2*p i j
def lateral {R} [Ring R] (p : Grid R) (i j : Nat) :=
  (if j=0 then 0 else p i (j-1)-p i j) + (if j=2 then 0 else p i (j+1)-p i j)
def robin {R} [Field R] (gate : R) (p : Grid R) (i j : Nat) :=
  if j=1 then 0 else 3333333333333333/10000000000000000*(gate-p i j)

noncomputable def row (p : Grid ℝ) (gate dx dy : ℝ) (i j : Nat) :=
  (axial p i j/(dx*dx) + 3/250*(gate-p i j))*(dy*dy) +
    robin gate p i j*dy + lateral p i j

private def A (i j : Nat) := axial barrier i j/(4.95*4.95) + 3/250*(-0.12-barrier i j)
private def B := robin (-0.12) barrier
private def C := lateral barrier
private theorem endpoints (i j : Fin 3) :
    let k := i.val+1
    0 ≤ axial barrier k j ∧ 0 ≤ A k j ∧
    A k j*(1.5*1.5)+B k j*1.5+C k j ≤ 0 ∧ A k j*(1.75*1.75)+B k j*1.75+C k j ≤ 0 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem quadratic {a b c d : ℝ} (ha : 0 ≤ a) (lo : 3/2 ≤ d) (hi : d ≤ 7/4)
    (l : a*(1.5*1.5)+b*1.5+c ≤ 0) (r : a*(1.75*1.75)+b*1.75+c ≤ 0) :
    a*(d*d)+b*d+c ≤ 0 := by
  have e := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr lo) (sub_nonpos.mpr hi)
  nlinarith only [mul_nonpos_of_nonneg_of_nonpos ha e,
    mul_nonpos_of_nonpos_of_nonneg l (sub_nonneg.mpr hi),
    mul_nonpos_of_nonpos_of_nonneg r (sub_nonneg.mpr lo)]

noncomputable def W (i j : Nat) : ℝ := barrier i j

private theorem upperRow (i j : Fin 3) {dx dy : ℝ} (hx : 4.95 ≤ dx)
    (yl : 3/2 ≤ dy) (yh : dy ≤ 7/4) : row W (-0.12) dx dy (i.val+1) j ≤ 0 := by
  let k := i.val+1
  obtain ⟨hn,ha,hl,hh⟩ := endpoints i j
  have castAx : ((axial barrier k j : ℚ):ℝ) = axial W k j := by simp [axial,W]
  have castB : ((B k j : ℚ):ℝ) = robin (-0.12) W k j := by simp [B,robin,W]; split <;> push_cast <;> norm_num
  have castC : ((C k j : ℚ):ℝ) = lateral W k j := by simp [C,lateral,W,apply_ite Rat.cast]
  have castA : ((A k j : ℚ):ℝ) = axial W k j/(4.95*4.95)+3/250*(-0.12-W k j) := by
    simp [A,k,W,axial]
  have hn' : 0 ≤ axial W k j := castAx ▸ (Rat.cast_nonneg.mpr hn)
  have m := div_le_div_of_nonneg_left hn' (by norm_num : (0:ℝ)<4.95*4.95)
    (mul_self_le_mul_self (by norm_num) hx)
  have e1 := (Rat.cast_le (K := ℝ)).mpr hl
  have e2 := (Rat.cast_le (K := ℝ)).mpr hh
  change _ ≤ (0:ℚ) at hl hh
  push_cast at e1 e2
  have fact := quadratic (Rat.cast_nonneg.mpr ha) yl yh (by convert e1 using 1 <;> norm_num) (by convert e2 using 1 <;> norm_num)
  change (A k j:ℝ)*(dy*dy)+(B k j:ℝ)*dy+(C k j:ℝ) ≤ 0 at fact
  rw [castA,castB,castC] at fact
  dsimp only [row]
  exact le_trans (add_le_add_left (add_le_add_left (mul_le_mul_of_nonneg_right
    (add_le_add_left m _) (mul_self_nonneg dy)) _) _) fact

/-- Discrete comparison with a strict top-gate term. Contacts have zero
excess, so a positive maximum would have to occur in an interior cell. -/
theorem enclosure (p : Grid ℝ) {gate dx dy : ℝ} (hg : gate ≤ -0.12) (hx : 4.95 ≤ dx)
    (yl : 3/2 ≤ dy) (yh : dy ≤ 7/4)
    (src : ∀ j : Fin 3, p 0 j = W 0 j) (drain : ∀ j : Fin 3, p 4 j = W 4 j)
    (charge : ∀ i j : Fin 3, 0 ≤ row p gate dx dy (i.val+1) j) :
    ∀ (i : Fin 5) (j : Fin 3), p i j ≤ W i j := by
  let diff (s : Fin 5 × Fin 3) := p s.1 s.2-W s.1 s.2
  obtain ⟨ij,_,maximal⟩ := Finset.exists_max_image Finset.univ diff Finset.univ_nonempty
  intro ix jx
  by_contra! fail
  obtain ⟨i,j⟩ := ij
  have maximum (a b : Nat) (ha : a < 5 := by omega) (hb : b < 3 := by omega) :
      p a b-W a b ≤ p i j-W i j := maximal (⟨a,ha⟩,⟨b,hb⟩) (Finset.mem_univ _)
  have hot : W i j < p i j := by linarith only [maximum ix jx, fail]
  have i0 : i.val ≠ 0 := by intro e; simp [e,src] at hot
  have i4 : i.val ≠ 4 := by intro e; simp [e,drain] at hot
  let k : Fin 3 := ⟨i.val-1,by omega⟩
  have succ : k.val+1=i.val := by dsimp [k]; omega
  have l := charge k j
  have h := upperRow k j hx yl yh
  rw [succ] at l h
  have ax : axial p i j ≤ axial W i j := by
    dsimp [axial]; linarith only [maximum (i.val-1) j,maximum (i.val+1) j]
  have lat : lateral p i j ≤ lateral W i j := by
    have adj (n : Nat) (hn : n < 3) : p i n-p i j ≤ W i n-W i j := by
      linarith only [maximum i n (by omega) hn]
    fin_cases j <;> simp [lateral] at adj ⊢
    · exact adj 1 (by decide)
    · linarith only [adj 0 (by decide),adj 2 (by decide)]
    · exact adj 1 (by decide)
  have gateLt : gate-p i j < -0.12-W i j := by linarith
  have rob : robin gate p i j ≤ robin (-0.12) W i j := by
    unfold robin; split <;> first | rfl | exact mul_le_mul_of_nonneg_left gateLt.le (by norm_num)
  have rx := div_le_div_of_nonneg_right ax (mul_self_nonneg dx)
  have ry := mul_le_mul_of_nonneg_right rob (by linarith : 0 ≤ dy)
  have strict := mul_lt_mul_of_pos_right (add_lt_add_of_le_of_lt rx (mul_lt_mul_of_pos_left gateLt
    (by norm_num : (0:ℝ)<3/250))) (mul_pos (by linarith : 0<dy) (by linarith : 0<dy))
  dsimp only [row] at l h
  linarith only [strict,ry,lat,l,h]

end SpiceSmtBench.FinMesh
