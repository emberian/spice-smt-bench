import SpiceSmtBench.StitchedMaterial
import SpiceSmtBench.StitchedResidualData
import SpiceSmtBench.SlotReplay

namespace SpiceSmtBench.Stitched
open TransientWindows PolynomialEnvelope StoredEnergy
set_option maxRecDepth 30000
noncomputable section
private theorem zero_ok : holds zeroW 0 := by simp [holds,zeroW]
private theorem neg_ok {b x} (h : holds b x) : holds (negW b) (-x) := by
  simpa [holds,negW] using And.intro (neg_le_neg h.2) (neg_le_neg h.1)
private theorem point_ok (z : Int) : holds (pointW z) ((z:ℝ)/1000000000) := by
  simp [holds,scale,pointW]; constructor <;> linarith
private theorem sum_ok {ι} (xs : List ι) (w : ι → Window) (v : ι → ℝ) (h : ∀ x, holds (w x) (v x)) :
    holds (sumW (xs.map w)) (xs.map v).sum := by
  induction xs with
  | nil => exact zero_ok
  | cons x xs ih => exact add_ok (h x) ih

private theorem sparse_ok (s : List (Fin 16)) (m v : Fin 16 → Window) (x y : Fin 16 → ℝ)
    (hs : supported s m) (hx : ∀ j, holds (m j) (x j)) (hy : ∀ j, holds (v j) (y j))
    (small : ∀ j, |y j|≤4) : holds (sparseDot s m v) (∑ j, x j*y j) := by
  let f := fun j => x j*y j
  let rest := Finset.univ \ s.toFinset
  have bound (j : Fin 16) (hj : j ∈ rest) : |f j|≤4/100000000000 := by
    have out : j ∉ s := by simpa [rest] using hj
    have b := hs.2 j out
    have h := hx j
    have low : (-10000000:ℝ) ≤ (m j).lo := by exact_mod_cast b.1
    have high : ((m j).hi:ℝ) ≤ 10000000 := by exact_mod_cast b.2
    have mag : |x j|≤1/100000000000 := by
      rcases h with ⟨h1,h2⟩; norm_num [scale] at h1 h2
      apply abs_le.mpr; constructor <;> linarith
    rw [show f j = x j*y j by rfl,abs_mul]
    exact (mul_le_mul mag (small j) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have rem : |∑ j ∈ rest, f j| ≤ 1/1000000000 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum bound).trans
    simp only [Finset.sum_const,nsmul_eq_mul]
    have card : rest.card≤16 := Finset.card_le_univ _
    have card' : (rest.card:ℝ)≤16 := by exact_mod_cast card
    linarith
  have rest_ok : holds ⟨-1000000000,1000000000⟩ (∑ j ∈ rest, f j) := by
    obtain ⟨lo,hi⟩ := abs_le.mp rem
    norm_num [holds,scale]; constructor <;> linarith
  have stored (j) : holds (applyRow (fun _ : Fin 1 => m j) (fun _ => v j)) (f j) := by
    simpa only [Fin.sum_univ_one,f] using applyRow_ok _ _ _ _ (fun _ : Fin 1 => hx j) (fun _ => hy j)
  have exactSum := Finset.sum_sdiff (s₁ := s.toFinset) (s₂ := Finset.univ) (Finset.subset_univ _) (f := f)
  rw [List.sum_toFinset f hs.1] at exactSum
  exact exactSum ▸ add_ok rest_ok (sum_ok s _ _ stored)

private theorem reference_small (k : Fin 81) (b : Fin 10) (j : Fin 16) :
    |referenceValue k.val b j| ≤ 2 := by
  have all : ∀ (l : Fin 81) (t : Fin 10) (i : Fin 16), |traceData l.val t i| ≤ 2000000000 := by decide +kernel
  have H : |(traceData k.val b j : ℝ)| ≤ 2000000000 := by exact_mod_cast all k b j
  simp only [referenceValue,abs_div,show |(1000000000:ℝ)|=1000000000 by norm_num]
  linarith

def source (k : Nat) (i : Fin 16) : ℝ := port ((SlotLine.drive k).val+(SlotLine.drive (k+1)).val) 0 i
def forceTerm (k : Nat) (i : Fin 16) (b : Fin 10) : ℝ :=
  action (fun j l => (baseNetwork j l).val)
    (fun j => referenceValue (k+1) b j + referenceValue k b j) i +
  if b=0 then source k i else 0
def massTerm (k : Nat) (i : Fin 16) (a : Fin 4) (b : Fin 10) : ℝ :=
  action (fun j l => (baseMass a j l).val)
    (fun j => referenceValue (k+1) b j-referenceValue k b j) i

private theorem cubic_ok (k : Fin 80) (i : Fin 16) (t : Fin 20) :
    holds (cubicW k.val i t) (coefficient (forceTerm k.val i) (massTerm k.val i) t) := by
  have d (b j) : holds (deltaW k b j) (referenceValue (k.val+1) b j-referenceValue k.val b j) := by
    simpa [deltaW,referenceValue,sub_div] using point_ok (traceData (k.val+1) b j-traceData k b j)
  have p (b j) : holds (plusW k b j) (referenceValue (k.val+1) b j+referenceValue k.val b j) := by
    simpa [plusW,referenceValue,add_div] using point_ok (traceData (k.val+1) b j+traceData k b j)
  have s : holds (srcW k.val) ((1/5)*((SlotLine.drive k.val).val+(SlotLine.drive (k.val+1)).val)) := by
    let box : Fin 1 → Window := fun _ => ⟨200000000000000000,200000000000000000⟩
    have one : ∀ j, holds (box j) (1/5) := by intro; norm_num [box,holds,scale]
    have a := holds_of_fits (SlotLine.drive_verified ⟨k.val,by omega⟩)
    have b := holds_of_fits (SlotLine.drive_verified ⟨k.val+1,by omega⟩)
    exact (by simpa only [srcW,box,Fin.sum_univ_one] using applyRow_ok box _ _ _ one (fun _ => add_ok a b))
  have inp : holds (inputW k.val i) (source k.val i) := by
    fin_cases i <;> simp [inputW,source,port] <;> first | exact zero_ok | convert s using 1 <;> ring | convert neg_ok s using 1; ring
  have small (b : Fin 10) (j : Fin 16) := reference_small ⟨k.val+1,by omega⟩ b j
  have prev (b : Fin 10) (j : Fin 16) := reference_small ⟨k.val,by omega⟩ b j
  have f (b : Fin 10) : holds (valueW k.val i b) (forceTerm k.val i b) := by
    apply add_ok (sparse_ok _ _ _ _ _ (supports_valid.2 i) (fun j => holds_of_fits (matrix_check.2 i j)) (p b) (fun j => (abs_add_le ..).trans (by linarith [small b j,prev b j])))
    by_cases h : b=0 <;> simp only [h,reduceIte] <;> first | exact inp | exact zero_ok
  have z (t : Fin 4 × Fin 10) : holds (productW k.val i t) (massTerm k.val i t.1 t.2) :=
    sparse_ok _ _ _ _ _ (supports_valid.1 t.1 i) (fun j => holds_of_fits (matrix_check.1 t.1 i j)) (d t.2) (fun j => (abs_sub ..).trans (by linarith [small t.2 j,prev t.2 j]))
  unfold cubicW coefficient
  rw [sub_eq_add_neg]
  apply add_ok _ (neg_ok (sum_ok (products t) _ _ z))
  split <;> first | apply f | exact zero_ok

theorem residual_bound (k : Fin 80) (i : Fin 16) (h : stepCheck k.val) (a b c : ℝ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1) :
    |evaluate (mon3 a b c) (coefficient (forceTerm k.val i) (massTerm k.val i))| ≤ (limits i:ℝ)/scale := by
  apply (eval_abs_le _ _ (mon3_le ha hb hc)).trans
  apply (le_div_iff₀ (by norm_num [scale] : (0:ℝ)<scale)).mpr
  rw [Finset.sum_mul]
  have term (t : Fin 20) : |coefficient (forceTerm k.val i) (massTerm k.val i) t| * (scale:ℝ) ≤ magnitudeW (cubicW k.val i t) := by
    have w := cubic_ok k i t
    rw [← abs_of_pos (by norm_num [scale] : (0:ℝ)<scale),← abs_mul,mul_comm,abs_le]
    simp only [magnitudeW,Int.cast_max,Int.cast_neg]
    constructor <;> rcases w with ⟨l,u⟩ <;> grind
  exact (Finset.sum_le_sum (fun t _ => term t)).trans (by exact_mod_cast h i)

end
end SpiceSmtBench.Stitched
