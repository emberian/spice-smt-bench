import SpiceSmtBench.LinearTransient

namespace SpiceSmtBench.TransientWindows
open LinearTransient Enclosed

/-- Fixed-point endpoints for replaying a matrix trajectory. Products accumulate
at double precision and are rounded outwards once per output coordinate. -/
structure Window where
  lo : Int
  hi : Int
  deriving Repr

def scale : Int := 1000000000000000000
def holds (b : Window) (x : ℝ) := (b.lo:ℝ) ≤ (scale:ℝ)*x ∧ (scale:ℝ)*x ≤ (b.hi:ℝ)
def fits (x : Enclosed) (b : Window) : Bool := x.inside ((b.lo:ℚ)/scale) ((b.hi:ℚ)/scale)

theorem holds_of_fits {b x} (h : fits x b) : holds b x.val := by
  have m := bounds h
  push_cast at m
  have hs : (0:ℝ) < scale := by norm_num [scale]
  exact ⟨by simpa [mul_comm] using (div_le_iff₀ hs).mp m.1,
    by simpa [mul_comm] using (le_div_iff₀ hs).mp m.2⟩

private def sumBox (a b : Window) : Window := ⟨a.lo+b.lo,a.hi+b.hi⟩
private def prodBox (a b : Window) : Window :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩
private def dotBox {n} (a b : Fin n → Window) : Window :=
  match n with
  | 0 => ⟨0,0⟩
  | n+1 => sumBox (prodBox (a 0) (b 0)) (dotBox (fun i : Fin n => a i.succ) (fun i => b i.succ))
private def rounded (a : Window) : Window := ⟨a.lo/scale,-((-a.hi)/scale)⟩

private def between (a : Window) (x : ℝ) := (a.lo:ℝ) ≤ x ∧ x ≤ (a.hi:ℝ)
private theorem plus_ok {a b x y} (ha : between a x) (hb : between b y) : between (sumBox a b) (x+y) := by
  simpa only [between,sumBox,Int.cast_add] using And.intro (add_le_add ha.1 hb.1) (add_le_add ha.2 hb.2)

private theorem prod_ok {a b x y} (ha : between a x) (hb : between b y) : between (prodBox a b) (x*y) := by
  let A : LeanCert.Core.IntervalRat := ⟨a.lo,a.hi,by exact_mod_cast ha.1.trans ha.2⟩
  let B : LeanCert.Core.IntervalRat := ⟨b.lo,b.hi,by exact_mod_cast hb.1.trans hb.2⟩
  have ax : x ∈ A := by simpa [A,LeanCert.Core.IntervalRat.mem_def,between] using ha
  have by' : y ∈ B := by simpa [B,LeanCert.Core.IntervalRat.mem_def,between] using hb
  simpa [between,prodBox,LeanCert.Core.IntervalRat.mem_def,LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,LeanCert.Core.IntervalRat.max4,A,B,or_assoc] using LeanCert.Core.IntervalRat.mem_mul ax by'

private theorem dot_ok {n} (a b : Fin n → Window) (x y : Fin n → ℝ)
    (ha : ∀ i, between (a i) (x i)) (hb : ∀ i, between (b i) (y i)) :
    between (dotBox a b) (∑ i, x i*y i) := by
  induction n with
  | zero => simp [dotBox,between]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    exact plus_ok (prod_ok (ha 0) (hb 0)) (ih _ _ _ _ (fun j => ha j.succ) (fun j => hb j.succ))

private theorem round_ok {a x} (h : between a ((scale:ℝ)*((scale:ℝ)*x))) : holds (rounded a) x := by
  have down (z : Int) : ((z / scale : Int):ℝ)*(scale:ℝ) ≤ z := by
    exact_mod_cast Int.ediv_mul_le z (by decide : scale ≠ 0)
  have low := down a.lo
  have high := down (-a.hi)
  simp only [Int.cast_neg] at high
  obtain ⟨l,u⟩ := h
  dsimp [holds, rounded]
  push_cast
  norm_num [scale] at *; constructor <;> linarith

def boxes {n} (P : Fin n → Fin (n+1) → Window) (u : Nat → Window) : Nat → Fin n → Window
  | 0 => fun _ => ⟨0,0⟩
  | k+1 =>
    let prev := boxes P u k
    let x := Fin.cases (sumBox (u k) (u (k+1))) prev
    let next := Vector.ofFn fun i => rounded (dotBox (P i) x)
    fun i => next[i]

theorem boxes_sound {n} (P : Grid n (n+1)) (u : Nat → Enclosed)
    (T : Fin n → Fin (n+1) → Window) (U : Nat → Window)
    (hp : ∀ i j, holds (T i j) (P i j).val) (k : Nat) (hu : ∀ j ≤ k, holds (U j) (u j).val) :
    ∀ i, holds (boxes T U k i) (trajectory P u k i).val := by
  induction k with
  | zero => intro i; simp [boxes,trajectory,holds]
  | succ k ih =>
    have prev := ih (fun j hj => hu j (Nat.le_succ_of_le hj))
    intro i
    let z : Fin (n+1) → ℝ := Fin.cases ((u k).val+(u (k+1)).val) (fun j => (trajectory P u k j).val)
    let X : Fin (n+1) → Window := Fin.cases (sumBox (U k) (U (k+1))) (boxes T U k)
    have inz : ∀ j, between (X j) ((scale:ℝ)*z j) := by
      intro j; refine Fin.cases ?_ (fun j => prev j) j
      change between _ ((scale:ℝ)*((u k).val+(u (k+1)).val))
      rw [mul_add]; exact plus_ok (hu k (by omega)) (hu (k+1) (by omega))
    have b := dot_ok (T i) X (fun j => (scale:ℝ)*(P i j).val) (fun j => (scale:ℝ)*z j) (hp i) inz
    simp_rw [show ∀ a b : ℝ, ((scale:ℝ)*a)*((scale:ℝ)*b) = (scale:ℝ)*((scale:ℝ)*(a*b)) by intros; ring,
      ← Finset.mul_sum] at b
    have r := round_ok b
    rw [Fin.sum_univ_succ] at r
    simp [boxes,trajectory,dot_val,z,X,add_comm] at r ⊢
    exact r

/-- Enclose a dot product after rounding the accumulated products back to
the coordinate scale. -/
def applyRow {n} (a b : Fin n → Window) := rounded (dotBox a b)
theorem applyRow_ok {n} (a b : Fin n → Window) (x y : Fin n → ℝ)
    (hx : ∀ j, holds (a j) (x j)) (hy : ∀ j, holds (b j) (y j)) :
    holds (applyRow a b) (∑ j, x j * y j) := by
  have m := dot_ok a b (fun j => (scale:ℝ)*x j) (fun j => (scale:ℝ)*y j) hx hy
  simp_rw [show ∀ z w : ℝ, ((scale:ℝ)*z)*((scale:ℝ)*w) = (scale:ℝ)*((scale:ℝ)*(z*w)) by intros; ring,
    ← Finset.mul_sum] at m
  exact round_ok m

def add := sumBox
theorem add_ok {a b x y} (h : holds a x) (g : holds b y) : holds (add a b) (x+y) := by
  unfold holds; rw [mul_add]; exact plus_ok h g

end SpiceSmtBench.TransientWindows
