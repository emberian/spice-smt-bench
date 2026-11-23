import SpiceSmtBench.PhysicsModels

/-!
# Verified Exact Rational Interval Arithmetic & Branch-and-Bound Paving Checker

Implements:
1. Exact arbitrary-precision rational endpoints `QRat` (`num : Int`, `den : Nat`, `0 < den`).
2. Soundness of `QInterval` arithmetic (`add`, `sub`, `neg`, `mul`, `divPos`, `exp`) and scaling-and-squaring
   transcendental `expLowerQ` (`(1 + x / 2^m)^(2^m) ≤ exp(x)`), proved from `TranscendentalField` laws
   with zero unproved obligations.
3. A verified n-dimensional branch-and-bound `PavingTree` checker (`verifyPaving`) with its
   machine-checked soundness theorem `paving_unsat_sound`, certifying Path A (`UNSAT` paving replay).
-/

namespace SpiceSmtBench.IntervalCheck

/-- Exact rational number `num / den` with strictly positive denominator `0 < den`. -/
structure QRat where
  num : Int
  den : Nat
  den_pos : 0 < den := by decide
  deriving DecidableEq, Repr

namespace QRat

def ofInt (n : Int) : QRat := ⟨n, 1, by decide⟩

def zero : QRat := ⟨0, 1, by decide⟩
def one  : QRat := ⟨1, 1, by decide⟩

/-- Exact rational comparison `a ≤ b ↔ a.num * b.den ≤ b.num * a.den`. -/
def le (a b : QRat) : Prop :=
  a.num * (b.den : Int) ≤ b.num * (a.den : Int)

def lt (a b : QRat) : Prop :=
  a.num * (b.den : Int) < b.num * (a.den : Int)

instance (a b : QRat) : Decidable (le a b) := by
  unfold le
  infer_instance

instance (a b : QRat) : Decidable (lt a b) := by
  unfold lt
  infer_instance

def add (a b : QRat) : QRat :=
  ⟨a.num * (b.den : Int) + b.num * (a.den : Int), a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def sub (a b : QRat) : QRat :=
  ⟨a.num * (b.den : Int) - b.num * (a.den : Int), a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def neg (a : QRat) : QRat :=
  ⟨-a.num, a.den, a.den_pos⟩

def mul (a b : QRat) : QRat :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def half (a : QRat) : QRat :=
  ⟨a.num, a.den * 2, Nat.mul_pos a.den_pos (by decide)⟩

def halfPow : Nat → QRat → QRat
  | 0, q => q
  | m + 1, q => halfPow m (half q)

def iterSq : Nat → QRat → QRat
  | 0, q => q
  | m + 1, q =>
    let r := iterSq m q
    mul r r

/-- Embed `QRat` into any `TranscendentalField R`. -/
def eval {R : Type} (TF : TranscendentalField R) (q : QRat) : R :=
  TF.ofRat q.num q.den

theorem eval_le_iff {R : Type} (TF : TranscendentalField R) (a b : QRat) :
    TF.le (eval TF a) (eval TF b) ↔ le a b :=
  TF.ofRat_le_iff a.num b.num a.den b.den a.den_pos b.den_pos

theorem eval_lt_iff {R : Type} (TF : TranscendentalField R) (a b : QRat) :
    TF.lt (eval TF a) (eval TF b) ↔ lt a b :=
  TF.ofRat_lt_iff a.num b.num a.den b.den a.den_pos b.den_pos

theorem eval_zero {R : Type} (TF : TranscendentalField R) :
    eval TF zero = TF.zero :=
  TF.zero_eq_ofRat.symm

theorem eval_one {R : Type} (TF : TranscendentalField R) :
    eval TF one = TF.one :=
  TF.one_eq_ofRat.symm

theorem eval_add {R : Type} (TF : TranscendentalField R) (a b : QRat) :
    eval TF (add a b) = TF.add (eval TF a) (eval TF b) :=
  (TF.ofRat_add a.num b.num a.den b.den a.den_pos b.den_pos).symm

theorem eval_sub {R : Type} (TF : TranscendentalField R) (a b : QRat) :
    eval TF (sub a b) = TF.sub (eval TF a) (eval TF b) :=
  (TF.ofRat_sub a.num b.num a.den b.den a.den_pos b.den_pos).symm

theorem eval_neg {R : Type} (TF : TranscendentalField R) (a : QRat) :
    eval TF (neg a) = TF.neg (eval TF a) :=
  (TF.ofRat_neg a.num a.den a.den_pos).symm

theorem eval_mul {R : Type} (TF : TranscendentalField R) (a b : QRat) :
    eval TF (mul a b) = TF.mul (eval TF a) (eval TF b) :=
  (TF.ofRat_mul a.num b.num a.den b.den a.den_pos b.den_pos).symm

theorem eval_half {R : Type} (TF : TranscendentalField R) (a : QRat) :
    eval TF (half a) = TF.div (eval TF a) (TF.ofInt 2) := by
  unfold eval half
  rw [TF.ofInt_eq_ofRat 2]
  have h := TF.ofRat_div_pos a.num a.den 2 1 a.den_pos (by decide) (by decide)
  have hm : a.num * ((1 : Nat) : Int) = a.num := Int.mul_one a.num
  have h2 : ((2 : Nat) : Int) = 2 := rfl
  rw [hm, h2] at h
  exact h.symm

end QRat

/-- Iterated squaring on `R` for scaling-and-squaring `exp` lower bounds. -/
def iterSqR {R : Type} (TF : TranscendentalField R) : Nat → R → R
  | 0, u => u
  | m + 1, u => TF.mul (iterSqR TF m u) (iterSqR TF m u)

/-- Iterated halving `x / 2^m` on `R`. -/
def halfPowR {R : Type} (TF : TranscendentalField R) : Nat → R → R
  | 0, x => x
  | m + 1, x => halfPowR TF m (TF.div x (TF.ofInt 2))

theorem iterSqR_nonneg {R : Type} (TF : TranscendentalField R) (m : Nat) (u : R)
    (hu : TF.le TF.zero u) : TF.le TF.zero (iterSqR TF m u) := by
  induction m with
  | zero => exact hu
  | succ k ih =>
    unfold iterSqR
    exact TF.mul_nonneg _ _ ih ih

/-- Scaling-and-squaring lower bound `(1 + x / 2^m)^(2^m) ≤ exp(x)` whenever `0 ≤ 1 + x / 2^m`. -/
theorem exp_ge_iterSq_one_add_halfPow {R : Type} (TF : TranscendentalField R) :
    ∀ (m : Nat) (x : R),
      TF.le TF.zero (TF.add TF.one (halfPowR TF m x)) →
      TF.le (iterSqR TF m (TF.add TF.one (halfPowR TF m x))) (TF.exp x)
  | 0, x, _ => by
    unfold iterSqR halfPowR
    exact TF.one_add_le_exp x
  | m + 1, x, hx => by
    unfold iterSqR halfPowR
    unfold halfPowR at hx
    let y := TF.div x (TF.ofInt 2)
    have ih := exp_ge_iterSq_one_add_halfPow TF m y hx
    have hnonneg := iterSqR_nonneg TF m (TF.add TF.one (halfPowR TF m y)) hx
    have hsq := TF.sq_mono_nonneg _ (TF.exp y) hnonneg ih
    have hexp2 : TF.mul (TF.exp y) (TF.exp y) = TF.exp x := by
      rw [← TF.exp_add y y]
      rw [TF.div_two_add_self x]
    rw [hexp2] at hsq
    exact hsq

theorem eval_halfPow {R : Type} (TF : TranscendentalField R) :
    ∀ (m : Nat) (q : QRat), QRat.eval TF (QRat.halfPow m q) = halfPowR TF m (QRat.eval TF q)
  | 0, _ => rfl
  | m + 1, q => by
    unfold QRat.halfPow halfPowR
    rw [eval_halfPow TF m (QRat.half q)]
    rw [QRat.eval_half TF q]

theorem eval_iterSq {R : Type} (TF : TranscendentalField R) :
    ∀ (m : Nat) (q : QRat), QRat.eval TF (QRat.iterSq m q) = iterSqR TF m (QRat.eval TF q)
  | 0, _ => rfl
  | m + 1, q => by
    unfold QRat.iterSq iterSqR
    rw [QRat.eval_mul TF]
    rw [eval_iterSq TF m q]

/-- Rational scaling-and-squaring `exp` lower bound:
    if `0 ≤ 1 + q / 2^m` and `eval q ≤ x`, then `eval (iterSq m (1 + q / 2^m)) ≤ exp(x)`. -/
theorem exp_ge_qrat_iterSq {R : Type} (TF : TranscendentalField R)
    (m : Nat) (q : QRat) (x : R)
    (hbase : QRat.le QRat.zero (QRat.add QRat.one (QRat.halfPow m q)))
    (hqx : TF.le (QRat.eval TF q) x) :
    TF.le (QRat.eval TF (QRat.iterSq m (QRat.add QRat.one (QRat.halfPow m q)))) (TF.exp x) := by
  have hbaseR : TF.le TF.zero (TF.add TF.one (halfPowR TF m (QRat.eval TF q))) := by
    have h1 := (QRat.eval_le_iff TF QRat.zero (QRat.add QRat.one (QRat.halfPow m q))).mpr hbase
    rw [QRat.eval_zero TF, QRat.eval_add TF, QRat.eval_one TF, eval_halfPow TF m q] at h1
    exact h1
  have h_at_q : TF.le (QRat.eval TF (QRat.iterSq m (QRat.add QRat.one (QRat.halfPow m q))))
      (TF.exp (QRat.eval TF q)) := by
    rw [eval_iterSq TF m, QRat.eval_add TF, QRat.eval_one TF, eval_halfPow TF m q]
    exact exp_ge_iterSq_one_add_halfPow TF m (QRat.eval TF q) hbaseR
  exact TF.le_trans _ _ _ h_at_q (TF.exp_mono (QRat.eval TF q) x hqx)

/-- Closed rational interval `[lo, hi]`. -/
structure QInterval where
  lo : QRat
  hi : QRat
  deriving DecidableEq, Repr

/-- Membership of `x : R` inside `iv : QInterval`. -/
def memInterval {R : Type} (TF : TranscendentalField R) (iv : QInterval) (x : R) : Prop :=
  TF.le (QRat.eval TF iv.lo) x ∧ TF.le x (QRat.eval TF iv.hi)

namespace QInterval

def add (a b : QInterval) : QInterval := ⟨QRat.add a.lo b.lo, QRat.add a.hi b.hi⟩
def sub (a b : QInterval) : QInterval := ⟨QRat.sub a.lo b.hi, QRat.sub a.hi b.lo⟩
def neg (a : QInterval) : QInterval := ⟨QRat.neg a.hi, QRat.neg a.lo⟩

theorem add_sound {R : Type} (TF : TranscendentalField R) (a b : QInterval) (x y : R)
    (hx : memInterval TF a x) (hy : memInterval TF b y) :
    memInterval TF (add a b) (TF.add x y) := by
  constructor
  · change TF.le (QRat.eval TF (QRat.add a.lo b.lo)) (TF.add x y)
    rw [QRat.eval_add]
    exact TF.add_le_add _ _ _ _ hx.1 hy.1
  · change TF.le (TF.add x y) (QRat.eval TF (QRat.add a.hi b.hi))
    rw [QRat.eval_add]
    exact TF.add_le_add _ _ _ _ hx.2 hy.2

theorem sub_sound {R : Type} (TF : TranscendentalField R) (a b : QInterval) (x y : R)
    (hx : memInterval TF a x) (hy : memInterval TF b y) :
    memInterval TF (sub a b) (TF.sub x y) := by
  constructor
  · change TF.le (QRat.eval TF (QRat.sub a.lo b.hi)) (TF.sub x y)
    rw [QRat.eval_sub]
    exact TF.sub_le_sub _ _ _ _ hx.1 hy.2
  · change TF.le (TF.sub x y) (QRat.eval TF (QRat.sub a.hi b.lo))
    rw [QRat.eval_sub]
    exact TF.sub_le_sub _ _ _ _ hx.2 hy.1

theorem neg_sound {R : Type} (TF : TranscendentalField R) (a : QInterval) (x : R)
    (hx : memInterval TF a x) : memInterval TF (neg a) (TF.neg x) := by
  constructor
  · change TF.le (QRat.eval TF (QRat.neg a.hi)) (TF.neg x)
    rw [QRat.eval_neg]
    exact TF.neg_le_neg _ _ hx.2
  · change TF.le (TF.neg x) (QRat.eval TF (QRat.neg a.lo))
    rw [QRat.eval_neg]
    exact TF.neg_le_neg _ _ hx.1

end QInterval

namespace QRat

def min (a b : QRat) : QRat := if le a b then a else b
def max (a b : QRat) : QRat := if le a b then b else a

def invPos (a : QRat) (h : 0 < a.num) : QRat :=
  ⟨(a.den : Int), a.num.toNat, by omega⟩

theorem eval_invPos {R : Type} (TF : TranscendentalField R) (a : QRat) (h : 0 < a.num) :
    eval TF (invPos a h) = TF.div TF.one (eval TF a) := by
  unfold eval invPos
  rw [TF.one_eq_ofRat]
  have ha : (a.num.toNat : Int) = a.num := Int.toNat_of_nonneg (by omega)
  have hd := TF.ofRat_div_pos 1 1 a.num.toNat a.den (by decide) (by omega) a.den_pos
  simpa only [ha, Int.one_mul, Nat.one_mul] using hd.symm

theorem min_le_left {R : Type} (TF : TranscendentalField R) (a b : QRat) :
    TF.le (eval TF (min a b)) (eval TF a) := by
  unfold min; split
  · exact TF.le_refl _
  · cases TF.le_total (eval TF a) (eval TF b) with
    | inl h => exact False.elim (by rename_i hn; exact hn ((eval_le_iff TF a b).mp h))
    | inr h => exact h

theorem min_le_right {R : Type} (TF : TranscendentalField R) (a b : QRat) :
    TF.le (eval TF (min a b)) (eval TF b) := by
  unfold min; split
  · exact (eval_le_iff TF a b).mpr (by assumption)
  · exact TF.le_refl _

theorem le_max_left {R : Type} (TF : TranscendentalField R) (a b : QRat) :
    TF.le (eval TF a) (eval TF (max a b)) := by
  unfold max; split
  · exact (eval_le_iff TF a b).mpr (by assumption)
  · exact TF.le_refl _

theorem le_max_right {R : Type} (TF : TranscendentalField R) (a b : QRat) :
    TF.le (eval TF b) (eval TF (max a b)) := by
  unfold max; split
  · exact TF.le_refl _
  · cases TF.le_total (eval TF a) (eval TF b) with
    | inl h => exact False.elim (by rename_i hn; exact hn ((eval_le_iff TF a b).mp h))
    | inr h => exact h

end QRat

namespace QInterval

def hull (a b : QInterval) : QInterval := ⟨QRat.min a.lo b.lo, QRat.max a.hi b.hi⟩

theorem hull_left {R : Type} (TF : TranscendentalField R) (a b : QInterval) (x : R)
    (h : memInterval TF a x) : memInterval TF (hull a b) x :=
  ⟨TF.le_trans _ _ _ (QRat.min_le_left TF _ _) h.1,
   TF.le_trans _ _ _ h.2 (QRat.le_max_left TF _ _)⟩

theorem hull_right {R : Type} (TF : TranscendentalField R) (a b : QInterval) (x : R)
    (h : memInterval TF b x) : memInterval TF (hull a b) x :=
  ⟨TF.le_trans _ _ _ (QRat.min_le_right TF _ _) h.1,
   TF.le_trans _ _ _ h.2 (QRat.le_max_right TF _ _)⟩

def scale (c : QRat) (a : QInterval) : QInterval :=
  if QRat.le QRat.zero c then ⟨QRat.mul c a.lo, QRat.mul c a.hi⟩
  else ⟨QRat.mul c a.hi, QRat.mul c a.lo⟩

theorem scale_sound {R : Type} (TF : TranscendentalField R) (c : QRat) (a : QInterval) (x : R)
    (h : memInterval TF a x) : memInterval TF (scale c a) (TF.mul (QRat.eval TF c) x) := by
  unfold scale; split
  · rename_i hc
    have hc' := (QRat.eval_le_iff TF QRat.zero c).mpr hc
    rw [QRat.eval_zero] at hc'
    constructor <;> simp only [QRat.eval_mul]
    · exact TF.mul_le_mul_nonneg_left _ _ _ hc' h.1
    · exact TF.mul_le_mul_nonneg_left _ _ _ hc' h.2
  · rename_i hc
    have hc' : TF.le (QRat.eval TF c) TF.zero := by
      cases TF.le_total (QRat.eval TF c) TF.zero with
      | inl h => exact h
      | inr h =>
        rw [← QRat.eval_zero TF] at h
        exact False.elim (hc ((QRat.eval_le_iff TF _ _).mp h))
    constructor <;> simp only [QRat.eval_mul]
    · exact TF.mul_le_mul_nonpos_left _ _ _ hc' h.2
    · exact TF.mul_le_mul_nonpos_left _ _ _ hc' h.1

def mul (a b : QInterval) : QInterval := hull (scale a.lo b) (scale a.hi b)

theorem mul_sound {R : Type} (TF : TranscendentalField R) (a b : QInterval) (x y : R)
    (hx : memInterval TF a x) (hy : memInterval TF b y) : memInterval TF (mul a b) (TF.mul x y) := by
  have hl := hull_left TF (scale a.lo b) (scale a.hi b) _ (scale_sound TF a.lo b y hy)
  have hh := hull_right TF (scale a.lo b) (scale a.hi b) _ (scale_sound TF a.hi b y hy)
  cases TF.le_total TF.zero y with
  | inl h =>
    have lo := TF.mul_le_mul_nonneg_left y _ _ h hx.1
    have hi := TF.mul_le_mul_nonneg_left y _ _ h hx.2
    rw [TF.mul_comm y x, TF.mul_comm y (QRat.eval TF a.lo)] at lo
    rw [TF.mul_comm y x, TF.mul_comm y (QRat.eval TF a.hi)] at hi
    exact ⟨TF.le_trans _ _ _ hl.1 lo, TF.le_trans _ _ _ hi hh.2⟩
  | inr h =>
    have lo := TF.mul_le_mul_nonpos_left y _ _ h hx.2
    have hi := TF.mul_le_mul_nonpos_left y _ _ h hx.1
    rw [TF.mul_comm y x, TF.mul_comm y (QRat.eval TF a.hi)] at lo
    rw [TF.mul_comm y x, TF.mul_comm y (QRat.eval TF a.lo)] at hi
    exact ⟨TF.le_trans _ _ _ hh.1 lo, TF.le_trans _ _ _ hi hl.2⟩

def invPos (a : QInterval) : Option QInterval :=
  if hl : 0 < a.lo.num then
    if hh : 0 < a.hi.num then some ⟨QRat.invPos a.hi hh, QRat.invPos a.lo hl⟩ else none
  else none

private theorem qpos {R : Type} (TF : TranscendentalField R) (q : QRat) (h : 0 < q.num) :
    TF.lt TF.zero (QRat.eval TF q) := by
  rw [← QRat.eval_zero TF, QRat.eval_lt_iff]
  change (0 : Int) * (q.den : Int) < q.num * 1
  simpa only [Int.zero_mul, Int.mul_one] using h

private theorem one_nonneg {R : Type} (TF : TranscendentalField R) : TF.le TF.zero TF.one := by
  rw [TF.zero_eq_ofRat, TF.one_eq_ofRat]
  exact (TF.ofRat_le_iff 0 1 1 1 (by decide) (by decide)).mpr (by decide)

private theorem pos_of_pos_le {R : Type} (TF : TranscendentalField R) (a b : R)
    (ha : TF.lt TF.zero a) (hab : TF.le a b) : TF.lt TF.zero b := by
  obtain ⟨h, hn⟩ := (TF.lt_iff_le_not_le _ _).mp ha
  exact (TF.lt_iff_le_not_le _ _).mpr ⟨TF.le_trans _ _ _ h hab, fun hb => hn (TF.le_trans _ _ _ hab hb)⟩

theorem invPos_sound {R : Type} (TF : TranscendentalField R) (a r : QInterval) (x : R)
    (he : invPos a = some r) (hx : memInterval TF a x) :
    memInterval TF r (TF.div TF.one x) := by
  unfold invPos at he
  split at he <;> try contradiction
  split at he <;> try contradiction
  rename_i hl hh
  cases he
  have hp := pos_of_pos_le TF _ x (qpos TF a.lo hl) hx.1
  constructor <;> simp only [QRat.eval_invPos]
  · exact TF.div_ge_of_num_ge_den_le _ _ _ _ (one_nonneg TF) (TF.le_refl _) hp hx.2
  · exact TF.div_ge_of_num_ge_den_le _ _ _ _ (one_nonneg TF) (TF.le_refl _) (qpos TF a.lo hl) hx.1

/-- Division enclosure uses numerator sign and positive denominator monotonicity. -/
def divPos (a b : QInterval) : Option QInterval := do
  let inv ← invPos b
  return mul a inv

theorem divPos_sound {R : Type} (TF : TranscendentalField R) (a b r : QInterval) (x y : R)
    (he : divPos a b = some r) (hx : memInterval TF a x) (hy : memInterval TF b y) :
    memInterval TF r (TF.div x y) := by
  cases hi : invPos b with
  | none => simp [divPos, hi] at he
  | some iv =>
    have hb : 0 < b.lo.num := by
      unfold invPos at hi
      split at hi
      · assumption
      · contradiction
    have hp := pos_of_pos_le TF _ y (qpos TF b.lo hb) hy.1
    simp [divPos, hi] at he
    subst r
    rw [TF.div_eq_mul_inv_pos x y hp]
    exact mul_sound TF a iv x _ hx (invPos_sound TF b iv y hi hy)

-- `exp(-x)` gives an upper bound by reciprocating a positive lower bound.
def exp (a : QInterval) (m : Nat := 8) : Option QInterval :=
  let baseLo := QRat.add QRat.one (QRat.halfPow m a.lo)
  let baseHi := QRat.add QRat.one (QRat.halfPow m (QRat.neg a.hi))
  if QRat.le QRat.zero baseLo then
    if QRat.le QRat.zero baseHi then
      let upperDen := QRat.iterSq m baseHi
      if h : 0 < upperDen.num then
        some ⟨QRat.iterSq m baseLo, QRat.invPos upperDen h⟩
      else none
    else none
  else none

theorem exp_sound {R : Type} (TF : TranscendentalField R) (a r : QInterval) (x : R) (m : Nat)
    (he : exp a m = some r) (hx : memInterval TF a x) : memInterval TF r (TF.exp x) := by
  unfold exp at he
  dsimp only at he
  split at he <;> try contradiction
  split at he <;> try contradiction
  split at he <;> try contradiction
  rename_i hlo hhi hp
  cases he
  constructor
  · exact exp_ge_qrat_iterSq TF m a.lo x hlo hx.1
  · have hn : TF.le (QRat.eval TF (QRat.neg a.hi)) (TF.neg x) := by
      rw [QRat.eval_neg]; exact TF.neg_le_neg _ _ hx.2
    have hd := exp_ge_qrat_iterSq TF m (QRat.neg a.hi) (TF.neg x) hhi hn
    have h := TF.div_ge_of_num_ge_den_le _ _ _ _ (one_nonneg TF) (TF.le_refl TF.one)
      (qpos TF _ hp) hd
    rw [← TF.exp_neg, TF.neg_neg, ← QRat.eval_invPos TF _ hp] at h
    exact h

end QInterval

/-- Pointwise box membership of an assignment `env : Nat → R` inside `box : List QInterval`. -/
def memBox {R : Type} (TF : TranscendentalField R) : List QInterval → (Nat → R) → Prop
  | [], _ => True
  | iv :: rest, env => memInterval TF iv (env 0) ∧ memBox TF rest (fun k => env (k + 1))

/-- Split variable `idx` of `box` at rational midpoint `mid` into `(leftBox, rightBox)`. -/
def splitBox : List QInterval → Nat → QRat → Option (List QInterval × List QInterval)
  | [], _, _ => none
  | iv :: rest, 0, mid =>
    some ({ lo := iv.lo, hi := mid } :: rest, { lo := mid, hi := iv.hi } :: rest)
  | iv :: rest, k + 1, mid =>
    match splitBox rest k mid with
    | none => none
    | some (l, r) => some (iv :: l, iv :: r)

/-- Exhaustiveness of box bisection: every point in `box` lies in `leftBox` or `rightBox`. -/
theorem splitBox_exhaustive {R : Type} (TF : TranscendentalField R) :
    ∀ (box l r : List QInterval) (idx : Nat) (mid : QRat) (env : Nat → R),
      splitBox box idx mid = some (l, r) →
      memBox TF box env →
      memBox TF l env ∨ memBox TF r env
  | [], _, _, _, _, _, h, _ => nomatch h
  | iv :: rest, l, r, 0, mid, env, h, ⟨⟨hlo, hhi⟩, hrest⟩ => by
    injection h with hpair
    injection hpair with hl hr
    subst hl; subst hr
    cases TF.le_total (env 0) (QRat.eval TF mid) with
    | inl hle => exact Or.inl ⟨⟨hlo, hle⟩, hrest⟩
    | inr hge => exact Or.inr ⟨⟨hge, hhi⟩, hrest⟩
  | iv :: rest, l, r, k + 1, mid, env, h, ⟨hiv, hrest⟩ => by
    unfold splitBox at h
    split at h
    · nomatch h
    · rename_i l' r' hrec
      injection h with hpair
      injection hpair with hl hr
      subst hl; subst hr
      cases splitBox_exhaustive TF rest l' r' k mid (fun j => env (j + 1)) hrec hrest with
      | inl hl' => exact Or.inl ⟨hiv, hl'⟩
      | inr hr' => exact Or.inr ⟨hiv, hr'⟩

/-- N-dimensional branch-and-bound `UNSAT` paving certificate tree. -/
inductive PavingTree where
  | leaf : Nat → PavingTree
  | split : Nat → QRat → PavingTree → PavingTree → PavingTree
  deriving Repr

/-- Verify a `PavingTree` given a sound leaf refuter `checkLeaf reason box = true`. -/
def verifyPaving (checkLeaf : Nat → List QInterval → Bool) :
    PavingTree → List QInterval → Bool
  | .leaf reason, box => checkLeaf reason box
  | .split idx mid left right, box =>
    match splitBox box idx mid with
    | none => false
    | some (lBox, rBox) => verifyPaving checkLeaf left lBox && verifyPaving checkLeaf right rBox

/-- Path-A Paving Soundness Theorem:
    If every leaf certificate validated by `checkLeaf` is locally inconsistent on its sub-box
    (`memBox TF subBox env → ¬ Active env`), and `verifyPaving checkLeaf tree rootBox = true`,
    then `Active env` is globally unsatisfiable (`UNSAT`) across the entire continuous `rootBox`! -/
theorem paving_unsat_sound {R : Type} (TF : TranscendentalField R)
    (Active : (Nat → R) → Prop)
    (checkLeaf : Nat → List QInterval → Bool)
    (hleaf_sound : ∀ reason box env,
      checkLeaf reason box = true → memBox TF box env → ¬ Active env) :
    ∀ (tree : PavingTree) (box : List QInterval) (env : Nat → R),
      verifyPaving checkLeaf tree box = true →
      memBox TF box env →
      ¬ Active env
  | .leaf reason, box, env, hver, hmem =>
    hleaf_sound reason box env hver hmem
  | .split idx mid left right, box, env, hver, hmem => by
    unfold verifyPaving at hver
    split at hver
    · contradiction
    · rename_i lBox rBox hsp
      have hand : verifyPaving checkLeaf left lBox = true ∧
                  verifyPaving checkLeaf right rBox = true := by
        cases h1 : verifyPaving checkLeaf left lBox <;>
        cases h2 : verifyPaving checkLeaf right rBox <;>
        simp_all
      cases splitBox_exhaustive TF box lBox rBox idx mid env hsp hmem with
      | inl hl => exact paving_unsat_sound TF Active checkLeaf hleaf_sound left lBox env hand.1 hl
      | inr hr => exact paving_unsat_sound TF Active checkLeaf hleaf_sound right rBox env hand.2 hr

/-- A softplus enclosure that remains finite at large positive gate drive.
It follows from max(0,x) ≤ log(1+exp x) ≤ max(0,x)+1. -/
def QInterval.softplus (a : QInterval) : QInterval :=
  ⟨QRat.max QRat.zero a.lo, QRat.add (QRat.max QRat.zero a.hi) QRat.one⟩

theorem QInterval.softplus_sound {R : Type} (TF : TranscendentalField R)
    (a : QInterval) (x : R) (hx : memInterval TF a x) :
    memInterval TF a.softplus (TF.ln1pExp x) := by
  have reflect {u v : R} (h : TF.le (TF.exp u) (TF.exp v)) : TF.le u v := by
    rcases TF.le_total u v with hu | hv
    · exact hu
    · exact TF.exp_injective u v (TF.le_antisymm _ _ h (TF.exp_mono _ _ hv)) ▸ TF.le_refl v
  have hxsp : TF.le x (TF.ln1pExp x) := by
    apply reflect
    rw [TF.ln1pExp_spec]
    simpa only [TF.zero_add] using TF.add_le_add _ _ _ _ (one_nonneg TF) (TF.le_refl (TF.exp x))
  constructor
  · change TF.le (QRat.eval TF (QRat.max QRat.zero a.lo)) _
    unfold QRat.max
    split
    · exact TF.le_trans _ _ _ hx.1 hxsp
    · rw [QRat.eval_zero]; exact (PhysicsModels.ekv_softplus_witness_nonneg TF x).2
  · let u := QRat.eval TF (QRat.max QRat.zero a.hi)
    have hzero : TF.le TF.zero u := by
      simpa only [QRat.eval_zero] using QRat.le_max_left TF QRat.zero a.hi
    have hu := TF.le_trans _ _ u hx.2 (QRat.le_max_right TF _ _)
    have hu1 : TF.le TF.one (TF.exp u) := by simpa only [TF.exp_zero] using TF.exp_mono _ _ hzero
    change TF.le _ (QRat.eval TF (QRat.add _ QRat.one))
    rw [QRat.eval_add, QRat.eval_one]
    apply reflect
    rw [TF.ln1pExp_spec, TF.exp_add]
    have h := TF.mul_le_mul_nonneg_left (TF.exp u) _ _
      (((TF.lt_iff_le_not_le _ _).mp (TF.exp_pos u)).1) (TF.one_add_le_exp TF.one)
    rw [TF.mul_add, TF.mul_one] at h
    exact TF.le_trans _ _ _ (TF.add_le_add _ _ _ _ hu1 (TF.exp_mono x u hu)) h

/-- Arithmetic syntax shared by concrete certificates and their semantics. -/
inductive PExpr where
  | const : QRat → PExpr
  | var : Nat → PExpr
  | neg : PExpr → PExpr
  | add : PExpr → PExpr → PExpr
  | sub : PExpr → PExpr → PExpr
  | mul : PExpr → PExpr → PExpr
  | div : PExpr → PExpr → PExpr
  | softplus : PExpr → PExpr
  | exp : PExpr → PExpr
  deriving Repr

def PExpr.eval {R : Type} (TF : TranscendentalField R) (env : Nat → R) : PExpr → R
  | .const q => QRat.eval TF q
  | .var i => env i
  | .neg a => TF.neg (a.eval TF env)
  | .add a b => TF.add (a.eval TF env) (b.eval TF env)
  | .sub a b => TF.sub (a.eval TF env) (b.eval TF env)
  | .mul a b => TF.mul (a.eval TF env) (b.eval TF env)
  | .div a b => TF.div (a.eval TF env) (b.eval TF env)
  | .softplus a => TF.ln1pExp (a.eval TF env)
  | .exp a => TF.exp (a.eval TF env)

def evalPExpr (box : List QInterval) : PExpr → Option QInterval
  | .const q => some ⟨q, q⟩
  | .var i => box[i]?
  | .neg a => QInterval.neg <$> evalPExpr box a
  | .add a b => do return QInterval.add (← evalPExpr box a) (← evalPExpr box b)
  | .sub a b => do return QInterval.sub (← evalPExpr box a) (← evalPExpr box b)
  | .mul a b => do return QInterval.mul (← evalPExpr box a) (← evalPExpr box b)
  | .div a b => do QInterval.divPos (← evalPExpr box a) (← evalPExpr box b)
  | .softplus a => QInterval.softplus <$> evalPExpr box a
  | .exp a => do QInterval.exp (← evalPExpr box a)

theorem memBox_lookup {R : Type} (TF : TranscendentalField R) :
    ∀ (box : List QInterval) (env : Nat → R) (i : Nat) (iv : QInterval),
      memBox TF box env → box[i]? = some iv → memInterval TF iv (env i)
  | [], _, _, _, _, h => by simp at h
  | a :: rest, env, 0, iv, h, hi => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst iv; exact h.1
  | a :: rest, env, i+1, iv, h, hi =>
    memBox_lookup TF rest (fun j => env (j+1)) i iv h.2 hi

theorem evalPExpr_sound {R : Type} (TF : TranscendentalField R) (box : List QInterval)
    (env : Nat → R) (hm : memBox TF box env) (e : PExpr) (iv : QInterval)
    (he : evalPExpr box e = some iv) : memInterval TF iv (e.eval TF env) := by
  induction e generalizing iv with
  | const q => cases he; exact ⟨TF.le_refl _, TF.le_refl _⟩
  | var i => exact memBox_lookup TF box env i iv hm he
  | neg a ih =>
    cases ha : evalPExpr box a with
    | none => simp [evalPExpr, ha] at he
    | some v =>
      simp [evalPExpr, ha] at he
      subst iv; exact QInterval.neg_sound TF v _ (ih v ha)
  | softplus a ih =>
    cases ha : evalPExpr box a with
    | none => simp [evalPExpr, ha] at he
    | some v =>
      simp [evalPExpr, ha] at he
      subst iv; exact QInterval.softplus_sound TF v _ (ih v ha)
  | exp a ih =>
    cases ha : evalPExpr box a with
    | none => simp [evalPExpr, ha] at he
    | some v =>
      simp [evalPExpr, ha] at he
      exact QInterval.exp_sound TF v iv _ 8 he (ih v ha)
  | add a b ia ib | sub a b ia ib | mul a b ia ib | div a b ia ib =>
    cases ha : evalPExpr box a with
    | none => simp [evalPExpr, ha] at he
    | some va =>
      cases hb : evalPExpr box b with
      | none => simp [evalPExpr, ha, hb] at he
      | some vb =>
        simp only [evalPExpr, ha, hb, Option.pure_def] at he
        first
        | exact QInterval.divPos_sound TF va vb iv _ _ he (ia va ha) (ib vb hb)
        | cases he
          first
          | exact QInterval.add_sound TF va vb _ _ (ia va ha) (ib vb hb)
          | exact QInterval.sub_sound TF va vb _ _ (ia va ha) (ib vb hb)
          | exact QInterval.mul_sound TF va vb _ _ (ia va ha) (ib vb hb)

inductive PCmp where
  | eqZero | gtZero | geZero
  deriving Repr, DecidableEq

def PCmp.holds {R : Type} (TF : TranscendentalField R) (op : PCmp) (x : R) : Prop :=
  match op with
  | .eqZero => x = TF.zero
  | .gtZero => TF.lt TF.zero x
  | .geZero => TF.le TF.zero x

def refuteConstraint (op : PCmp) (iv : QInterval) : Bool :=
  match op with
  | .eqZero => decide (QRat.lt iv.hi QRat.zero) || decide (QRat.lt QRat.zero iv.lo)
  | .gtZero => decide (QRat.le iv.hi QRat.zero)
  | .geZero => decide (QRat.lt iv.hi QRat.zero)

theorem refuteConstraint_sound {R : Type} (TF : TranscendentalField R) (op : PCmp)
    (iv : QInterval) (x : R) (hm : memInterval TF iv x)
    (h : refuteConstraint op iv = true) : ¬ op.holds TF x := by
  have lt0 (h : QRat.lt iv.hi QRat.zero) : ¬ TF.le TF.zero x := by
    have hh := (QRat.eval_lt_iff TF iv.hi QRat.zero).mpr h
    rw [QRat.eval_zero] at hh
    exact fun hx => ((TF.lt_iff_le_not_le _ _).mp hh).2 (TF.le_trans _ _ _ hx hm.2)
  have gt0 (h : QRat.lt QRat.zero iv.lo) : ¬ TF.le x TF.zero := by
    have hh := (QRat.eval_lt_iff TF QRat.zero iv.lo).mpr h
    rw [QRat.eval_zero] at hh
    exact fun hx => ((TF.lt_iff_le_not_le _ _).mp hh).2 (TF.le_trans _ _ _ hm.1 hx)
  cases op with
  | eqZero =>
    simp only [refuteConstraint, Bool.or_eq_true, decide_eq_true_eq] at h
    intro hx; change x = TF.zero at hx
    cases h with
    | inl h => exact lt0 h (hx ▸ TF.le_refl _)
    | inr h => exact gt0 h (hx ▸ TF.le_refl _)
  | geZero => exact lt0 (of_decide_eq_true h)
  | gtZero =>
    have hh := (QRat.eval_le_iff TF iv.hi QRat.zero).mpr (of_decide_eq_true h)
    rw [QRat.eval_zero] at hh
    intro hx
    exact ((TF.lt_iff_le_not_le _ _).mp hx).2 (TF.le_trans _ _ _ hm.2 hh)

abbrev PConstraint := PCmp × PExpr

def holdsConstraints {R : Type} (TF : TranscendentalField R) (cs : List PConstraint)
    (env : Nat → R) : Prop := ∀ c ∈ cs, c.1.holds TF (c.2.eval TF env)

def checkConcreteLeaf (cs : List PConstraint) (reason : Nat) (box : List QInterval) : Bool :=
  match cs[reason]? with
  | none => false
  | some (op, e) => match evalPExpr box e with
    | none => false
    | some iv => refuteConstraint op iv

theorem checkConcreteLeaf_sound {R : Type} (TF : TranscendentalField R) (cs : List PConstraint)
    (reason : Nat) (box : List QInterval) (env : Nat → R)
    (hc : checkConcreteLeaf cs reason box = true) (hm : memBox TF box env) :
    ¬ holdsConstraints TF cs env := by
  unfold checkConcreteLeaf at hc
  cases hg : cs[reason]? with
  | none => simp [hg] at hc
  | some c =>
    rcases c with ⟨op, e⟩
    cases he : evalPExpr box e with
    | none => simp [hg, he] at hc
    | some iv =>
      simp only [hg, he] at hc
      intro hs
      have hmem : (op, e) ∈ cs := List.mem_of_getElem? hg
      exact refuteConstraint_sound TF op iv _ (evalPExpr_sound TF box env hm e iv he) hc (hs _ hmem)

end SpiceSmtBench.IntervalCheck

namespace SpiceSmtBench
namespace TranscendentalField

theorem mul_right_cancel_pos {R : Type} (TF : TranscendentalField R) (a b c : R)
    (hc : TF.lt TF.zero c) (h : TF.mul a c = TF.mul b c) : a = b := by
  have hi : TF.mul c (TF.div TF.one c) = TF.one := by
    rw [TF.mul_comm]; exact TF.mul_div_cancel_pos TF.one c hc
  have hh := congrArg (fun z => TF.mul z (TF.div TF.one c)) h
  simpa only [TF.mul_assoc, hi, TF.mul_one] using hh

theorem square_le_reflect {R : Type} (TF : TranscendentalField R) (a b : R)
    (ha : TF.le TF.zero a) (hb : TF.le TF.zero b)
    (h : TF.le (TF.mul a a) (TF.mul b b)) : TF.le a b := by
  cases TF.le_total a b with
  | inl h => exact h
  | inr hba =>
    have he := TF.le_antisymm _ _ h (TF.sq_mono_nonneg b a hb hba)
    by_cases hb0 : TF.le b TF.zero
    · have eb : b = TF.zero := TF.le_antisymm _ _ hb0 hb
      rw [eb, TF.mul_zero] at he
      by_cases ha0 : TF.le a TF.zero
      · exact eb ▸ ha0
      · have hap := (TF.lt_iff_le_not_le _ _).mpr ⟨ha, ha0⟩
        have hz : TF.mul TF.zero a = TF.zero := by rw [TF.mul_comm, TF.mul_zero]
        have ea := TF.mul_right_cancel_pos a TF.zero a hap (he.trans hz.symm)
        exact ea ▸ hb
    · have hbp := (TF.lt_iff_le_not_le _ _).mpr ⟨hb, hb0⟩
      have hap := (TF.lt_iff_le_not_le _ _).mpr ⟨ha, fun hn => hb0 (TF.le_trans _ _ _ hba hn)⟩
      have eq := TF.positive_sqrt_unique a b hap hbp he
      exact eq ▸ TF.le_refl b

end TranscendentalField

namespace IntervalCheck

/-- Checked forward definitions bound initially unbounded algebraic auxiliaries. -/
inductive DefKind where
  | direct | logarithm | squareRoot
  deriving Repr

structure PDefinition where
  kind : DefKind
  rhs : PExpr
  deriving Repr

def PDefinition.holds {R : Type} (TF : TranscendentalField R) (env : Nat → R)
    (n : Nat) (d : PDefinition) : Prop :=
  match d.kind with
  | .direct => env n = d.rhs.eval TF env
  | .logarithm => TF.exp (env n) = d.rhs.eval TF env
  | .squareRoot => TF.le TF.zero (env n) ∧ TF.mul (env n) (env n) = d.rhs.eval TF env

def encloses (outer inner : QInterval) : Bool :=
  decide (QRat.le outer.lo inner.lo) && decide (QRat.le inner.hi outer.hi)

theorem encloses_sound {R : Type} (TF : TranscendentalField R) (a b : QInterval) (x : R)
    (h : encloses a b = true) (hm : memInterval TF b x) : memInterval TF a x := by
  simp only [encloses, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨TF.le_trans _ _ _ ((QRat.eval_le_iff TF _ _).mpr h.1) hm.1,
    TF.le_trans _ _ _ hm.2 ((QRat.eval_le_iff TF _ _).mpr h.2)⟩

def checkDefinition (box : List QInterval) (d : PDefinition) (iv : QInterval) : Bool :=
  match evalPExpr box d.rhs with
  | none => false
  | some rhs => match d.kind with
    | .direct => encloses iv rhs
    | .logarithm => match QInterval.exp ⟨iv.lo, iv.lo⟩, QInterval.exp ⟨iv.hi, iv.hi⟩ with
      | some lo, some hi => decide (QRat.le lo.hi rhs.lo) && decide (QRat.le rhs.hi hi.lo)
      | _, _ => false
    | .squareRoot => decide (QRat.le QRat.zero iv.lo) && decide (QRat.le QRat.zero iv.hi) &&
        decide (QRat.le (QRat.mul iv.lo iv.lo) rhs.lo) && decide (QRat.le rhs.hi (QRat.mul iv.hi iv.hi))

theorem checkDefinition_sound {R : Type} (TF : TranscendentalField R) (box : List QInterval)
    (d : PDefinition) (iv : QInterval) (env : Nat → R)
    (hm : memBox TF box env) (hd : d.holds TF env box.length)
    (hc : checkDefinition box d iv = true) : memInterval TF iv (env box.length) := by
  unfold checkDefinition at hc
  cases he : evalPExpr box d.rhs with
  | none => simp [he] at hc
  | some rhs =>
    have hr := evalPExpr_sound TF box env hm d.rhs rhs he
    simp only [he] at hc
    cases hk : d.kind with
    | direct =>
      simp only [hk] at hc
      simp only [PDefinition.holds, hk] at hd
      rw [hd]; exact encloses_sound TF iv rhs _ hc hr
    | logarithm =>
      simp only [hk] at hc
      simp only [PDefinition.holds, hk] at hd
      cases hl : QInterval.exp ⟨iv.lo, iv.lo⟩ with
      | none => simp [hl] at hc
      | some lo =>
        cases hh : QInterval.exp ⟨iv.hi, iv.hi⟩ with
        | none => simp [hl, hh] at hc
        | some hi =>
          simp only [hl, hh, Bool.and_eq_true, decide_eq_true_eq] at hc
          have hlo := QInterval.exp_sound TF ⟨iv.lo,iv.lo⟩ lo (QRat.eval TF iv.lo) 8 hl ⟨TF.le_refl _,TF.le_refl _⟩
          have hhi := QInterval.exp_sound TF ⟨iv.hi,iv.hi⟩ hi (QRat.eval TF iv.hi) 8 hh ⟨TF.le_refl _,TF.le_refl _⟩
          have reflect : ∀ a b, TF.le (TF.exp a) (TF.exp b) → TF.le a b := by
            intro a b h
            cases TF.le_total a b with
            | inl h => exact h
            | inr hba =>
              have eq := TF.exp_injective a b (TF.le_antisymm _ _ h (TF.exp_mono _ _ hba))
              exact eq ▸ TF.le_refl b
          constructor
          · apply reflect; rw [hd]
            exact TF.le_trans _ _ _ hlo.2 (TF.le_trans _ _ _ ((QRat.eval_le_iff TF _ _).mpr hc.1) hr.1)
          · apply reflect; rw [hd]
            exact TF.le_trans _ _ _ hr.2 (TF.le_trans _ _ _ ((QRat.eval_le_iff TF _ _).mpr hc.2) hhi.1)
    | squareRoot =>
      simp only [hk, Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [PDefinition.holds, hk] at hd
      have lo := (QRat.eval_le_iff TF _ _).mpr hc.1.1.1
      have hi := (QRat.eval_le_iff TF _ _).mpr hc.1.1.2
      rw [QRat.eval_zero] at lo hi
      constructor
      · apply TF.square_le_reflect _ _ lo hd.1
        rw [hd.2, ← QRat.eval_mul]
        exact TF.le_trans _ _ _ ((QRat.eval_le_iff TF _ _).mpr hc.1.2) hr.1
      · apply TF.square_le_reflect _ _ hd.1 hi
        rw [hd.2, ← QRat.eval_mul]
        exact TF.le_trans _ _ _ hr.2 ((QRat.eval_le_iff TF _ _).mpr hc.2)

theorem memBox_append_one {R : Type} (TF : TranscendentalField R) :
    ∀ (box : List QInterval) (iv : QInterval) (env : Nat → R),
      memBox TF box env → memInterval TF iv (env box.length) → memBox TF (box ++ [iv]) env
  | [], _iv, _env, _, hi => ⟨hi, trivial⟩
  | _a::rest, iv, env, hm, hi =>
    ⟨hm.1, memBox_append_one TF rest iv (fun k => env (k+1)) hm.2 hi⟩

def holdsDefinitions {R : Type} (TF : TranscendentalField R) (env : Nat → R) : Nat → List PDefinition → Prop
  | _, [] => True
  | n, d::ds => d.holds TF env n ∧ holdsDefinitions TF env (n+1) ds

def forwardBox : List QInterval → List PDefinition → List QInterval → Option (List QInterval)
  | box, [], [] => some box
  | box, d::ds, iv::ivs => if checkDefinition box d iv then forwardBox (box ++ [iv]) ds ivs else none
  | _, _, _ => none

theorem forwardBox_sound {R : Type} (TF : TranscendentalField R) (env : Nat → R) :
    ∀ (box : List QInterval) (ds : List PDefinition) (ivs result : List QInterval),
      memBox TF box env → holdsDefinitions TF env box.length ds →
      forwardBox box ds ivs = some result → memBox TF result env
  | box, [], [], result, hm, _, he => by cases he; exact hm
  | _, [], _::_, _, _, _, he => by contradiction
  | _, _::_, [], _, _, _, he => by contradiction
  | box, d::ds, iv::ivs, result, hm, hd, he => by
    unfold forwardBox at he
    split at he
    · rename_i hc
      have hm' := memBox_append_one TF box iv env hm (checkDefinition_sound TF box d iv env hm hd.1 hc)
      apply forwardBox_sound TF env (box ++ [iv]) ds ivs result hm' _ he
      simpa only [List.length_append, List.length_singleton] using hd.2
    · contradiction

def checkRanges (box : List QInterval) : List (Nat × QInterval) → Bool
  | [] => true
  | (i, iv)::rest => (match box[i]? with | none => false | some got => encloses iv got) && checkRanges box rest

def holdsRanges {R : Type} (TF : TranscendentalField R) (env : Nat → R) : List (Nat × QInterval) → Prop
  | [] => True
  | (i, iv)::rest => memInterval TF iv (env i) ∧ holdsRanges TF env rest

theorem checkRanges_sound {R : Type} (TF : TranscendentalField R) (env : Nat → R)
    (box : List QInterval) (hm : memBox TF box env) :
    ∀ ranges, checkRanges box ranges = true → holdsRanges TF env ranges
  | [], _ => trivial
  | (i, iv)::rest, h => by
    simp only [checkRanges, Bool.and_eq_true] at h
    cases hg : box[i]? with
    | none => simp [hg] at h
    | some got =>
      simp only [hg] at h
      exact ⟨encloses_sound TF iv got _ h.1 (memBox_lookup TF box env i got hm hg), checkRanges_sound TF env box hm rest h.2⟩

def checkForwardLeaf (n : Nat) (ds : List PDefinition) (ranges : List (Nat × QInterval))
    (certs : List (List QInterval)) (reason : Nat) (box : List QInterval) : Bool :=
  decide (box.length = n) && match certs[reason]? with
    | none => false
    | some ivs => match forwardBox box ds ivs with
      | none => false
      | some result => checkRanges result ranges

theorem checkForwardLeaf_sound {R : Type} (TF : TranscendentalField R) (n : Nat)
    (ds : List PDefinition) (ranges : List (Nat × QInterval)) (certs : List (List QInterval))
    (reason : Nat) (box : List QInterval) (env : Nat → R)
    (hc : checkForwardLeaf n ds ranges certs reason box = true) (hm : memBox TF box env) :
    ¬ (holdsDefinitions TF env n ds ∧ ¬ holdsRanges TF env ranges) := by
  simp only [checkForwardLeaf, Bool.and_eq_true, decide_eq_true_eq] at hc
  intro ⟨hd, hn⟩
  cases hg : certs[reason]? with
  | none => simp [hg] at hc
  | some ivs =>
    cases hf : forwardBox box ds ivs with
    | none => simp [hg, hf] at hc
    | some result =>
      simp only [hg, hf] at hc
      rw [← hc.1] at hd
      exact hn (checkRanges_sound TF env result (forwardBox_sound TF env box ds ivs result hm hd hf) ranges hc.2)

end IntervalCheck

end SpiceSmtBench
