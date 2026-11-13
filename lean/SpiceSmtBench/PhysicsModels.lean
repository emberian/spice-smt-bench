import Init.Data.Rat.Lemmas

/-!
# Transcendental Circuit, Multi-PDK Transistor, PCB EM & TCAD Physics Models

Defines the self-contained algebraic/analytic carrier structure `TranscendentalField R`
used across all 19 target specifications. Results are conditional on this
interface; this library does not construct a concrete real-exponential instance.
-/

namespace SpiceSmtBench

/-- A minimal algebraic ordered-field interface, independent of transcendental
operations. Its rational model below witnesses consistency of these laws. -/
structure AlgebraicOrderedField (R : Type) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  neg : R → R
  inv : R → R
  le : R → R → Prop
  zero_ne_one : zero ≠ one
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  add_zero : ∀ a, add a zero = a
  add_neg : ∀ a, add a (neg a) = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  mul_one : ∀ a, mul a one = a
  mul_add : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  mul_inv : ∀ a, a ≠ zero → mul a (inv a) = one
  le_refl : ∀ a, le a a
  le_total : ∀ a b, le a b ∨ le b a
  le_trans : ∀ a b c, le a b → le b c → le a c
  le_antisymm : ∀ a b, le a b → le b a → a = b
  add_le : ∀ a b c, le a b → le (add c a) (add c b)
  mul_nonneg : ∀ a b, le zero a → le zero b → le zero (mul a b)

namespace AlgebraicOrderedField

/-- Canonical reduced rationals; interval endpoints may separately retain an
unreduced numerator and denominator for efficient certificate calculations. -/
abbrev QRat := Rat

def qrat : AlgebraicOrderedField QRat where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := Neg.neg
  inv := Inv.inv
  le := (· ≤ ·)
  zero_ne_one := by decide
  add_assoc := Rat.add_assoc
  add_comm := Rat.add_comm
  add_zero := Rat.add_zero
  add_neg := Rat.add_neg_cancel
  mul_assoc := Rat.mul_assoc
  mul_comm := Rat.mul_comm
  mul_one := Rat.mul_one
  mul_add := Rat.mul_add
  mul_inv := Rat.mul_inv_cancel
  le_refl := fun _ => Rat.le_refl
  le_total := fun _ _ => Rat.le_total
  le_trans := fun _ _ _ => Rat.le_trans
  le_antisymm := fun _ _ => Rat.le_antisymm
  add_le := fun _ _ _ h => Rat.add_le_add_left.mpr h
  mul_nonneg := fun a b ha hb => by
    simpa using (Rat.mul_le_mul_of_nonneg_left hb ha)

/-- Kernel computation exercises normalized arithmetic and order. -/
theorem qrat_computation : (1/2 + 1/3 : QRat) = 5/6 ∧ (0 : QRat) < 5/6 := by decide +kernel

end AlgebraicOrderedField

/-- Ordered real field equipped with exponential `exp` and EKV softplus `ln1pExp`,
    parameterizing all `spice2smt` target specifications without external library bloat. -/
structure TranscendentalField (R : Type) where
  zero    : R
  one     : R
  add     : R → R → R
  sub     : R → R → R
  mul     : R → R → R
  div     : R → R → R
  neg     : R → R
  exp     : R → R
  ln1pExp : R → R
  sqrt : R → R
  ofInt   : Int → R
  ofRat   : Int → Nat → R
  le      : R → R → Prop
  lt      : R → R → Prop

  sqrt_nonneg : ∀ x, le zero (sqrt x)
  sqrt_sq : ∀ x, le zero x → mul (sqrt x) (sqrt x) = x

  -- Rational embedding & exact ring identities
  zero_eq_ofRat      : zero = ofRat 0 1
  one_eq_ofRat       : one = ofRat 1 1
  ofInt_eq_ofRat     : ∀ n : Int, ofInt n = ofRat n 1
  ofRat_eq_iff       : ∀ (a b : Int) (da db : Nat), 0 < da → 0 < db →
                         (ofRat a da = ofRat b db ↔ a * (db : Int) = b * (da : Int))
  ofRat_le_iff       : ∀ (a b : Int) (da db : Nat), 0 < da → 0 < db →
                         (le (ofRat a da) (ofRat b db) ↔ a * (db : Int) ≤ b * (da : Int))
  ofRat_lt_iff       : ∀ (a b : Int) (da db : Nat), 0 < da → 0 < db →
                         (lt (ofRat a da) (ofRat b db) ↔ a * (db : Int) < b * (da : Int))
  ofRat_add          : ∀ (a b : Int) (da db : Nat), 0 < da → 0 < db →
                         add (ofRat a da) (ofRat b db) = ofRat (a * (db : Int) + b * (da : Int)) (da * db)
  ofRat_sub          : ∀ (a b : Int) (da db : Nat), 0 < da → 0 < db →
                         sub (ofRat a da) (ofRat b db) = ofRat (a * (db : Int) - b * (da : Int)) (da * db)
  ofRat_neg          : ∀ (a : Int) (da : Nat), 0 < da → neg (ofRat a da) = ofRat (-a) da
  ofRat_mul          : ∀ (a b : Int) (da db : Nat), 0 < da → 0 < db →
                         mul (ofRat a da) (ofRat b db) = ofRat (a * b) (da * db)
  ofRat_div_pos      : ∀ (a : Int) (da : Nat) (b : Nat) (db : Nat), 0 < da → 0 < b → 0 < db →
                         div (ofRat a da) (ofRat (b : Int) db) = ofRat (a * (db : Int)) (da * b)

  -- Commutative ring & division laws
  add_comm           : ∀ x y, add x y = add y x
  add_assoc          : ∀ x y z, add (add x y) z = add x (add y z)
  zero_add           : ∀ x, add zero x = x
  add_zero           : ∀ x, add x zero = x
  add_neg_self       : ∀ x, add x (neg x) = zero
  sub_eq_add_neg     : ∀ x y, sub x y = add x (neg y)
  sub_self           : ∀ x, sub x x = zero
  mul_comm           : ∀ x y, mul x y = mul y x
  mul_assoc          : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  one_mul            : ∀ x, mul one x = x
  mul_one            : ∀ x, mul x one = x
  mul_zero           : ∀ x, mul x zero = zero
  mul_add            : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  mul_sub            : ∀ x y z, mul x (sub y z) = sub (mul x y) (mul x z)
  div_self_pos       : ∀ x, lt zero x → div x x = one
  div_zero_num       : ∀ y, lt zero y → div zero y = zero
  div_two_add_self   : ∀ x, add (div x (ofInt 2)) (div x (ofInt 2)) = x
  mul_div_cancel_pos : ∀ x y, lt zero y → mul (div x y) y = x
  neg_div            : ∀ x y, neg (div x y) = div (neg x) y

  -- Linear order & monotonicity laws
  le_refl            : ∀ x, le x x
  le_trans           : ∀ x y z, le x y → le y z → le x z
  le_antisymm        : ∀ x y, le x y → le y x → x = y
  le_total           : ∀ x y, le x y ∨ le y x
  lt_iff_le_not_le   : ∀ x y, lt x y ↔ (le x y ∧ ¬ le y x)
  add_le_add         : ∀ a b c d, le a b → le c d → le (add a c) (add b d)
  sub_le_sub         : ∀ a b c d, le a b → le d c → le (sub a c) (sub b d)
  neg_le_neg         : ∀ a b, le a b → le (neg b) (neg a)
  mul_nonneg         : ∀ a b, le zero a → le zero b → le zero (mul a b)
  mul_le_mul_nonneg_left : ∀ c a b, le zero c → le a b → le (mul c a) (mul c b)
  sq_mono_nonneg     : ∀ a b, le zero a → le a b → le (mul a a) (mul b b)
  div_nonneg_of_pos  : ∀ a b, le zero a → lt zero b → le zero (div a b)
  div_le_div_of_pos  : ∀ a b c, le a b → lt zero c → le (div a c) (div b c)
  div_ge_of_num_ge_den_le : ∀ a₁ a₂ b₁ b₂,
                         le zero a₁ → le a₁ a₂ → lt zero b₂ → le b₂ b₁ →
                         le (div a₁ b₁) (div a₂ b₂)

  -- Transcendental `exp` & EKV softplus laws
  exp_zero           : exp zero = one
  exp_pos            : ∀ x, lt zero (exp x)
  exp_pos_surj       : ∀ y : R, lt zero y → ∃ x : R, exp x = y
  exp_add            : ∀ x y, exp (add x y) = mul (exp x) (exp y)
  exp_mono           : ∀ x y, le x y → le (exp x) (exp y)
  one_add_le_exp     : ∀ x, le (add one x) (exp x)
  ln1pExp_spec       : ∀ z, exp (ln1pExp z) = add one (exp z)

namespace TranscendentalField

/-- Powers of ten are derived from the rational embedding. -/
def pow10 {R : Type} (TF : TranscendentalField R) : Nat → R
  | 0 => TF.one
  | n + 1 => TF.mul (TF.ofInt 10) (pow10 TF n)

theorem pow10_eq_ofRat {R : Type} (TF : TranscendentalField R) (n : Nat) :
    TF.pow10 n = TF.ofRat ((10 : Int)^n) 1 := by
  induction n with
  | zero => exact TF.one_eq_ofRat
  | succ n ih =>
    simp only [pow10, ih, TF.ofInt_eq_ofRat]
    rw [TF.ofRat_mul 10 ((10 : Int)^n) 1 1 (by decide) (by decide)]
    simp only [Nat.mul_one, Int.pow_succ, Int.mul_comm]

theorem pow10_pos {R : Type} (TF : TranscendentalField R) (n : Nat) :
    TF.lt TF.zero (TF.pow10 n) := by
  rw [pow10_eq_ofRat, TF.zero_eq_ofRat]
  apply (TF.ofRat_lt_iff 0 ((10 : Int)^n) 1 1 (by decide) (by decide)).mpr
  simpa using (Int.pow_pos (m := n) (show (0 : Int) < 10 from by decide))

/-- Cancel a common additive term using the ring identities. -/
theorem add_le_cancel_right {R : Type} (TF : TranscendentalField R) (a b c : R)
    (h : TF.le (TF.add a c) (TF.add b c)) : TF.le a b := by
  have h' := TF.add_le_add _ _ (TF.neg c) (TF.neg c) h (TF.le_refl _)
  simpa only [TF.add_assoc, TF.add_neg_self, TF.add_zero] using h'

theorem exp_injective {R : Type} (TF : TranscendentalField R) (x y : R)
    (h : TF.exp x = TF.exp y) : x = y := by
  have bound : ∀ a b : R, TF.exp a = TF.exp b → TF.le a b := by
    intro a b hab
    have he : TF.exp (TF.add a (TF.neg b)) = TF.one := by
      rw [TF.exp_add, hab, ← TF.exp_add, TF.add_neg_self, TF.exp_zero]
    have hb := TF.one_add_le_exp (TF.add a (TF.neg b))
    rw [he] at hb
    have hz : TF.le (TF.add (TF.add a (TF.neg b)) TF.one) (TF.add TF.zero TF.one) := by
      simpa only [TF.zero_add, TF.add_comm] using hb
    have hd := TF.add_le_cancel_right _ _ TF.one hz
    have hs := TF.add_le_add _ _ b b hd (TF.le_refl b)
    have hn : TF.add (TF.neg b) b = TF.zero := by rw [TF.add_comm, TF.add_neg_self]
    simpa only [TF.add_assoc, hn, TF.add_zero, TF.zero_add] using hs
  exact TF.le_antisymm x y (bound x y h) (bound y x h.symm)

theorem exp_strictMono {R : Type} (TF : TranscendentalField R) (x y : R)
    (h : TF.lt x y) : TF.lt (TF.exp x) (TF.exp y) := by
  obtain ⟨hxy, hnot⟩ := (TF.lt_iff_le_not_le x y).mp h
  have he := TF.exp_mono x y hxy
  apply (TF.lt_iff_le_not_le _ _).mpr
  refine ⟨he, fun hyx => ?_⟩
  have hEq := TF.exp_injective x y (TF.le_antisymm _ _ he hyx)
  exact hnot (hEq ▸ TF.le_refl x)

/-- Positive square roots are unique; positive surjectivity supplies logarithms. -/
theorem positive_sqrt_unique {R : Type} (TF : TranscendentalField R) (a b : R)
    (ha : TF.lt TF.zero a) (hb : TF.lt TF.zero b)
    (hsq : TF.mul a a = TF.mul b b) : a = b := by
  obtain ⟨u, hu⟩ := TF.exp_pos_surj a ha
  obtain ⟨v, hv⟩ := TF.exp_pos_surj b hb
  have hd : TF.add u u = TF.add v v := by
    apply TF.exp_injective
    rw [TF.exp_add, TF.exp_add, hu, hv, hsq]
  have cancel : ∀ x y : R, TF.le (TF.add x x) (TF.add y y) → TF.le x y := by
    intro x y h
    cases TF.le_total x y with
    | inl hxy => exact hxy
    | inr hyx =>
      have h1 := TF.add_le_add y x x x hyx (TF.le_refl x)
      have h2 := TF.le_trans _ _ _ h1 h
      rw [TF.add_comm y x] at h2
      exact TF.add_le_cancel_right x y y h2
  have huv := TF.le_antisymm u v (cancel u v (hd ▸ TF.le_refl _))
    (cancel v u (hd ▸ TF.le_refl _))
  rw [← hu, ← hv, huv]

theorem neg_neg {R : Type} (TF : TranscendentalField R) (x : R) : TF.neg (TF.neg x) = x := by
  calc
    TF.neg (TF.neg x) = TF.add (TF.neg (TF.neg x)) TF.zero := (TF.add_zero _).symm
    _ = TF.add (TF.neg (TF.neg x)) (TF.add (TF.neg x) x) := by rw [TF.add_comm (TF.neg x) x, TF.add_neg_self]
    _ = TF.add (TF.add (TF.neg (TF.neg x)) (TF.neg x)) x := (TF.add_assoc _ _ _).symm
    _ = x := by rw [TF.add_comm (TF.neg (TF.neg x)) (TF.neg x), TF.add_neg_self, TF.zero_add]

theorem mul_neg {R : Type} (TF : TranscendentalField R) (x y : R) :
    TF.mul x (TF.neg y) = TF.neg (TF.mul x y) := by
  have h : TF.add (TF.mul x y) (TF.mul x (TF.neg y)) = TF.zero := by
    rw [← TF.mul_add, TF.add_neg_self, TF.mul_zero]
  have h' := congrArg (fun z => TF.add (TF.neg (TF.mul x y)) z) h
  simpa only [← TF.add_assoc, TF.add_comm, TF.add_neg_self, TF.zero_add, TF.add_zero] using h'

theorem mul_le_mul_nonpos_left {R : Type} (TF : TranscendentalField R) (c a b : R)
    (hc : TF.le c TF.zero) (hab : TF.le a b) : TF.le (TF.mul c b) (TF.mul c a) := by
  have hn := TF.neg_le_neg c TF.zero hc
  have nz : TF.neg TF.zero = TF.zero := by
    have h := TF.add_neg_self TF.zero
    simpa only [TF.zero_add] using h
  rw [nz] at hn
  have h := TF.mul_le_mul_nonneg_left (TF.neg c) a b hn hab
  rw [TF.mul_comm (TF.neg c) a, TF.mul_comm (TF.neg c) b, TF.mul_neg, TF.mul_neg] at h
  have h' := TF.neg_le_neg _ _ h
  simpa only [TF.neg_neg, TF.mul_comm] using h'

theorem exp_neg {R : Type} (TF : TranscendentalField R) (x : R) :
    TF.exp (TF.neg x) = TF.div TF.one (TF.exp x) := by
  have he : TF.mul (TF.exp (TF.neg x)) (TF.exp x) = TF.one := by
    rw [← TF.exp_add, TF.add_comm, TF.add_neg_self, TF.exp_zero]
  have hd := TF.mul_div_cancel_pos TF.one (TF.exp x) (TF.exp_pos x)
  have cancel : ∀ a b, TF.mul a (TF.exp x) = TF.mul b (TF.exp x) → a = b := by
    intro a b h
    have h' := congrArg (fun z => TF.mul z (TF.exp (TF.neg x))) h
    have hp : TF.mul (TF.exp x) (TF.exp (TF.neg x)) = TF.one := by rw [TF.mul_comm]; exact he
    simpa only [TF.mul_assoc, hp, TF.mul_one] using h'
  exact cancel _ _ (he.trans hd.symm)

theorem div_eq_mul_inv_pos {R : Type} (TF : TranscendentalField R) (x y : R)
    (hy : TF.lt TF.zero y) : TF.div x y = TF.mul x (TF.div TF.one y) := by
  have hi := TF.mul_div_cancel_pos TF.one y hy
  have hyi : TF.mul y (TF.div TF.one y) = TF.one := by rw [TF.mul_comm]; exact hi
  have h := congrArg (fun z => TF.mul z (TF.div TF.one y)) (TF.mul_div_cancel_pos x y hy)
  simpa only [TF.mul_assoc, hyi, TF.mul_one] using h

end TranscendentalField

namespace PhysicsModels

/-- Shockley p-n junction / ESD diode constitutive equation:
    `I_D(v) = I_s * (exp(v / (n * V_T)) - 1)`. -/
def shockleyDiodeCurrent {R : Type} (TF : TranscendentalField R) (i_s n vt v : R) : R :=
  TF.mul i_s (TF.sub (TF.exp (TF.div v (TF.mul n vt))) TF.one)

/-- At zero bias `v = 0`, Shockley diode current is identically `0` for any `n * vt > 0`. -/
theorem shockley_zero_bias {R : Type} (TF : TranscendentalField R) (i_s n vt : R)
    (hnvt : TF.lt TF.zero (TF.mul n vt)) :
    shockleyDiodeCurrent TF i_s n vt TF.zero = TF.zero := by
  unfold shockleyDiodeCurrent
  rw [TF.div_zero_num (TF.mul n vt) hnvt]
  rw [TF.exp_zero]
  rw [TF.sub_self TF.one]
  exact TF.mul_zero i_s

/-- Under forward bias `v ≥ 0` and positive thermal scale `n * vt > 0`, `I_D(v) ≥ 0`. -/
theorem shockley_forward_nonneg {R : Type} (TF : TranscendentalField R) (i_s n vt v : R)
    (his : TF.le TF.zero i_s)
    (hv : TF.le TF.zero v)
    (hnvt : TF.lt TF.zero (TF.mul n vt)) :
    TF.le TF.zero (shockleyDiodeCurrent TF i_s n vt v) := by
  unfold shockleyDiodeCurrent
  have harg : TF.le TF.zero (TF.div v (TF.mul n vt)) := TF.div_nonneg_of_pos v (TF.mul n vt) hv hnvt
  have hexp : TF.le TF.one (TF.exp (TF.div v (TF.mul n vt))) := by
    rw [← TF.exp_zero]
    exact TF.exp_mono TF.zero (TF.div v (TF.mul n vt)) harg
  have hsub : TF.le TF.zero (TF.sub (TF.exp (TF.div v (TF.mul n vt))) TF.one) := by
    have h0 : TF.sub TF.one TF.one = TF.zero := TF.sub_self TF.one
    rw [← h0]
    exact TF.sub_le_sub TF.one (TF.exp (TF.div v (TF.mul n vt))) TF.one TF.one hexp (TF.le_refl TF.one)
  exact TF.mul_nonneg i_s _ his hsub

/-- Pure-`exp` EKV / BSIM-CMG / ASM-HEMT softplus auxiliary encoding (`exp(y) = 1 + exp(z)`),
    eliminating `log` from `smt2-exp` solver queries. -/
def ekvSoftplusRel {R : Type} (TF : TranscendentalField R) (z y : R) : Prop :=
  TF.exp y = TF.add TF.one (TF.exp z)

/-- `TF.ln1pExp z` witnesses the pure-`exp` EKV softplus auxiliary relation AND satisfies `0 ≤ y`. -/
theorem ekv_softplus_witness_nonneg {R : Type} (TF : TranscendentalField R) (z : R) :
    ekvSoftplusRel TF z (TF.ln1pExp z) ∧ TF.le TF.zero (TF.ln1pExp z) := by
  refine ⟨TF.ln1pExp_spec z, ?_⟩
  cases TF.le_total TF.zero (TF.ln1pExp z) with
  | inl h => exact h
  | inr hle =>
    -- If `y ≤ 0`, then `exp(y) ≤ exp(0) = 1`, contradicting `exp(y) = 1 + exp(z) > 1` since `exp(z) > 0`!
    have hexp_le : TF.le (TF.exp (TF.ln1pExp z)) TF.one := by
      rw [← TF.exp_zero]
      exact TF.exp_mono (TF.ln1pExp z) TF.zero hle
    rw [TF.ln1pExp_spec z] at hexp_le
    have hpos : TF.lt TF.zero (TF.exp z) := TF.exp_pos z
    rcases (TF.lt_iff_le_not_le TF.zero (TF.exp z)).mp hpos with ⟨_, hnot_ez_le_0⟩
    have h_one_add : TF.le (TF.add TF.one (TF.exp z)) (TF.add TF.one TF.zero) := by
      rw [TF.add_zero TF.one]
      exact hexp_le
    -- Subtract `1` on the left via `sub_le_sub`: `(1 + exp z) - 1 ≤ 1 - 1 = 0`
    have hez_eq : TF.sub (TF.add (TF.exp z) TF.one) TF.one = TF.exp z := by
      rw [TF.sub_eq_add_neg, TF.add_assoc, TF.add_neg_self, TF.add_zero]
    have h_ez_le_0 : TF.le (TF.exp z) TF.zero := by
      rw [← hez_eq, ← TF.sub_self TF.one]
      rw [TF.add_comm TF.one (TF.exp z)] at h_one_add
      rw [TF.add_zero TF.one] at h_one_add
      exact TF.sub_le_sub (TF.add (TF.exp z) TF.one) TF.one TF.one TF.one h_one_add (TF.le_refl TF.one)
    exact False.elim (hnot_ez_le_0 h_ez_le_0)

theorem ekv_softplus_unique {R : Type} (TF : TranscendentalField R) (z y : R)
    (h : ekvSoftplusRel TF z y) : y = TF.ln1pExp z :=
  TF.exp_injective y (TF.ln1pExp z) (h.trans (TF.ln1pExp_spec z).symm)

theorem ekv_softplus_iff {R : Type} (TF : TranscendentalField R) (z y : R) :
    ekvSoftplusRel TF z y ↔ y = TF.ln1pExp z := by
  constructor
  · exact ekv_softplus_unique TF z y
  · intro h
    rw [h]
    exact TF.ln1pExp_spec z

/-- Coupled 2nm Gate-All-Around (`gt2n`) stacked-nanosheet electro-thermal balance:
    `T_ch = T_amb + R_th * V_ds * I_stack`. -/
def gaaElectroThermalBalance {R : Type} (TF : TranscendentalField R)
    (t_ch t_amb r_th v_ds i_stack : R) : Prop :=
  t_ch = TF.add t_amb (TF.mul r_th (TF.mul v_ds i_stack))

/-- Thermodynamic non-self-cooling law: under passive thermal resistance `R_th ≥ 0`,
    forward bias `V_ds ≥ 0`, and positive drain-to-source current `I_stack ≥ 0`,
    channel temperature satisfies `T_amb ≤ T_ch`. -/
theorem gaa_self_heating_ge_ambient {R : Type} (TF : TranscendentalField R)
    (t_ch t_amb r_th v_ds i_stack : R)
    (hbal : gaaElectroThermalBalance TF t_ch t_amb r_th v_ds i_stack)
    (hrth : TF.le TF.zero r_th)
    (hvds : TF.le TF.zero v_ds)
    (hist : TF.le TF.zero i_stack) :
    TF.le t_amb t_ch := by
  rw [hbal]
  have hp : TF.le TF.zero (TF.mul v_ds i_stack) := TF.mul_nonneg v_ds i_stack hvds hist
  have hdt : TF.le TF.zero (TF.mul r_th (TF.mul v_ds i_stack)) := TF.mul_nonneg r_th _ hrth hp
  have h0 : t_amb = TF.add t_amb TF.zero := (TF.add_zero t_amb).symm
  have hle := TF.add_le_add t_amb t_amb TF.zero (TF.mul r_th (TF.mul v_ds i_stack)) (TF.le_refl t_amb) hdt
  rw [← h0] at hle
  exact hle

/-- Cancellation-free Scharfetter–Gummel Bernoulli identity:
    whenever `B_p * (E - 1) = Δ` and `B_m = B_p * E`, the classical difference identity
    `B_m - B_p = Δ` holds identically without subtractive cancellation! -/
theorem sg_cancellation_free_identity {R : Type} (TF : TranscendentalField R)
    (bp ee delta : R)
    (hbern : TF.mul bp (TF.sub ee TF.one) = delta) :
    TF.sub (TF.mul bp ee) bp = delta := by
  have h1 : TF.mul bp (TF.sub ee TF.one) = TF.sub (TF.mul bp ee) bp := by
    rw [TF.mul_sub bp ee TF.one, TF.mul_one bp]
  rw [← h1]
  exact hbern

/-- Integer exponentiation `x^n` in `TranscendentalField R`. -/
def powNat {R : Type} (TF : TranscendentalField R) (x : R) : Nat → R
  | 0 => TF.one
  | k + 1 => TF.mul x (powNat TF x k)

/-- Factorial `k!` on `Nat`. -/
def factNat : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factNat k

/-- Truncated Maclaurin polynomial `Σ_{k=0}^{N} t^k / k!` for `exp(t)`. -/
def expTaylorSum {R : Type} (TF : TranscendentalField R) (t : R) : Nat → R
  | 0 => TF.one
  | k + 1 =>
    TF.add (expTaylorSum TF t k)
      (TF.div (powNat TF t (k + 1)) (TF.ofInt (factNat (k + 1))))

/-- Path-A Solver-Synthesis Target 1 (`ExpHalfTaylor12Target`):
    Degree-12 rational Taylor remainder enclosure on `t ∈ [-1/2, 1/2]`:
    `|exp(t) - Σ_{k=0}^{12} t^k / k!| ≤ (2 / 13!) * t^12` (even-power uniform bound `2 / 13!`). -/
def ExpHalfTaylor12Target {R : Type} (TF : TranscendentalField R) : Prop :=
  ∀ t : R,
    TF.le (TF.ofRat (-1) 2) t →
    TF.le t (TF.ofRat 1 2) →
    let err := TF.sub (TF.exp t) (expTaylorSum TF t 12)
    let bound := TF.mul (TF.ofRat 2 (factNat 13)) (powNat TF t 12)
    TF.le (TF.neg bound) err ∧ TF.le err bound

/-- Degree-10 rational Bernoulli Maclaurin polynomial on `|x| ≤ 1/8`:
    `S_10(x) = 1 - x/2 + x^2/12 - x^4/720 + x^6/30240 - x^8/1209600 + x^10/47900160`. -/
def bernTaylor10 {R : Type} (TF : TranscendentalField R) (x : R) : R :=
  let x2 := TF.mul x x
  let x4 := TF.mul x2 x2
  let x6 := TF.mul x4 x2
  let x8 := TF.mul x4 x4
  let x10 := TF.mul x8 x2
  TF.add
    (TF.sub
      (TF.add
        (TF.sub
          (TF.add (TF.sub TF.one (TF.div x (TF.ofInt 2))) (TF.div x2 (TF.ofInt 12)))
          (TF.div x4 (TF.ofInt 720)))
        (TF.div x6 (TF.ofInt 30240)))
      (TF.div x8 (TF.ofInt 1209600)))
    (TF.div x10 (TF.ofInt 47900160))

/-- Path-A Solver-Synthesis Target 2 (`BernSmallTaylor10Target`):
    Removable-singularity Scharfetter–Gummel Bernoulli enclosure on `x ∈ [-1/8, 1/8]`:
    `|B(x) - S_10(x)| ≤ x^12 / 10^9` whenever `B(x) * (exp(x) - 1) = x` and `x ≠ 0`. -/
def BernSmallTaylor10Target {R : Type} (TF : TranscendentalField R) : Prop :=
  ∀ (x bx : R),
    x ≠ TF.zero →
    TF.le (TF.ofRat (-1) 8) x →
    TF.le x (TF.ofRat 1 8) →
    TF.mul bx (TF.sub (TF.exp x) TF.one) = x →
    let err := TF.sub bx (bernTaylor10 TF x)
    let bound := TF.div (powNat TF x 12) (TF.ofInt 1000000000)
    TF.le (TF.neg bound) err ∧ TF.le err bound

/-- Linear tangent lower bound `1 + t ≤ exp(t)` on `[-1/2, 1/2]`. -/
def ExpHalfLowerTarget {R : Type} (TF : TranscendentalField R) : Prop :=
  ∀ t : R,
    TF.le (TF.ofRat (-1) 2) t →
    TF.le t (TF.ofRat 1 2) →
    TF.le (TF.add TF.one t) (TF.exp t)

/-- `ExpHalfLowerTarget` holds unconditionally in any `TranscendentalField`. -/
theorem exp_half_lower_proved {R : Type} (TF : TranscendentalField R) :
    ExpHalfLowerTarget TF := by
  intro t _ _
  exact TF.one_add_le_exp t

/-- Path-B Solver-Target Lemma 2 (`BernSmallTarget`):
    Singularity-free global Euler-coth quadratic/quartic bracket specification around `Δ = 0`,
    eliminating removable `0 / 0` division in Scharfetter–Gummel TCAD stamps. -/
def BernGlobalBracketSpec {R : Type} (TF : TranscendentalField R) (B : R → R) : Prop :=
  ∀ delta : R,
    let bp := B delta
    let d2 := TF.mul delta delta
    let d4 := TF.mul d2 d2
    let upper := TF.add (TF.sub TF.one (TF.div delta (TF.ofInt 2))) (TF.div d2 (TF.ofInt 12))
    let lower := TF.sub upper (TF.div d4 (TF.ofInt 720))
    TF.mul bp (TF.sub (TF.exp delta) TF.one) = delta ∧
    TF.le lower bp ∧ TF.le bp upper

/-- The brackets, unlike the transport identity alone, fix the removable singularity. -/
theorem bern_global_bracket_zero {R : Type} (TF : TranscendentalField R)
    (B : R → R) (h : BernGlobalBracketSpec TF B) : B TF.zero = TF.one := by
  have pos : ∀ n : Nat, 0 < n → TF.lt TF.zero (TF.ofInt (n : Int)) := by
    intro n hn
    rw [TF.zero_eq_ofRat, TF.ofInt_eq_ofRat]
    apply (TF.ofRat_lt_iff 0 (n : Int) 1 1 (by decide) (by decide)).mpr
    omega
  have hb := (h TF.zero).2
  have subzero : TF.sub TF.one TF.zero = TF.one := by
    rw [TF.one_eq_ofRat, TF.zero_eq_ofRat, TF.ofRat_sub 1 0 1 1 (by decide) (by decide)]
    rfl
  simp only [TF.mul_zero] at hb
  rw [TF.div_zero_num (TF.ofInt 2) (pos 2 (by decide)),
      TF.div_zero_num (TF.ofInt 12) (pos 12 (by decide)),
      TF.div_zero_num (TF.ofInt 720) (pos 720 (by decide)),
      subzero, TF.add_zero, subzero] at hb
  exact TF.le_antisymm _ _ hb.2 hb.1

end PhysicsModels
end SpiceSmtBench
