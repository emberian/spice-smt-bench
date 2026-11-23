import SpiceSmtBench.RealPhysics
import SpiceSmtBench.IntervalCheck
import LeanCert.Core.IntervalRat.Taylor

namespace SpiceSmtBench.RealInterval
open LeanCert.Core IntervalCheck

abbrev I := IntervalRat

-- Round after transcendental operations so later Taylor evaluations operate
-- on small integer endpoints even when their inputs have complex denominators.
private def down (q : ℚ) : ℚ := ⌊q * 2^52⌋ / 2^52
private def up (q : ℚ) : ℚ := ⌈q * 2^52⌉ / 2^52

private theorem down_le (q : ℚ) : down q ≤ q := (div_le_iff₀ (by norm_num)).2 (Int.floor_le _)
private theorem le_up (q : ℚ) : q ≤ up q := (le_div_iff₀ (by norm_num)).2 (Int.le_ceil _)

private def rounded (a : I) : I := ⟨down a.lo,up a.hi,(down_le _).trans (a.le.trans (le_up _))⟩
private theorem mem_rounded {a : I} {x : ℝ} (h : x ∈ a) : x ∈ rounded a :=
  ⟨(show (down a.lo : ℝ) ≤ (a.lo:ℝ) by exact_mod_cast down_le a.lo).trans h.1,
   h.2.trans (by exact_mod_cast le_up a.hi)⟩

private def expI (a : I) : I := rounded ((rounded a).expComputable 19)
private theorem mem_expI {x : ℝ} {a : I} (h : x ∈ a) : Real.exp x ∈ expI a :=
  mem_rounded (IntervalRat.mem_expComputable (mem_rounded h) 19)

private def spI (a : I) : Option I :=
  let arg := (IntervalRat.singleton 1).add (expI a)
  if 0 < arg.lo then some (rounded (arg.logComputable 32)) else none

private theorem mem_spI {a v : I} {x : ℝ} (h : x ∈ a) (ok : spI a = some v) :
    Real.log (1+Real.exp x) ∈ v := by
  dsimp only [spI] at ok
  split at ok <;> simp_all only [Option.some.injEq, reduceCtorEq]
  subst v
  apply mem_rounded
  apply IntervalRat.mem_logComputable _ (by assumption)
  exact IntervalRat.mem_add (by simpa using IntervalRat.mem_singleton 1) (mem_expI h)

private def divI (a b : I) : Option I :=
  if h : 0 < b.lo then
    some (a.mul (IntervalRat.invNonzero ⟨b,fun hz => (not_le_of_gt h) hz.1⟩))
  else none

private theorem mem_divI {a b v : I} {x y : ℝ} (hx : x ∈ a) (hy : y ∈ b)
    (ok : divI a b = some v) : x/y ∈ v := by
  unfold divI at ok
  split at ok <;> simp_all only [Option.some.injEq, reduceCtorEq]
  subst v
  rw [div_eq_mul_inv]
  apply IntervalRat.mem_mul hx
  apply IntervalRat.mem_invNonzero hy
  exact ne_of_gt ((show 0 < (b.lo:ℝ) by exact_mod_cast (by assumption : 0 < b.lo)).trans_le hy.1)

/-- Real enclosure of the same stamped expression as the coarse sign checker.
Division and logarithms require a certified positive denominator or argument. -/
def enclose (env : Nat → I) : PExpr → Option I
  | .var i => some (env i)
  | .const q => some (IntervalRat.singleton ((q.num:ℚ)/q.den))
  | .neg a => IntervalRat.neg <$> enclose env a
  | .exp a => expI <$> enclose env a
  | .softplus a => enclose env a >>= spI
  | .add a b => return (← enclose env a).add (← enclose env b)
  | .sub a b => return (← enclose env a).sub (← enclose env b)
  | .mul a b => return (← enclose env a).mul (← enclose env b)
  | .div a b => do divI (← enclose env a) (← enclose env b)

theorem enclose_sound (e : PExpr) (env : Nat → I) (ρ : Nat → ℝ) (h : ∀ i, ρ i ∈ env i)
    {v : I} (ok : enclose env e = some v) : e.eval realTF ρ ∈ v := by
  induction e generalizing v with
  | var i => cases ok; exact h i
  | const q => cases ok; simpa [PExpr.eval,QRat.eval,realTF] using IntervalRat.mem_singleton ((q.num:ℚ)/q.den)
  | neg a ih | softplus a ih | exp a ih =>
    cases ha : enclose env a with
    | none => simp [enclose,ha] at ok
    | some va =>
      simp [enclose, ha] at ok
      first | exact mem_spI (ih ha) ok
            | subst v; exact IntervalRat.mem_neg (ih ha)
            | subst v; exact mem_expI (ih ha)
  | add a b ia ib | sub a b ia ib | mul a b ia ib | div a b ia ib =>
    cases ha : enclose env a <;> cases hb : enclose env b <;> simp [enclose, ha, hb] at ok
    first | exact mem_divI (ia ha) (ib hb) ok
          | subst v; exact IntervalRat.mem_add (ia ha) (ib hb)
          | subst v; exact IntervalRat.mem_sub (ia ha) (ib hb)
          | subst v; exact IntervalRat.mem_mul (ia ha) (ib hb)
/-- Successful evaluation on a box certifies continuity there, including the
nonvanishing side condition at every division in the expression. -/
theorem enclose_continuous {X : Type*} [TopologicalSpace X] (e : PExpr)
    (env : Nat → I) (ρ : X → Nat → ℝ) (bound : ∀ x i, ρ x i ∈ env i)
    (hc : ∀ i, Continuous (fun x => ρ x i)) {v : I} (ok : enclose env e = some v) :
    Continuous (fun x => e.eval realTF (ρ x)) := by
  induction e generalizing v with
  | var i => exact hc i
  | const => exact continuous_const
  | neg a ih | exp a ih | softplus a ih =>
    cases ha : enclose env a with
    | none => simp [enclose,ha] at ok
    | some va =>
      first | exact (ih ha).neg | exact Real.continuous_exp.comp (ih ha)
            | exact (continuous_const.add (Real.continuous_exp.comp (ih ha))).log (fun x => ne_of_gt (add_pos zero_lt_one (Real.exp_pos _)))
  | add a b ia ib | sub a b ia ib | mul a b ia ib | div a b ia ib =>
    cases ha : enclose env a <;> cases hb : enclose env b <;> simp [enclose, ha, hb] at ok
    first | exact (ia ha).add (ib hb) | exact (ia ha).sub (ib hb) | exact (ia ha).mul (ib hb)
          | apply (ia ha).div (ib hb)
            intro x
            unfold divI at ok
            split at ok
            · apply ne_of_gt
              rename_i hp
              exact lt_of_lt_of_le (by exact_mod_cast hp) (enclose_sound b env (ρ x) (bound x) hb).1
            · contradiction

end SpiceSmtBench.RealInterval
