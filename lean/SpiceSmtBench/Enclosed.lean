import SpiceSmtBench.RealInterval

namespace SpiceSmtBench
open LeanCert.Core IntervalRat

/-- A real expression and its certified rational enclosure. An absent box
represents the whole real line, including at an unresolved division. -/
structure Enclosed where
  val : ℝ
  box : Option IntervalRat
  valid : ∀ {b}, box = some b → val ∈ b

namespace Enclosed

def const (q : ℚ) : Enclosed := ⟨q,some (.singleton q),by rintro _ ⟨⟩; exact mem_singleton _⟩

/-- Preserve the stamp's real division while evaluating the rational endpoints. -/
noncomputable def fraction (z : Int) (d : Nat) : Enclosed :=
  ⟨(z:ℝ)/d,some (.singleton ((z:ℚ)/d)),by
    rintro _ ⟨⟩; simpa using mem_singleton ((z:ℚ)/d)⟩

noncomputable def integer (z : Int) : Enclosed :=
  ⟨z,some (.singleton z),by rintro _ ⟨⟩; simpa using mem_singleton (z:ℚ)⟩

def trim (b : IntervalRat) : IntervalRat :=
  let s : ℚ := 2^192
  ⟨⌊b.lo*s⌋/s,⌈b.hi*s⌉/s,by
    apply div_le_div_of_nonneg_right _ (by norm_num [s])
    exact (Int.floor_le _).trans ((mul_le_mul_of_nonneg_right b.le (by norm_num [s])).trans (Int.le_ceil _))⟩

private theorem mem_trim {x : ℝ} {b : IntervalRat} (h : x ∈ b) : x ∈ trim b := by
  have lo : (trim b).lo ≤ b.lo := (div_le_iff₀ (by norm_num)).2 (Int.floor_le _)
  have hi : b.hi ≤ (trim b).hi := (le_div_iff₀ (by norm_num)).2 (Int.le_ceil _)
  exact ⟨(Rat.cast_le.mpr lo).trans h.1,h.2.trans (Rat.cast_le.mpr hi)⟩

private def unary (f : ℝ → ℝ) (F : IntervalRat → IntervalRat)
    (hf : ∀ {x b}, x ∈ b → f x ∈ F b) (x : Enclosed) : Enclosed :=
  ⟨f x.val,x.box.map F,by intro b h; obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp h; exact hf (x.valid ha)⟩

private def binary (f : ℝ → ℝ → ℝ) (F : IntervalRat → IntervalRat → IntervalRat)
    (hf : ∀ {x y a b}, x ∈ a → y ∈ b → f x y ∈ F a b) (x y : Enclosed) : Enclosed :=
  ⟨f x.val y.val,do return F (← x.box) (← y.box),by
    intro b h
    cases hx : x.box <;> cases hy : y.box <;> simp [hx,hy] at h
    cases h; exact hf (x.valid hx) (y.valid hy)⟩

noncomputable instance : Add Enclosed := ⟨binary (·+·) IntervalRat.add mem_add⟩
noncomputable instance : Sub Enclosed := ⟨binary (·-·) IntervalRat.sub mem_sub⟩
noncomputable instance : Neg Enclosed := ⟨unary Neg.neg IntervalRat.neg mem_neg⟩
noncomputable instance : Mul Enclosed := ⟨binary (·*·) (fun a b => trim (a.mul b))
  (fun hx hy => mem_trim (mem_mul hx hy))⟩

private def invBox (a : IntervalRat) : Option IntervalRat :=
  if h : a.containsZero then none else some (trim (invNonzero ⟨a,h⟩))
private theorem mem_inv {x : ℝ} {a b : IntervalRat} (hx : x ∈ a) (h : invBox a = some b) :
    x⁻¹ ∈ b := by
  unfold invBox at h; split at h <;> simp_all only [reduceCtorEq,Option.some.injEq]
  subst b; apply mem_trim; apply mem_invNonzero hx
  intro he; subst x; apply ‹¬ a.containsZero›
  exact ⟨by exact_mod_cast hx.1,by exact_mod_cast hx.2⟩

private noncomputable def inv (x : Enclosed) : Enclosed :=
  ⟨x.val⁻¹,x.box.bind invBox,by
    intro b h; obtain ⟨a,ha,hab⟩ := Option.bind_eq_some_iff.mp h; exact mem_inv (x.valid ha) hab⟩
noncomputable instance : Div Enclosed := ⟨fun x y => x * inv y⟩

@[simp] theorem const_val (q : ℚ) : (const q).val = q := rfl
@[simp] theorem add_val (x y : Enclosed) : (x+y).val = x.val+y.val := rfl
@[simp] theorem sub_val (x y : Enclosed) : (x-y).val = x.val-y.val := rfl
@[simp] theorem neg_val (x : Enclosed) : (-x).val = -x.val := rfl
@[simp] theorem mul_val (x y : Enclosed) : (x*y).val = x.val*y.val := rfl
@[simp] theorem div_val (x y : Enclosed) : (x/y).val = x.val/y.val := by rfl

noncomputable def exp := unary Real.exp (fun b => trim (b.expComputable 28))
  (fun h => mem_trim (mem_expComputable h _))

private def logBox (a : IntervalRat) :=
  if 0 < a.lo then some (trim (a.logComputable 42)) else none
noncomputable def log (x : Enclosed) : Enclosed :=
  ⟨Real.log x.val,x.box.bind logBox,by
    intro b h; obtain ⟨a,ha,hab⟩ := Option.bind_eq_some_iff.mp h
    unfold logBox at hab; split at hab <;> simp_all only [reduceCtorEq,Option.some.injEq]
    subst b; exact mem_trim (mem_logComputable (x.valid ha) (by assumption) _)⟩

/-- A rational bracket for a square root, verified by squaring its endpoints. -/
noncomputable def sqrt (x : Enclosed) (l h : ℚ) : Enclosed :=
  ⟨Real.sqrt x.val,do
    let b ← x.box
    if ok : 0 ≤ l ∧ l ≤ h ∧ l*l ≤ b.lo ∧ b.hi ≤ h*h then
      return ⟨l,h,ok.2.1⟩
    else none,by
    intro b he
    cases hx : x.box with
    | none => simp [hx] at he
    | some a =>
      rw [hx] at he
      dsimp only [bind,Option.bind,pure,Pure.pure] at he
      split at he <;> simp_all only [reduceCtorEq,Option.some.injEq]
      subst b
      obtain ⟨lp,lh,low,high⟩ := ‹0 ≤ l ∧ _›
      have m := x.valid hx
      have L := (Rat.cast_le (K := ℝ)).mpr low
      have H := (Rat.cast_le (K := ℝ)).mpr high
      push_cast at L H
      have nn : 0 ≤ x.val := by nlinarith only [m.1,L,sq_nonneg (l:ℝ)]
      have hp : 0 ≤ (h:ℝ) := Rat.cast_nonneg.mpr (lp.trans lh)
      change (l:ℝ) ≤ Real.sqrt x.val ∧ Real.sqrt x.val ≤ (h:ℝ)
      constructor <;> nlinarith only [Real.sq_sqrt nn,Real.sqrt_nonneg x.val,hp,m.1,m.2,L,H]⟩

def positive (x : Enclosed) : Bool := x.box.any fun b => decide (0<b.lo)
theorem pos {x : Enclosed} (hp : x.positive) : 0<x.val := by
  unfold positive at hp; cases h : x.box with
  | none => simp [h] at hp
  | some b =>
    simp [h] at hp
    exact (Rat.cast_pos.mpr hp).trans_le (x.valid h).1

def inside (x : Enclosed) (l h : ℚ) : Bool := x.box.any fun b => decide (l ≤ b.lo ∧ b.hi ≤ h)
theorem bounds {x : Enclosed} {l h : ℚ} (ok : x.inside l h) : (l:ℝ) ≤ x.val ∧ x.val ≤ (h:ℝ) := by
  unfold inside at ok; cases he : x.box with
  | none => simp [he] at ok
  | some b =>
    simp [he] at ok
    exact ⟨(Rat.cast_le.mpr ok.1).trans (x.valid he).1,(x.valid he).2.trans (Rat.cast_le.mpr ok.2)⟩

end Enclosed
end SpiceSmtBench
