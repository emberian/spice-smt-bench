import SpiceSmtBench.RealPhysics
import SpiceSmtBench.TargetsGenerated
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace SpiceSmtBench.PdnCertificate

-- BGA and core voltages are measured relative to 0.90 V.
private structure Coeff where
  b : ℚ
  v : ℚ
  i : ℚ
  h : ℚ
  deriving DecidableEq
private structure State where
  b : ℝ
  v : ℝ
  i : ℝ
  h : ℝ
private noncomputable def Coeff.eval (q : Coeff) (s : State) : ℝ := q.b*s.b + q.v*s.v + q.i*s.i + q.h*s.h

-- Backward Euler in A, V, ns and nF. u is the current across the solder void,
-- w the MLCC's internal voltage relative to the rail, d the core load.
private structure Step (s t : State) (r u w d : ℝ) : Prop where
  bga : 32*(t.b-s.b) = t.i-u
  core : 12*(t.v-s.v) = u-t.h-d
  plane : (88/100)*(t.i-s.i) = -t.b-t.i/500
  mlcc : (56/100)*(t.h-s.h) = t.v-w-3/1000*t.h
  void : t.b-t.v = r*u

private structure Multipliers where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  e : ℚ

-- Solve the transposed, constant-resistance step at the center of a bin.
private def adjoint (r : ℚ) (q : Coeff) : Multipliers :=
  let ra := 1/(32+1/(882/1000 : ℚ))
  let rb := 1/(12+1/(563/1000 : ℚ))
  let x := ra*(q.b - q.i/(882/1000))
  let y := rb*(q.v + q.h/(563/1000))
  let e := (x-y)/(r+ra+rb)
  let a := x-ra*e
  let b := y+rb*e
  ⟨a,b,(q.i+a)/(882/1000),(q.h-b)/(563/1000),e⟩

private def next (m : Multipliers) : Coeff := ⟨32*m.a,12*m.b,88/100*m.c,56/100*m.d⟩
private def valid (r : ℚ) (q : Coeff) (m : Multipliers) : Bool := decide
  (32*m.a+m.c+m.e=q.b ∧ 12*m.b-m.d-m.e=q.v ∧ 882/1000*m.c-m.a=q.i ∧
   563/1000*m.d+m.b=q.h ∧ m.a-m.b=r*m.e)

-- The inequalities hold independently at every sample, so the replay only
-- needs bounds on the load, MLCC voltage and the deviation in void resistance.
private def cost (m : Multipliers) : ℚ :=
  max (m.b/10) (6/5*m.b) + |m.d|/125 + |m.e|/400

private def check (r : ℚ) (steps : Nat) (q : Coeff) (loss : ℚ) : Bool :=
  decide (-1/10 ≤ q.i/10-loss) && match steps with
  | 0 => true
  | k+1 => let m := adjoint r q
           valid r q m && check r k (next m) (loss+cost m)

private def center (i : Fin 54) : ℚ := (5+2*(i.val:ℚ))/4000
private def core : Coeff := ⟨0,1,0,0⟩

set_option maxRecDepth 32000 in
private theorem replay : ∀ j : Fin 54, check (center j) 16 core 0 := by decide +kernel

private theorem perturbed_step {s t : State} {r u w d : ℝ} (f : Step s t r u w d)
    {r0 : ℚ} (rbox : |r-r0| ≤ 1/4000) (ubox : |u| ≤ 10)
    (wbox : |w| ≤ 1/125) (dlo : 1/10 ≤ d) (dhi : d ≤ 6/5)
    {q : Coeff} {m : Multipliers} (ok : valid r0 q m) :
    (next m).eval s - (cost m : ℝ) ≤ q.eval t := by
  obtain ⟨hb,hv,hi,hh,he⟩ := of_decide_eq_true ok
  have bj := (Rat.cast_inj (α := ℝ)).mpr hb
  have vj := (Rat.cast_inj (α := ℝ)).mpr hv
  have ij := (Rat.cast_inj (α := ℝ)).mpr hi
  have hj := (Rat.cast_inj (α := ℝ)).mpr hh
  have ej := (Rat.cast_inj (α := ℝ)).mpr he
  push_cast at bj vj ij hj ej
  have id : (next m).eval s = q.eval t + (m.b:ℝ)*d + (m.d:ℝ)*w +
      (m.e:ℝ)*((r0-r)*u) := by
    simp only [next, Coeff.eval, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_div, ← bj, ← vj, ← ij, ← hj]
    linear_combination - (m.a:ℝ)*f.bga - (m.b:ℝ)*f.core - (m.c:ℝ)*f.plane -
      (m.d:ℝ)*f.mlcc - (m.e:ℝ)*f.void + u*ej
  have load : (m.b:ℝ)*d ≤ max ((m.b:ℝ)/10) (6/5*m.b) := by
    rcases le_total 0 (m.b:ℝ) with hp | hn
    · exact (mul_le_mul_of_nonneg_left dhi hp).trans (by rw [mul_comm]; exact le_max_right ..)
    · apply (mul_le_mul_of_nonpos_left dlo hn).trans
      convert le_max_left ((m.b:ℝ)/10) (6/5*m.b) using 1; ring
  have ml := (le_abs_self ((m.d:ℝ)*w)).trans_eq (abs_mul ..)
  have lead := mul_le_mul_of_nonneg_left wbox (abs_nonneg (m.d:ℝ))
  have er : |(r0-r)*u| ≤ 1/400 := by
    rw [abs_mul, abs_sub_comm]
    linarith [mul_le_mul rbox ubox (abs_nonneg u) (by norm_num)]
  have eh := mul_le_mul_of_nonneg_left er (abs_nonneg (m.e:ℝ))
  have em := (le_abs_self ((m.e:ℝ)*((r0-r)*u))).trans_eq (abs_mul ..)
  rw [id]
  dsimp [cost]
  push_cast
  linarith only [load,ml,lead,eh,em]

private theorem sound {r0 : ℚ} {r : ℝ} (rbox : |r-r0| ≤ 1/4000)
    (s : Nat → State) (init : s 0 = ⟨0,0,1/10,0⟩)
    (steps : ∀ k < 16, ∃ u w d, Step (s k) (s (k+1)) r u w d ∧
        |u| ≤ 10 ∧ |w| ≤ 1/125 ∧ 1/10 ≤ d ∧ d ≤ 6/5)
    (n : Nat) (q : Coeff) (loss : ℚ) (ok : check r0 n q loss)
    (k : Nat) (hk : k ≤ n) (hk' : k ≤ 16) : -1/10 ≤ q.eval (s k) - loss := by
  induction n generalizing k q loss with
  | zero =>
    have : k=0 := by omega
    subst k
    have h : -1/10 ≤ q.i/10-loss := by simpa [check] using ok
    rw [init]; dsimp [Coeff.eval]
    have h' := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at h'; linarith
  | succ n ih =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at ok
    cases k with
    | zero =>
      rw [init]; dsimp [Coeff.eval]
      have h := (Rat.cast_le (K := ℝ)).mpr ok.1
      push_cast at h; linarith
    | succ k =>
      obtain ⟨u,w,d,f,hu,hw,hd,hd'⟩ := steps k (by omega)
      have step := perturbed_step f rbox hu hw hd hd' ok.2.1
      have previous :=  ih _ _ ok.2.2 k (by omega) (by omega)
      push_cast at previous; linarith

private theorem choose_center {r : ℝ} (hl : 1/1000 ≤ r) (hh : r ≤ 7/250) :
    ∃ j, |r - (center j : ℝ)| ≤ 1/4000 := by
  let x := (r-1/1000)*2000
  have hx : 0 ≤ x := by dsimp [x]; linarith
  by_cases h : 53 ≤ x
  · refine ⟨53, ?_⟩
    norm_num [center,abs_le]; dsimp [x] at h; constructor <;> linarith
  · let j : Fin 54 := ⟨⌊x⌋₊, Nat.lt_of_lt_of_le ((Nat.floor_lt hx).2 (by push_cast; linarith : x < (53:Nat))) (by decide)⟩
    refine ⟨j, ?_⟩
    have l := Nat.floor_le hx
    have u := Nat.lt_floor_add_one x
    simp [center, j, abs_le]; dsimp [x] at l u ⊢; constructor <;> linarith

private noncomputable def stampTime (k : Nat) : ℝ :=
  ([0, 1/4000000000, 1/2000000000, 7500000000000001/10000000000000000000000000, 1/1000000000, 1/800000000, 7500000000000001/5000000000000000000000000, 8750000000000001/5000000000000000000000000, 1/500000000, 22500000000000003/10000000000000000000000000, 1/400000000, 13750000000000001/5000000000000000000000000, 7500000000000001/2500000000000000000000000, 13/4000000000, 35000000000000003/10000000000000000000000000, 7500000000000001/2000000000000000000000000, 1/250000000] : List ℝ).getD k 0
private noncomputable def load (d t : ℝ) :=
  let base : ℝ := 1/(1+Real.exp (2666666666666667/1000000000000000))
  1/10+d*((1/(1+Real.exp (-((t-1/2500000000)/(3/20000000000))))-base)/(1-base))

private theorem load_bounds {d t : ℝ} (dl : 0 ≤ d) (dh : d ≤ 11/10) (ht : 0 ≤ t) :
    1/10 ≤ load d t ∧ load d t ≤ 6/5 := by
  let base : ℝ := 1/(1+Real.exp (2666666666666667/1000000000000000))
  let x := -((t-1/2500000000)/(3/20000000000))
  have baseLt : base < 1 := (div_lt_one (by positivity)).2 (by linarith [Real.exp_pos (2666666666666667/1000000000000000)])
  have h1 : base ≤ 1/(1+Real.exp x) := one_div_le_one_div_of_le (by positivity)
    (by dsimp [x]; linarith [Real.exp_le_exp.mpr (show -((t-1/2500000000)/(3/20000000000)) ≤ 2666666666666667/1000000000000000 by linarith)])
  have h2 : 1/(1+Real.exp x) ≤ 1 := (div_le_one (by positivity)).2 (by linarith [Real.exp_pos x])
  let z := (1/(1+Real.exp x)-base)/(1-base)
  have zl : 0 ≤ z := div_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr baseLt.le)
  have zh : z ≤ 1 := (div_le_one (sub_pos.mpr baseLt)).2 (by linarith)
  change 1/10 ≤ 1/10+d*z ∧ 1/10+d*z ≤ 6/5
  constructor <;> linarith [mul_nonneg dl zl,mul_le_mul_of_nonneg_left zh dl]

private noncomputable def mlccCap (v sat : ℝ) :=
  3/2000000+(11/500000)/(1+(v/sat)*(v/sat))

private theorem capDelta {v w h sat : ℝ} (hl : -3 ≤ h) (hh : h ≤ 3)
    (eqn : v = w + 1/4000000000*(h/mlccCap v sat)) : |v-w| ≤ 1/2000 := by
  have den : 0 < 1+(v/sat)*(v/sat) := by nlinarith [sq_nonneg (v/sat)]
  have hc : 3/2000000 ≤ mlccCap v sat := by dsimp [mlccCap]; linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 11/500000) den.le]
  have cp : 0 < mlccCap v sat := by linarith
  have ub : h/mlccCap v sat ≤ 2000000 := (div_le_iff₀ cp).2 (by linarith)
  have lb : -2000000 ≤ h/mlccCap v sat := (le_div_iff₀ cp).2 (by linarith)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem void_bound {s t : State} {r u w d : ℝ} (f : Step s t r u w d)
    (hr : 0 ≤ r) (b : -1/5 ≤ s.b ∧ s.b ≤ 1/10) (v : -1/2 ≤ s.v ∧ s.v ≤ 1/5)
    (i : -1/2 ≤ t.i ∧ t.i ≤ 4) (h : -3 ≤ t.h ∧ t.h ≤ 3)
    (d1 : 1/10 ≤ d) (d2 : d ≤ 6/5) : |u| ≤ 10 := by
  apply abs_le.mpr
  constructor
  · by_contra! bad
    nlinarith only [f.bga,f.core,f.void,b.1,v.2,i.1,h.1,d1,bad,mul_nonpos_of_nonneg_of_nonpos hr (by linarith : u ≤ 0)]
  · by_contra! bad
    nlinarith only [f.bga,f.core,f.void,b.2,v.1,i.2,h.2,d2,bad,mul_nonneg hr (by linarith : 0 ≤ u)]

set_option maxRecDepth 12000 in
theorem certified : Targets.Bench_11_pcb_pdn_mlcc_derating_droop_ode realTF := by
  intro r sat d st
  dsimp only
  intro box phys
  obtain ⟨⟨rl,rh⟩,_,⟨dl,dh⟩,bounds⟩ := box
  obtain ⟨init,steps⟩ := phys
  dsimp only [realTF] at rl rh dl dh bounds init steps
  push_cast at rl rh dl dh bounds init steps
  let state (k : Nat) : State := ⟨st k 0-9/10,st k 1-9/10,st k 2,st k 3⟩
  have start : state 0 = ⟨0,0,1/10,0⟩ := by
    rcases init with ⟨b,v,i,h,_⟩
    simp [state,b,v,i,h]
  have wstep (k : Nat) (hk : k < 16) : |st (k+1) 4-st k 4| ≤ 1/2000 :=
    capDelta (sat := sat) (bounds _ (by omega)).2.2.2.1.1 (bounds _ (by omega)).2.2.2.1.2 (steps k hk).2.2.2.2
  have wc (k : Nat) (hk : k ≤ 16) : |st k 4-9/10| ≤ k*(1/2000) := by
    induction k with
    | zero => simp [init.2.2.2.2]
    | succ k ih =>
      have := wstep k (by omega)
      have := ih (by omega)
      push_cast
      linarith [abs_sub_le (st (k+1) 4) (st k 4) (9/10)]
  obtain ⟨j,hj⟩ := choose_center rl rh
  have trajectory (k : Nat) (hk : k < 16) : ∃ u w d', Step (state k) (state (k+1)) r u w d' ∧
      |u| ≤ 10 ∧ |w| ≤ 1/125 ∧ 1/10 ≤ d' ∧ d' ≤ 6/5 := by
    let u := (st (k+1) 0-st (k+1) 1)/r
    let d' := load d (stampTime (k+1))
    have time_pos (i : Fin 17) : 0 ≤ stampTime i := by fin_cases i <;> norm_num [stampTime,List.getD]
    obtain ⟨ld,ld'⟩ := load_bounds (by linarith only [dl] : 0 ≤ d) dh (time_pos ⟨k+1,by omega⟩)
    obtain ⟨be,ve,ie,he,_⟩ := steps k hk
    change st (k+1) 0 = st k 0+1/4000000000*((st (k+1) 2-u)/(1/125000000)) at be
    change st (k+1) 1 = st k 1+1/4000000000*((u-st (k+1) 3-d')/(3/1000000000)) at ve
    change st (k+1) 2 = st k 2+1/4000000000*((9/10-st (k+1) 0-1/500*st (k+1) 2)/(11/50000000000)) at ie
    change st (k+1) 3 = st k 3+1/4000000000*((st (k+1) 1-st (k+1) 4-3/1000*st (k+1) 3)/(7/50000000000)) at he
    have f : Step (state k) (state (k+1)) r u (st (k+1) 4-9/10) d' := by
      constructor
      · dsimp [state]; linarith only [be]
      · dsimp [state]; linarith only [ve]
      · dsimp [state]; linarith only [ie]
      · dsimp [state]; linarith only [he]
      · dsimp [state,u]; field_simp [show r ≠ 0 by linarith]; ring
    have bp := bounds k (by omega)
    have bn := bounds (k+1) (by omega)
    refine ⟨u,_,d',f,void_bound f (by linarith) ?_ ?_ bn.2.2.1 bn.2.2.2.1 ld ld',?_,ld,ld'⟩
    · change -1/5 ≤ st k 0-9/10 ∧ _
      constructor <;> (try dsimp [state]) <;> linarith [bp.1.1,bp.1.2]
    · change -1/2 ≤ st k 1-9/10 ∧ _
      constructor <;> (try dsimp [state]) <;> linarith [bp.2.1.1,bp.2.1.2]
    · have := wc (k+1) (by omega)
      have lim : ((k+1:Nat):ℝ) ≤ 16 := by exact_mod_cast (show k+1 ≤ 16 by omega)
      linarith
  rintro ⟨k,hk,bad⟩
  have h := sound hj state start trajectory 16 core 0 (replay j) k hk hk
  dsimp [core,Coeff.eval,state] at h
  norm_num at h
  change st k 1 < 4/5 at bad
  linarith

end SpiceSmtBench.PdnCertificate
