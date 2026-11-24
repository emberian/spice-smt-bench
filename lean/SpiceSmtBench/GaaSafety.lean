import SpiceSmtBench.RealPhysics
import SpiceSmtBench.TargetsGenerated
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace SpiceSmtBench.GaaSafety

-- A supersolution of the four electrostatic rows, valid at every
-- temperature because all the mobile and fixed charge on the RHS is positive.
private theorem source_potential {p q u v lam sep : ℝ} (lh : 0 < lam) (lmax : lam ≤ 7/2)
    (sh : 12 ≤ sep)
    (a : 0 ≤ ((13/25)+q-2*p)/(144/25)+(((51/100)-p)/lam+(9/50)*((13/25)-p)/sep))
    (b : 0 ≤ (p+u-2*q)/(144/25)+((51/100)-q)/lam)
    (c : 0 ≤ (q+v-2*u)/(144/25)+((51/100)-u)/lam)
    (d : 0 ≤ (u+(117/100)-2*v)/(144/25)+(((51/100)-v)/lam+(9/50)*((117/100)-v)/sep)) : p ≤ (107/200) := by
  have gate {w x : ℝ} (hw : (51/100) ≤ w) (hx : w ≤ x) :
      ((51/100)-x)/lam ≤ ((51/100)-w)/(7/2) := (div_le_iff₀ lh).2 (by
    nlinarith only [hx,mul_le_mul_of_nonpos_left lmax (sub_nonpos.mpr hw)])
  by_contra! hp
  have left : (9/50)*((13/25)-p)/sep ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hq : p-(107/200) < q-(11/20) := by nlinarith only [a, left,gate (by norm_num) hp.le,hp]
  have qh : (11/20) < q := by linarith
  have hu : q-(11/20) < u-(3/5) := by nlinarith only [b, gate (by norm_num) qh.le,hq]
  have uh : (3/5) < u := by linarith
  have hv : u-(3/5) < v-(3/4) := by nlinarith only [c,gate (by norm_num) uh.le,hu]
  have vh : (3/4) < v := by linarith
  have right : (9/50)*((117/100)-v)/sep ≤ (9/50)*((117/100)-(3/4))/12 :=
    (div_le_iff₀ (by linarith)).2 (by linarith)
  nlinarith only [d,right,gate (by norm_num) vh.le,hv,vh]

/-- The SG weight is positive and its reverse coefficient is no larger
than max(1, exp z), including the removable singularity. -/
private theorem reverse_weight {b z : ℝ} (eqn : b*(Real.exp z-1)=z) (atZero : z=0 → b=1) :
    0 ≤ b ∧ b*Real.exp z ≤ max 1 (Real.exp z) := by
  rcases lt_trichotomy z 0 with neg | zero | pos
  · have hE := Real.exp_lt_one_iff.mpr neg
    have hp : 0 ≤ b := by
      by_contra! bad
      nlinarith only [eqn,neg,mul_pos_of_neg_of_neg bad (sub_neg.mpr hE)]
    have aux := Real.add_one_le_exp (-z)
    rw [Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos _)] at aux
    constructor
    · exact hp
    · apply le_trans _ (le_max_left ..)
      by_contra! bad
      nlinarith only [mul_pos (sub_pos.mpr bad) (sub_pos.mpr hE),
        congrArg (fun t => t*Real.exp z) eqn,aux]
  · subst z; simp [atZero rfl]
  · have hE := Real.one_lt_exp_iff.mpr pos
    have hb : b = z/(Real.exp z-1) := (eq_div_iff (sub_pos.mpr hE).ne').2 eqn
    have upper : b ≤ 1 := hb ▸ (div_le_one (sub_pos.mpr hE)).2 (by linarith [Real.add_one_le_exp z])
    exact ⟨hb ▸ div_nonneg pos.le (sub_pos.mpr hE).le,
      (mul_le_mul_of_nonneg_right upper (Real.exp_pos _).le).trans
        (by simp)⟩

private noncomputable abbrev kb : ℝ := 4308666631/50000000000000
private noncomputable abbrev activation (t : ℝ) := (6498530148177529/1000000000000)*
  (6666666666666667/2000000000000000000-1/t)

private theorem emission {t e : ℝ} (hot : 410 < t) (hq : 3/100 ≤ e) :
    let x := activation t + ((107/200)-e)/(kb*t)
    (t ≤ 500 → Real.exp x ≤ 1400000000) ∧ Real.exp x ≤ 3700000000 := by
  let x := activation t + ((107/200)-e)/(kb*t)
  have ht : 0 < t := by linarith
  have thermal : ((107/200)-e)/(kb*t) ≤ 6000/t := by
    rw [← div_div]; exact div_le_div_of_nonneg_right ((div_le_iff₀ (by norm_num [kb])).2 (by norm_num [kb]; linarith)) ht.le
  have norm : x*t ≤ (217/10)*t-490 := by
    have tr := (le_div_iff₀ ht).mp thermal
    dsimp [x,activation]
    field_simp [ht.ne',show kb ≠ 0 by norm_num [kb]] at tr ⊢
    nlinarith only [tr,ht]
  have expMajor (n : Nat) (hn : x ≤ n) : Real.exp x ≤ ((68/25):ℝ)^n := by
    calc
      _ ≤ Real.exp (n*1) := Real.exp_le_exp.mpr (by simpa using hn)
      _ = Real.exp 1 ^ n := Real.exp_nat_mul 1 n
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) _
  constructor
  · intro h
    have bound : x ≤ 21 := by
      by_contra! bad
      nlinarith only [norm,h,mul_pos (sub_pos.mpr bad) ht]
    exact (expMajor 21 (by simpa using bound)).trans (by norm_num)
  · have bound : x ≤ 22 := by
      by_contra! bad
      nlinarith only [norm,ht,mul_pos (sub_pos.mpr bad) ht]
    exact (expMajor 22 (by simpa using bound)).trans (by norm_num)

set_option maxRecDepth 32000 in
theorem certified : Targets.Bench_14a_gt2n_gaa_nanosheet_electrothermal_unsat realTF := by
  intro tn dl amb r t root p f1 q f2 u f3 v f4 e0 b0 e1 b1 e2 b2 e3 b3 e4 b4 cur box phys hot
  simp only [and_assoc] at phys
  obtain ⟨ht,hs,hsq,h1,h2,h3,h4,_,he0,hb0,bl,bu,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,
    j1,j2,j3,j4,drain,heat⟩ := phys
  obtain ⟨⟨tnl,tnh⟩,⟨dll,_⟩,⟨_,ambh⟩,⟨rl,rh⟩,_⟩ := box
  have source := drain.trans (j4.trans (j3.trans (j2.trans j1)))
  dsimp only [realTF] at ht hs hsq h1 h2 h3 h4 he0 hb0 bl bu heat hot source tnl tnh dll ambh rl rh
  push_cast at ht hs hsq h1 h2 h3 h4 he0 hb0 bl bu heat hot source tnl tnh dll ambh rl rh
  have hspos : 0 < root := by nlinarith only [hot,hsq,hs]
  have posRhs {x y : ℝ} (h : x = y) (p : 0 ≤ y) : 0 ≤ x := h.symm ▸ p
  have hp : p ≤ (107/200) := source_potential (p := p) (q := q) (u := u) (v := v)
    (lam := 3/4*((5+tn)*(17/20))) (sep := (11/2+dl)*(12/5))
    (by nlinarith only [tnl]) (by linarith only [tnh]) (by linarith only [dll])
    (posRhs h1 (by positivity)) (posRhs h2 (by positivity))
    (posRhs h3 (by positivity)) (posRhs h4 (by positivity))
  let z := (p-13/25)/(kb*t)
  let shift := (2293/2500)/((5+tn)*(5+tn))
  let arg := (13/25-shift)/(kb*t)
  let endArg := (p-shift-f1)/(kb*t)
  let sourceFlux := b0*Real.exp z*Real.exp arg-b0*Real.exp endArg
  change e0 = Real.exp z at he0
  subst e0
  change b0*(Real.exp z-1)=z at hb0
  have neutral : z=0 → b0=1 := by
    change 1-z/2+z*z/12-(z*z)*(z*z)/720 ≤ b0 at bl
    change b0 ≤ 1-z/2+z*z/12 at bu
    intro h; rw [h] at bl bu; linarith only [bl,bu]
  obtain ⟨bpos,limit⟩ := reverse_weight hb0 neutral
  have hkt : 0 < kb*t := mul_pos (by norm_num [kb]) ht
  have fluxBound : sourceFlux ≤ Real.exp (((107/200)-shift)/(kb*t)) := by
    have bound := mul_le_mul_of_nonneg_right limit (Real.exp_pos arg).le
    dsimp [sourceFlux]
    rw [max_mul_of_nonneg _ _ (Real.exp_pos arg).le, one_mul,← Real.exp_add] at bound
    apply (sub_le_self _ (mul_nonneg bpos (Real.exp_pos _).le)).trans (bound.trans _)
    apply max_le <;> apply Real.exp_le_exp.mpr
    · exact div_le_div_of_nonneg_right (by linarith only) hkt.le
    · dsimp [z,arg]; rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith only [hp]) hkt.le
  have thick : 0 < 5+tn := by linarith
  have shiftLo : 3/100 ≤ shift := (le_div_iff₀ (mul_pos thick thick)).2 (by
    nlinarith only [mul_self_le_mul_self thick.le (by linarith only [tnh] : 5+tn ≤ (107/20))])
  let K : ℝ := (801088317/50000000000000000000000000000)*10000000000*300*3*18*(5+tn)*kb/(12/5)
  have kp : 0 ≤ K := by dsimp [K,kb]; positivity
  have kh : K ≤ 5/10000000000 := by dsimp [K,kb]; linarith only [tnh]
  have dosPos : 0 < (t/300)*root := by positivity
  change cur = ((801088317/50000000000000000000000000000)*
    ((10000000000*((t/300*root)*Real.exp (activation t)))*(300/(t/300*root))))*
    ((3*(18*(5+tn)))*((kb*t)*sourceFlux))/(12/5) at source
  have id : cur = K*t*(Real.exp (activation t)*sourceFlux) := by
    rw [source]; dsimp [K]; field_simp [dosPos.ne',ht.ne',hspos.ne']
  have hcur : cur ≤ K*t*Real.exp (activation t + ((107/200)-shift)/(kb*t)) := by
    rw [id,Real.exp_add]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left fluxBound (Real.exp_pos _).le) (mul_nonneg kp ht.le)
  have maxI (n : ℝ) (hn : 0 ≤ n) (h : Real.exp (activation t + ((107/200)-shift)/(kb*t)) ≤ n) :
      cur ≤ 5/10000000000*t*n := hcur.trans
    (mul_le_mul (mul_le_mul_of_nonneg_right kh ht.le) h (Real.exp_pos _).le (by positivity))
  have rpos : 0 ≤ r := by linarith
  have nonneg : 0 ≤ cur := by
    by_contra! neg
    nlinarith only [heat,ambh,hot,mul_nonpos_of_nonneg_of_nonpos rpos neg.le]
  have heatBound := mul_le_mul_of_nonneg_right rh nonneg
  have both := emission hot shiftLo
  rcases le_total t 500 with small | large
  · linarith only [maxI _ (by norm_num) (both.1 small),heat,heatBound,hot,ambh]
  · linarith only [maxI _ (by norm_num) both.2,heat,heatBound,large,ambh]

end SpiceSmtBench.GaaSafety
