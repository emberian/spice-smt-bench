import Mathlib.Analysis.Complex.ExponentialBounds
import SpiceSmtBench.BoxCertificate
import SpiceSmtBench.TargetsGenerated

namespace SpiceSmtBench.GanCertificate
open IntervalCheck BoxCertificate

private noncomputable def sp (x : ℝ) := Real.log (1 + Real.exp x)

private theorem sp_nn (z : ℝ) : 0 ≤ sp z :=
  Real.log_nonneg (by linarith [Real.exp_pos z])

private theorem sp_le {z a : ℝ} (ha : 0 ≤ a) (hz : z ≤ a) : sp z ≤ a+1 := by
  apply Real.exp_le_exp.mp
  rw [sp, Real.exp_log (by positivity), Real.exp_add]
  have h := Real.exp_le_exp.mpr hz
  have h' := Real.exp_le_exp.mpr ha
  rw [Real.exp_zero] at h'
  nlinarith only [h,h',mul_le_mul_of_nonneg_left Real.exp_one_gt_two.le (Real.exp_pos a).le]

private noncomputable def forward (g vt : ℝ) := sp ((41/50*(g-29/20))/(2*vt))
private noncomputable def reverseGate (g s vt : ℝ) := sp ((41/50*(g-29/20)-s)/(2*vt))
private noncomputable def current (g s vt : ℝ) :=
  (1/250 / (1+3/25*forward g vt)) *
  (forward g vt * forward g vt - reverseGate g s vt * reverseGate g s vt)

private theorem current_bounds {g s vt : ℝ} (hvt : 1/40 ≤ vt) (hg : g ≤ 3) :
    current g s vt ≤ 3 ∧ (0 ≤ s → 0 ≤ current g s vt) ∧
    (g ≤ 6/5 → current g s vt ≤ 1/250) := by
  let a := forward g vt
  let b := reverseGate g s vt
  have ha : 0 ≤ a := sp_nn _
  have hb : 0 ≤ b := sp_nn _
  have hd : 0 < 2*vt := by linarith
  have scale : 0 ≤ (1/250 : ℝ) / (1+3/25*a) := by positivity
  have scale' : (1/250 : ℝ) / (1+3/25*a) ≤ 1/250 :=
    (div_le_iff₀ (by positivity)).2 (by linarith)
  have hh : a ≤ 27 := by
    change sp _ ≤ 27
    have z : 41/50*(g-29/20)/(2*vt) ≤ 26 := (div_le_iff₀ hd).2 (by linarith)
    linarith [sp_le (by norm_num : (0:ℝ) ≤ 26) z]
  have bound {v : ℝ} (hv : a*a ≤ v) : current g s vt ≤ 1/250*v :=
    (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg b] : a*a-b*b ≤ v) scale).trans
      (mul_le_mul_of_nonneg_right scale' ((mul_nonneg ha ha).trans hv))
  constructor
  · linarith [bound (mul_self_le_mul_self ha hh)]
  constructor
  · intro hs
    have hba : b ≤ a := Real.log_le_log (by positivity) (add_le_add_right
      (Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right hd).2 (by linarith))) _)
    exact mul_nonneg scale (sub_nonneg.mpr (mul_self_le_mul_self hb hba))
  · intro small
    have ha' : a ≤ 1 := by
      have z : (41/50*(g-29/20))/(2*vt) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
      change sp _ ≤ 1
      simpa using sp_le (by norm_num : (0:ℝ) ≤ 0) z
    linarith [bound (mul_self_le_mul_self ha ha')]

private noncomputable def cap (cgd g s : ℝ) :=
  7/2000000000000 + cgd/Real.sqrt (1+((s-g)/8)*((s-g)/8))

-- c is measured in pF. The second bound retains depletion feedback as the
-- switching node rises. It follows from sqrt(1+x²) ≥ x for every real x.
private theorem cap_bounds {cgd g s : ℝ} (hl : 0 ≤ cgd) (hh : cgd ≤ 3/62500000000) :
    let c := 10^12*cap cgd g s
    0 ≤ c ∧ c ≤ 52 ∧ (s-g)*(c-7/2) ≤ 384 ∧ 0 ≤ c-7/2 := by
  let u := (s-g)/8
  let d := Real.sqrt (1+u*u)
  have hsq : d*d = 1+u*u := Real.mul_self_sqrt (by nlinarith [sq_nonneg u])
  have hn : 0 ≤ d := Real.sqrt_nonneg _
  have hd : 1 ≤ d := by nlinarith [sq_nonneg u]
  have hu : u ≤ d := by nlinarith
  have he : (cgd/d)*d = cgd := div_mul_cancel₀ _ (by linarith)
  have hp : 0 ≤ cgd/d := div_nonneg hl hn
  have h1 := mul_le_mul_of_nonneg_left hd hp
  have h2 := mul_le_mul_of_nonneg_left hu hp
  change 0 ≤ 10^12*(7/2000000000000+cgd/d) ∧ _
  change _ ∧ 10^12*(7/2000000000000+cgd/d) ≤ 52 ∧
    (s-g)*(10^12*(7/2000000000000+cgd/d)-7/2) ≤ 384 ∧ 0 ≤ 10^12*(7/2000000000000+cgd/d)-7/2
  dsimp [u] at h2
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [hh,h1,h2,he,hp]

private noncomputable def drive (t : ℝ) :=
  let base : ℝ := 1/(1+Real.exp (2142857142857143/1250000000000000))
  48*((1/(1+Real.exp (-((t-3/5000000000)/(7/20000000000))))-base)/(1-base))

private structure Step (oldG oldS g s c p d i : ℝ) : Prop where
  gate : (680+c)*(g-oldG)+p*g = c*(s-oldS)
  drain : (120+c)*(s-oldS)+500*(s-d)+250*i = c*(g-oldG)

-- Multiply the two stamped inverse-capacitance rows by their common
-- determinant to recover charge balance before interval evaluation.
private theorem balance {oldG oldS g s C r d i : ℝ} (hc : 0 ≤ C)
    (gate : g = oldG + 1/4000000000 *
      (((3/25000000000+C)*(-(g/r))+C*((d-s)/(1/2)-i)) /
       (51/625000000000000000000+C*(1/1250000000))))
    (drain : s = oldS + 1/4000000000 *
      (((17/25000000000+C)*((d-s)/(1/2)-i)+C*(-(g/r))) /
       (51/625000000000000000000+C*(1/1250000000)))) :
    Step oldG oldS g s (10^12*C) (250/r) d i := by
  let det : ℝ := 51/625000000000000000000+C*(1/1250000000)
  have pos : 0 < det := by dsimp [det]; positivity
  have hG : (g-oldG)*det = 1/4000000000*((3/25000000000+C)*(-(g/r))+C*((d-s)/(1/2)-i)) := by
    rw [← mul_div_assoc] at gate
    exact (eq_div_iff pos.ne').mp (by linarith only [gate])
  have hS : (s-oldS)*det = 1/4000000000*((17/25000000000+C)*((d-s)/(1/2)-i)+C*(-(g/r))) := by
    rw [← mul_div_assoc] at drain
    exact (eq_div_iff pos.ne').mp (by linarith only [drain])
  constructor
  · apply (mul_right_cancel₀ pos.ne')
    linear_combination (norm := (dsimp [det]; ring)) (680+10^12*C)*hG - (10^12*C)*hS
  · apply (mul_right_cancel₀ pos.ne')
    linear_combination (norm := (dsimp [det]; ring)) (120+10^12*C)*hS - (10^12*C)*hG

private theorem affine_nonneg {a b c m : ℝ} (hl : 0 ≤ a) (hr : 0 ≤ a+m*b)
    (hc : 0 ≤ c) (hm : c ≤ m) : 0 ≤ a+c*b := by
  rcases le_total 0 b with h | h
  · linarith [mul_nonneg hc h]
  · linarith [mul_le_mul_of_nonpos_right hm h]

-- Each row uses only affine endpoint checks. The capacitance and current may
-- vary with the unknown next state throughout the backward-Euler step.
private theorem advance {oldG oldS g s c p d i sl sh gh dl dh l h u m : ℝ}
    (flow : Step oldG oldS g s c p d i)
    (cpos : 0 ≤ c) (chi : c ≤ 52) (dep : (s-g)*(c-7/2) ≤ 384) (cd : 0 ≤ c-7/2)
    (pd : 500/3 ≤ p) (curr : i ≤ 3) (on : 0 ≤ s → 0 ≤ i)
    (og : -3/10 ≤ oldG) (gg : -3/10 ≤ g) (gb : g ≤ 3) (ob : oldG ≤ 3)
    (prev : sl ≤ oldS ∧ oldS ≤ sh ∧ oldG ≤ gh) (drv : dl ≤ d ∧ d ≤ dh)
    (table : 0 ≤ l ∧ 0 ≤ u ∧
      0 ≤ 120*(sl-l)+500*(dl-l)-750 ∧
      0 ≤ 120*(sl-l)+500*(dl-l)-750+52*(sl-l-33/10) ∧
      0 ≤ 120*(h-sh)+500*(h-dh) ∧
      0 ≤ 120*(h-sh)+500*(h-dh)+52*(h-sh-33/10) ∧
      (52 ≤ m ∨ (3 < l ∧ 384 ≤ (l-3)*(m-7/2))) ∧
      0 ≤ 680*(u-gh)+500/3*u ∧
      0 ≤ 680*(u-gh)+500/3*u+m*(u-gh-h+sl)) :
    l ≤ s ∧ s ≤ h ∧ g ≤ u := by
  obtain ⟨hl,hu,L0,L1,H0,H1,M,G0,G1⟩ := table
  obtain ⟨ps,ps',pg⟩ := prev
  obtain ⟨dd,dd'⟩ := drv
  have L := affine_nonneg L0 L1 cpos chi
  have H := affine_nonneg H0 H1 cpos chi
  have ls : l ≤ s := by
    by_contra! bad
    nlinarith only [flow.drain, L, curr, dd, ps, bad,
      mul_nonneg cpos (sub_nonneg.mpr ps), mul_nonneg cpos (sub_nonneg.mpr bad.le),
      mul_nonneg cpos (by linarith : 0 ≤ (g-oldG)+33/10)]
  have hs : s ≤ h := by
    by_contra! bad
    nlinarith only [flow.drain, H, on (hl.trans ls), dd', ps', bad,
      mul_nonneg cpos (sub_nonneg.mpr ps'), mul_nonneg cpos (sub_nonneg.mpr bad.le),
      mul_nonneg cpos (by linarith : 0 ≤ 33/10-(g-oldG))]
  have cm : c ≤ m := by
    rcases M with easy | ⟨pos,lim⟩
    · exact chi.trans easy
    · by_contra! bad
      nlinarith only [lim,dep,mul_pos (sub_pos.mpr pos) (sub_pos.mpr bad),
        mul_nonneg (by linarith : 0 ≤ (s-g)-(l-3)) cd]
  have G := affine_nonneg G0 G1 cpos cm
  refine ⟨ls,hs,?_⟩
  by_contra! bad
  nlinarith only [flow.gate, G, bad, pg,
    mul_nonneg cpos (sub_nonneg.mpr pg), mul_nonneg cpos (sub_nonneg.mpr bad.le),
    mul_nonneg cpos (by linarith : 0 ≤ (h-sl)-(s-oldS)),
    mul_nonneg (sub_nonneg.mpr pd) (hu.trans bad.le)]

private def times : List QRat := [⟨0,1,by decide⟩,⟨1,4000000000,by decide⟩,
  ⟨1,2000000000,by decide⟩,⟨7500000000000001,10000000000000000000000000,by decide⟩,
  ⟨1,1000000000,by decide⟩,⟨1,800000000,by decide⟩,
  ⟨7500000000000001,5000000000000000000000000,by decide⟩]

private noncomputable def stampTime (k : Nat) : ℝ :=
  ([0,1/4000000000,1/2000000000,7500000000000001/10000000000000000000000000,
    1/1000000000,1/800000000,7500000000000001/5000000000000000000000000] : List ℝ).getD k 0

private def envelope : List (ℚ × ℚ × ℚ) :=
  [(0,0,1/20),(3.5,5.4,0.36),(11.1,13.7,0.88),(20.5,23.4,1.08),
   (29.3,32.3,1.14),(36.1,38.9,1.10),(40.5,43.1,1.01)]

private def supplies : List (ℚ × ℚ) :=
  [(6.58,6.60),(15.65,15.67),(25.65,25.67),(34.30,34.32),(40.35,40.37),(43.97,43.99)]

private def capMax : List ℚ := [52,51,26,19,16,14]

private def lower (k : Nat) := (envelope.getD k 0).1
private def upper (k : Nat) := (envelope.getD k 0).2.1
private def gateMax (k : Nat) := (envelope.getD k 0).2.2

private def constQ (n : Int) (d : Nat := 1) (h : 0 < d := by decide) : PExpr :=
  .const ⟨n,d,h⟩

private def driveExpr (t : QRat) : PExpr :=
  let sigmoid (z : PExpr) := PExpr.div (constQ 1) (.add (constQ 1) (.exp z))
  let base := sigmoid (constQ 2142857142857143 1250000000000000)
  .mul (constQ 48) (.div (.sub (sigmoid (.neg (.div (.sub (.const t) (constQ 3 5000000000))
    (constQ 7 20000000000)))) base) (.sub (constQ 1) base))

private theorem supplyBounds (k : Fin 6) :
    ((supplies.getD k 0).1 : ℝ) ≤ drive (stampTime (k+1)) ∧
    drive (stampTime (k+1)) ≤ ((supplies.getD k 0).2 : ℝ) := by
  let t := times.getD (k+1) QRat.zero
  let env := fun _ : Nat => LeanCert.Core.IntervalRat.singleton 0
  have ok : (RealInterval.enclose env (driveExpr t)).any (fun v =>
      decide ((supplies.getD k 0).1 ≤ v.lo ∧ v.hi ≤ (supplies.getD k 0).2)) := by
    fin_cases k <;> decide +kernel
  cases he : RealInterval.enclose env (driveExpr t) with
  | none => simp [he] at ok
  | some v =>
    obtain ⟨hl,hh⟩ := of_decide_eq_true (by simpa only [he,Option.any_some] using ok)
    have ht : t.eval realTF = stampTime (k+1) := by
      fin_cases k <;> norm_num [t,times,stampTime,QRat.eval,realTF,List.getD]
    have h := RealInterval.enclose_sound (driveExpr t) env (fun _ => 0)
      (fun _ => by exact_mod_cast LeanCert.Core.IntervalRat.mem_singleton 0) he
    have eq : (driveExpr t).eval realTF (fun _ => 0) = drive (t.eval realTF) := by
      simp [driveExpr, drive, constQ, PExpr.eval, QRat.eval, realTF]
    rw [eq] at h
    rw [ht] at h
    exact ⟨(by exact_mod_cast hl : ((supplies.getD k 0).1 : ℝ) ≤ v.lo).trans h.1,
      h.2.trans (by exact_mod_cast hh)⟩

private theorem numeric (k : Fin 6) :
    let sl : ℝ := lower k
    let sh : ℝ := upper k
    let gh : ℝ := gateMax k
    let dl : ℝ := (supplies.getD k 0).1
    let dh : ℝ := (supplies.getD k 0).2
    let l : ℝ := lower (k+1)
    let h : ℝ := upper (k+1)
    let u : ℝ := gateMax (k+1)
    let m : ℝ := capMax.getD k 0
    0 ≤ l ∧ 0 ≤ u ∧
      0 ≤ 120*(sl-l)+500*(dl-l)-750 ∧
      0 ≤ 120*(sl-l)+500*(dl-l)-750+52*(sl-l-33/10) ∧
      0 ≤ 120*(h-sh)+500*(h-dh) ∧
      0 ≤ 120*(h-sh)+500*(h-dh)+52*(h-sh-33/10) ∧
      (52 ≤ m ∨ (3 < l ∧ 384 ≤ (l-3)*(m-7/2))) ∧
      0 ≤ 680*(u-gh)+500/3*u ∧
      0 ≤ 680*(u-gh)+500/3*u+m*(u-gh-h+sl) := by
  fin_cases k <;> norm_num [lower,upper,gateMax,envelope,supplies,capMax,List.getD]

set_option maxRecDepth 12000 in
theorem certified : Targets.Bench_07_gan_sic_halfbridge_shootthrough_soa_ode realTF := by
  intro cgd r vt st
  dsimp only
  intro box phys
  obtain ⟨c0,c1⟩ := box.1
  obtain ⟨⟨r0,r1⟩,⟨vt0,_⟩,bounds⟩ := box.2
  obtain ⟨_,init,steps⟩ := phys
  dsimp only [realTF] at c0 c1 r0 r1 vt0 bounds init
  push_cast at c0 c1 r0 r1 vt0 bounds init
  have allStates (k : Nat) (hk : k ≤ 6) :
      (lower k : ℝ) ≤ st k 1 ∧ st k 1 ≤ (upper k : ℝ) ∧ st k 0 ≤ (gateMax k : ℝ) := by
    induction k with
    | zero => norm_num [lower,upper,gateMax,envelope,List.getD,init.2]; exact init.1.2
    | succ k ih =>
      have hk' : k < 6 := by omega
      let j : Fin 6 := ⟨k,hk'⟩
      obtain ⟨hg,hs⟩ := steps k hk'
      dsimp only [realTF] at hg hs
      push_cast at hg hs
      let C := cap cgd (st (k+1) 0) (st (k+1) 1)
      obtain ⟨cp,ch,dep,cd⟩ := cap_bounds (g := st (k+1) 0) (s := st (k+1) 1)
        (by linarith only [c0] : 0 ≤ cgd) c1
      have hc : 0 ≤ C := by change 0 ≤ cap _ _ _; linarith only [cp]
      have flow := balance (d := drive (stampTime (k+1))) (i := current (st (k+1) 0) (st (k+1) 1) vt)
        (oldG := st k 0) (oldS := st k 1) (g := st (k+1) 0) (s := st (k+1) 1)
        (r := r) (C := C) hc hg hs
      have bg := (bounds (k+1) hk).1
      have bo := (bounds k (by omega)).1
      have ib := current_bounds (s := st (k+1) 1) vt0 bg.2
      have tab := numeric j
      dsimp only at tab
      apply advance (m := (capMax.getD j 0 : ℝ)) flow cp ch dep cd
        ((le_div_iff₀ (by linarith : 0 < r)).2 (by linarith)) ib.1 ib.2.1
        bo.1 bg.1 bg.2 bo.2 (ih (by omega)) (supplyBounds j)
      exact tab
  rintro ⟨k,hk,bad⟩
  obtain ⟨hsl,_,hgh⟩ := allStates k hk
  have safe (j : Fin 7) : 0 ≤ lower j ∧ gateMax j ≤ 6/5 := by fin_cases j <;> decide +kernel
  obtain ⟨sl,gh⟩ := safe ⟨k,by omega⟩
  change gateMax k ≤ (6/5 : ℚ) at gh
  have g : st k 0 ≤ 6/5 := hgh.trans (by simpa using (Rat.cast_le (K := ℝ)).mpr gh)
  have s : 0 ≤ st k 1 := (by exact_mod_cast sl : (0:ℝ) ≤ lower k).trans hsl
  have ch := (current_bounds (s := st k 1) vt0 (bounds k hk).1.2).2.2 g
  have power := (mul_le_mul_of_nonneg_right ch s).trans
    (mul_le_mul_of_nonneg_left (bounds k hk).2.2 (by norm_num))
  dsimp only [realTF] at bad
  push_cast at bad
  change st k 0 > 6/5 ∨ current (st k 0) (st k 1) vt > 1/2 ∨
    current (st k 0) (st k 1) vt * st k 1 > 20 at bad
  rcases bad with h | h | h <;> linarith

end SpiceSmtBench.GanCertificate
