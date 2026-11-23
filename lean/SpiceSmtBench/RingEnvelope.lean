import SpiceSmtBench.BoxCertificate

namespace SpiceSmtBench.RingEnvelope

open LeanCert.Core IntervalRat IntervalCheck BoxCertificate

abbrev I := IntervalRat
noncomputable def sp (x : ℝ) := Real.log (1+Real.exp x)

private theorem sp_mono : Monotone sp := fun _ _ h => Real.log_le_log (by positivity)
  (add_le_add_right (Real.exp_le_exp.mpr h) 1)
private theorem sp_nonneg (x : ℝ) : 0 ≤ sp x := Real.log_nonneg (by linarith [Real.exp_pos x])
private theorem sp_sym (x : ℝ) : sp x = max x 0 + sp (-|x|) := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h,abs_of_nonneg h]
    apply Real.exp_injective
    rw [Real.exp_add,sp,sp,Real.exp_log (by positivity),Real.exp_log (by positivity),
      Real.exp_neg,mul_add,mul_one,mul_inv_cancel₀ (Real.exp_pos _).ne',add_comm]
  · rw [max_eq_right h,abs_of_nonpos h,neg_neg,zero_add]

private def corr (q : ℚ) : ℚ :=
  if 4 ≤ |q| then 1/50 else if 2 ≤ |q| then 13/100 else if 1 ≤ |q| then 8/25 else 7/10
private theorem corr_pos (q : ℚ) : 0 ≤ corr q := by unfold corr; split_ifs <;> norm_num

private def lit (q : ℚ) : PExpr := .const ⟨q.num,q.den,q.den_pos⟩
private theorem lit_eval (q : ℚ) (ρ : Nat → ℝ) : (lit q).eval realTF ρ = (q:ℝ) := by
  simp [lit,PExpr.eval,QRat.eval,realTF,Rat.cast_def]
private theorem endpoint (q c : ℚ)
    (ok : checkPositive (n := 0) (fun _ => .singleton 0) (.sub (lit c) (.softplus (lit q))) false) :
    sp q ≤ c := by
  have h := positive_of_check _ _ false (x := Fin.elim0) (fun i => Fin.elim0 i) ok
  change 0 ≤ (lit c).eval realTF _ - sp ((lit q).eval realTF _) at h
  simpa only [lit_eval,sub_nonneg] using h

private theorem sp_corr (q : ℚ) : sp (-|(q:ℝ)|) ≤ (corr q : ℝ) := by
  unfold corr
  split_ifs with h4 h2 h1
  · exact (sp_mono (show -|(q:ℝ)| ≤ ((-4:ℚ):ℝ) by exact_mod_cast neg_le_neg h4)).trans
      (endpoint (-4) (1/50) (by decide +kernel))
  · exact (sp_mono (show -|(q:ℝ)| ≤ ((-2:ℚ):ℝ) by exact_mod_cast neg_le_neg h2)).trans
      (endpoint (-2) (13/100) (by decide +kernel))
  · exact (sp_mono (show -|(q:ℝ)| ≤ ((-1:ℚ):ℝ) by exact_mod_cast neg_le_neg h1)).trans
      (endpoint (-1) (8/25) (by decide +kernel))
  · exact (sp_mono (show -|(q:ℝ)| ≤ ((0:ℚ):ℝ) by simp)).trans
      (endpoint 0 (7/10) (by decide +kernel))

private def spBox (a : I) : I :=
  ⟨max a.lo 0,max a.hi 0+corr a.hi,
    (max_le_max_right 0 a.le).trans (le_add_of_nonneg_right (corr_pos _))⟩
private theorem mem_sp {x : ℝ} {a : I} (h : x ∈ a) : sp x ∈ spBox a := by
  rw [mem_def]; dsimp only [spBox]
  push_cast
  constructor
  · apply le_trans _ (sp_mono h.1); rw [sp_sym]; exact le_add_of_nonneg_right (sp_nonneg _)
  · apply (sp_mono h.2).trans; rw [sp_sym]; exact add_le_add_right (sp_corr _) _

private def unionBox (a b : I) : I :=
  ⟨min a.lo b.lo,max a.hi b.hi,(min_le_left ..).trans (a.le.trans (le_max_left ..))⟩
private theorem mem_union {x : ℝ} {a b : I} (h : x ∈ a ∨ x ∈ b) : x ∈ unionBox a b := by
  change (↑(min a.lo b.lo):ℝ) ≤ x ∧ x ≤ ↑(max a.hi b.hi)
  push_cast; rcases h with h|h
  · exact ⟨(min_le_left ..).trans h.1,h.2.trans (le_max_left ..)⟩
  · exact ⟨(min_le_right ..).trans h.1,h.2.trans (le_max_right ..)⟩

private def pieces (f : I → I) : Nat → I → I
  | 0, a => f a
  | k+1, a => unionBox (pieces f k a.bisect.1) (pieces f k a.bisect.2)
private theorem mem_pieces {f : I → I} {g : ℝ → ℝ} (sound : ∀ {x a}, x ∈ a → g x ∈ f a)
    (k : Nat) {a : I} {x : ℝ} (hx : x ∈ a) : g x ∈ pieces f k a := by
  induction k generalizing a with
  | zero => exact sound hx
  | succ k ih => exact mem_union ((mem_bisect_or hx).imp ih ih)

private def diffBox (d a : I) : I :=
  let f := spBox a
  let r := spBox (a.sub d)
  (f.mul f).sub (r.mul r)
private theorem mem_diff {d a : I} {v x : ℝ} (hd : v ∈ d) (ha : x ∈ a) :
    sp x*sp x-sp (x-v)*sp (x-v) ∈ diffBox d a :=
  mem_sub (mem_mul (mem_sp ha) (mem_sp ha))
    (mem_mul (mem_sp (mem_sub ha hd)) (mem_sp (mem_sub ha hd)))

private def reduction (a : I) : I :=
  let f := spBox a
  ⟨1/(1+f.hi/10),1/(1+f.lo/10),by
    have h : 0 ≤ f.lo := le_max_right .. 
    exact one_div_le_one_div_of_le (by positivity) (by linarith only [f.le])⟩
private theorem mem_reduction {a : I} {x : ℝ} (hx : x ∈ a) : 1/(1+sp x/10) ∈ reduction a := by
  have h := mem_sp hx
  have hl : 0 ≤ ((spBox a).lo:ℝ) := by exact_mod_cast (le_max_right a.lo 0)
  rw [mem_def]; dsimp only [reduction]
  push_cast
  exact ⟨one_div_le_one_div_of_le (by linarith only [sp_nonneg x]) (by linarith only [h.2]),
    one_div_le_one_div_of_le (by linarith only [hl]) (by linarith only [h.1])⟩

noncomputable def channel (k threshold dibl d g : ℝ) :=
  let a := k*(g-(threshold-dibl*d))/(6463/125000)
  (sp a*sp a-sp (a-d/(6463/125000))*sp (a-d/(6463/125000)))/(1+sp a/10)

def thresholdBox (pmos : Bool) : I :=
  if pmos then ⟨234/1000,246/1000,by decide +kernel⟩ else ⟨224/1000,236/1000,by decide +kernel⟩
def diblBox : I := ⟨87/1000,111/1000,by decide +kernel⟩
def slope (pmos : Bool) : ℚ := if pmos then 9/10 else 91/100
private def chanBox (pmos : Bool) (d g : I) : I :=
  let a := ((g.add (diblBox.mul d)).sub (thresholdBox pmos)).scale (slope pmos)
  let a := a.scale (125000/6463)
  (pieces (diffBox (d.scale (125000/6463))) 3 a).mul (reduction a)

private theorem mem_chan {d g : ℝ} {D G : I} (p : Bool) {v b : ℝ}
    (hd : d ∈ D) (hg : g ∈ G) (ht : v ∈ thresholdBox p) (hb : b ∈ diblBox) :
    channel (slope p) v b d g ∈ chanBox p D G := by
  let x := (slope p:ℝ)*(g-(v-b*d))/(6463/125000)
  have ha := mem_scale (125000/6463) (mem_scale (slope p) (mem_sub (mem_add hg (mem_mul hb hd)) ht))
  have hv := mem_scale (125000/6463) hd
  push_cast at ha hv
  rw [show (125000/6463:ℝ)*((slope p:ℝ)*(g+b*d-v)) = x by dsimp [x]; ring] at ha
  rw [show (125000/6463:ℝ)*d = d/(6463/125000) by ring] at hv
  have m := mem_pieces (fun h => mem_diff hv h) 3 ha
  simpa only [chanBox,channel,x,div_eq_mul_inv,one_mul] using mem_mul m (mem_reduction ha)

structure Process where
  pn : ℝ
  pp : ℝ
  bn : ℝ
  bp : ℝ
  geometry : ℝ
  diagonal : ℝ
  coupling : ℝ

def sizeBox : I := ⟨1135/100,1165/100,by decide +kernel⟩
def diagBox : I := ⟨471/1000,487/1000,by decide +kernel⟩
def crossBox : I := ⟨21/1000,26/1000,by decide +kernel⟩

structure Admissible (p : Process) : Prop where
  nThreshold : p.pn ∈ thresholdBox false
  pThreshold : p.pp ∈ thresholdBox true
  nDibl : p.bn ∈ diblBox
  pDibl : p.bp ∈ diblBox
  geometry : p.geometry ∈ sizeBox
  diagonal : p.diagonal ∈ diagBox
  coupling : p.coupling ∈ crossBox

noncomputable def net (p : Process) (d g v : ℝ) :=
  (22/100)*channel (9/10) p.pp p.bp (v-d) (v-g) -
    (25/100)*channel (91/100) p.pn p.bn d g

private def netBox (d g v : I) : I :=
  ((chanBox true (v.sub d) (v.sub g)).scale (22/100)).sub ((chanBox false d g).scale (25/100))
private theorem mem_net {p : Process} (hp : Admissible p) {d g v : ℝ} {D G V : I}
    (hd : d ∈ D) (hg : g ∈ G) (hv : v ∈ V) : net p d g v ∈ netBox D G V := by
  have h := mem_sub (mem_scale (22/100) (mem_chan true (mem_sub hv hd) (mem_sub hv hg) hp.pThreshold hp.pDibl))
    (mem_scale (25/100) (mem_chan false hd hg hp.nThreshold hp.nDibl))
  simpa only [netBox,net,slope,Bool.false_eq_true,↓reduceIte,Rat.cast_div,Rat.cast_ofNat] using h

/-- Half of a trapezoidal increment, in volts. Capacitance is in fF and current in µA. -/
noncomputable def halfStep (p : Process) (x y z v : ℝ) :=
  (1/2000)*(p.geometry*(p.diagonal*net p x z v+p.coupling*(net p y x v+net p z y v)))

private def incBox (x y z v : I) := (sizeBox.mul ((diagBox.mul (netBox x z v)).add
  (crossBox.mul ((netBox y x v).add (netBox z y v))))).scale (1/2000)
private theorem mem_inc {p : Process} (hp : Admissible p) {x y z v : ℝ} {X Y Z V : I}
    (hx : x ∈ X) (hy : y ∈ Y) (hz : z ∈ Z) (hv : v ∈ V) : halfStep p x y z v ∈ incBox X Y Z V := by
  simpa only [incBox,halfStep,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
    mem_scale (1/2000) (mem_mul hp.geometry (mem_add (mem_mul hp.diagonal (mem_net hp hx hz hv))
      (mem_mul hp.coupling (mem_add (mem_net hp hy hx hv) (mem_net hp hz hy hv)))))

private def distance (a : I) (r : ℚ) := max (max (r-a.hi) (a.lo-r)) 0
private theorem distance_le {x : ℝ} {a : I} (hx : x ∈ a) (r : ℚ) :
    (distance a r : ℝ) ≤ |x-r| := by
  unfold distance; push_cast
  exact max_le (max_le (by linarith only [hx.2,neg_le_abs (x-r)])
    (by linarith only [hx.1,le_abs_self (x-r)])) (abs_nonneg _)

inductive Partition
  | leaf
  | split (axis : Fin 4) (left right : Partition)

def check (box : Fin 4 → I) : Partition → Bool
  | .leaf =>
    let a := incBox (box 0) (box 1) (box 2) (box 3)
    decide (-distance (box 0) (-2/25) < a.lo ∧ a.hi < distance (box 0) (83/100))
  | .split i l r => check (Function.update box i (box i).bisect.1) l &&
      check (Function.update box i (box i).bisect.2) r
termination_by structural tree => tree

theorem checked {p : Process} (hp : Admissible p) (s : Fin 4 → ℝ)
    (tree : Partition) (box : Fin 4 → I) (hs : ∀ i, s i ∈ box i) (ok : check box tree) :
    let inc := halfStep p (s 0) (s 1) (s 2) (s 3);
    -abs (s 0-(-2/25)) < inc ∧ inc < abs (s 0-83/100) := by
  induction tree generalizing box with
  | leaf =>
    rw [check] at ok
    have limits := of_decide_eq_true ok
    have d := mem_inc hp (hs 0) (hs 1) (hs 2) (hs 3)
    have l := (Rat.cast_lt (K := ℝ)).mpr limits.1
    have h := (Rat.cast_lt (K := ℝ)).mpr limits.2
    push_cast only [Rat.cast_neg] at l
    have dl := distance_le (hs 0) (-2/25)
    have dh := distance_le (hs 0) (83/100)
    push_cast only [Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat] at dl dh
    exact ⟨(neg_le_neg dl).trans_lt (l.trans_le d.1), (d.2.trans_lt h).trans_le dh⟩
  | split i l r il ir =>
    simp only [check,Bool.and_eq_true] at ok
    rcases mem_bisect_or (hs i) with left|right
    · apply il _ _ ok.1; intro j; by_cases e : j=i <;> simp_all [Function.update]
    · apply ir _ _ ok.2; intro j; by_cases e : j=i <;> simp_all [Function.update]

def nodeBox : I := ⟨-1/5,9/10,by decide +kernel⟩
def supplyBox : I := ⟨31/50,17/25,by decide +kernel⟩
def whole : Fin 4 → I := ![nodeBox,nodeBox,nodeBox,supplyBox]

end SpiceSmtBench.RingEnvelope
