import SpiceSmtBench.TargetsGenerated
import SpiceSmtBench.BoxRoot
import SpiceSmtBench.RealInterval
import SpiceSmtBench.SramCertificate

namespace SpiceSmtBench.SramTrajectory
open LeanCert.Core IntervalCheck SramCertificate RealInterval

structure Sample where
  q : I
  b : I

private def endpoint (n : Int) : ℚ := n / 1000000000000
private def band (a b : Int) (h : a ≤ b := by decide) : I :=
  ⟨endpoint a, endpoint b, by dsimp [endpoint]; gcongr⟩

/-- Rational voltage boxes at the initial sample and each of the 20 implicit steps.
Bounds are in units of 10⁻¹² V. -/
def samples : List Sample := [
  ⟨band 700000000000 700000000000, band 0 0⟩,
  ⟨band 699935792722 699935832722, band 137550431959 137550471959⟩,
  ⟨band 699209558224 699209618226, band 213786500289 213786540289⟩,
  ⟨band 696437319419 696437399421, band 260535926429 260535966429⟩,
  ⟨band 690268918283 690269018285, band 291762869716 291762909716⟩,
  ⟨band 679807766518 679807891690, band 314113707108 314113747108⟩,
  ⟨band 664485103439 664485258663, band 331003426537 331003466537⟩,
  ⟨band 643990980984 643991172250, band 344309818959 344309858959⟩,
  ⟨band 618354098770 618354312498, band 355132654872 355132694872⟩,
  ⟨band 587957361134 587957611648, band 364159669707 364159709707⟩,
  ⟨band 553397789042 553398065408, band 371854388613 371854428613⟩,
  ⟨band 515331591012 515331906994, band 378571598588 378571638588⟩,
  ⟨band 474436444039 474436788813, band 384686067119 384686107119⟩,
  ⟨band 431530911611 431531281951, band 390852926487 390852986489⟩,
  ⟨band 387712646298 387713057924, band 398495754676 398495854678⟩,
  ⟨band 343779774385 343780243261, band 410322227696 410322408772⟩,
  ⟨band 298136820824 298137445682, band 430886586514 430886955670⟩,
  ⟨band 242611490000 242612729672, band 469568191653 469569185331⟩,
  ⟨band 164968014014 164974948408, band 541813194203 541819436031⟩,
  ⟨band 111408692669 111495499857, band 611082640165 611162722473⟩,
  ⟨band 88339156573 89629444945, band 653633340229 654818943649⟩]

def sample (k : Nat) := samples.getD k ⟨.singleton 0,.singleton 0⟩

private def shift (t : ℚ) : ℚ :=
  4178112912843729/5000000000000000 * (1/(t*t)-23668639053254437/1000000000000000000)
private def asp (t : ℚ) : ℚ := (64+t)/21

-- At these geometry corners both etched natural lengths are rational. Only
-- the access transistors retain the nominal square root of 6.5 nm².
private def params : List I :=
  [ .singleton (33/100 + shift (25/4)),
    band 47985845824 47985845827, band 47985845824 47985845827,
    .singleton (13/50000000*asp (25/4)),
    .singleton (8/25 + shift (25/4)), .singleton (8/25+12/25+shift (121/25)),
    band 44986730460 44986730463, band 25371850080 25371850083,
    .singleton (3/10000000*(2*asp (25/4))), .singleton (3/10000000*(2*asp (121/25))),
    band 48809683703 48809683706, band 48809683703 48809683706 ]

def binding (q b : ℝ) (static : Nat → ℝ) : Nat → ℝ
  | 0 => q
  | 1 => b
  | i+2 => static i

def geometryBox (i : Nat) := params.getD i (.singleton 0)

private def faceEnv (s : Sample) (side high : Bool) : Nat → I
  | 0 => if side then s.q else .singleton (if high then s.q.hi else s.q.lo)
  | 1 => if !side then s.b else .singleton (if high then s.b.hi else s.b.lo)
  | i+2 => geometryBox i

def checkFace (old next : Sample) (side high : Bool) : Bool := Id.run do
  let past := if side then old.b else old.q
  let some est := enclose (faceEnv next side high) (previous side) | return false
  return if high then decide (past.hi ≤ est.lo) else decide (est.hi ≤ past.lo)


def faceCheck (k : Nat) := checkFace (sample k) (sample (k+1))

private def gateBox : I := band 2549509756796 2549509756797

private def etaExpr (n d : Nat) (hd : 0 < d := by decide) : PExpr :=
  .mul (c n d hd) (.exp (.neg (.div (c 21) (.mul (c 2) (.var 0)))))

private def contains (a b : I) : Bool := decide (a.lo ≤ b.lo ∧ b.hi ≤ a.hi)
private theorem contains_sound {a b : I} {x : ℝ} (h : contains a b) (hx : x ∈ b) : x ∈ a := by
  obtain ⟨hl,hh⟩ := of_decide_eq_true h
  exact ⟨(show (a.lo:ℝ) ≤ b.lo by exact_mod_cast hl).trans hx.1,
    hx.2.trans (by exact_mod_cast hh)⟩

private def checkEta (n d : Nat) (hd : 0 < d) (l b : I) :=
  (enclose (fun _ => l) (etaExpr n d hd)).any (contains b)
private theorem eta_sound {n d : Nat} {hd : 0 < d} {l b : I} {x : ℝ} (h : x ∈ l)
    (ok : checkEta n d hd l b) : ((n:ℝ)/d)*Real.exp (-(21/(2*x))) ∈ b := by
  unfold checkEta at ok
  cases he : enclose (fun _ => l) (etaExpr n d hd) with
  | none => simp [he] at ok
  | some a =>
    apply contains_sound (a := b) (b := a) (by simpa [he] using ok)
    simpa [etaExpr,c,PExpr.eval,realTF,QRat.eval] using
      enclose_sound _ _ (fun _ => x) (fun _ => h) he

private noncomputable def eta (k l : ℝ) := k * Real.exp (-(21/(2*l)))

noncomputable def static (i : Nat) : ℝ := ([
    ↑(33/100 + shift (25/4) : ℚ), eta (16/5) (5/2), eta (16/5) (5/2),
    ↑(13/50000000*asp (25/4) : ℚ), ↑(8/25+shift (25/4) : ℚ), ↑(8/25+12/25+shift (121/25) : ℚ),
    eta 3 (5/2), eta 3 (11/5), ↑(3/10000000*(2*asp (25/4)) : ℚ),
    ↑(3/10000000*(2*asp (121/25)) : ℚ), eta 3 (Real.sqrt (13/2)), eta 3 (Real.sqrt (13/2))] : List ℝ).getD i 0

private theorem static_mem (i : Nat) : static i ∈ geometryBox i := by
  have hgate : Real.sqrt (13/2) ∈ gateBox := by
    have hs := Real.sq_sqrt (by norm_num : 0 ≤ (13/2:ℝ))
    change ((2549509756796 / 1000000000000 : ℚ) : ℝ) ≤ _ ∧ _ ≤ ((2549509756797 / 1000000000000 : ℚ) : ℝ)
    push_cast
    constructor <;> nlinarith [Real.sqrt_nonneg (13/2)]
  have hp : eta (16/5) (5/2) ∈ geometryBox 1 :=
    eta_sound (n := 16) (d := 5) (hd := by decide)
      (l := .singleton (5/2)) (by norm_num [IntervalRat.mem_def,IntervalRat.singleton]) (by decide +kernel)
  have hn : eta 3 (5/2) ∈ geometryBox 6 := by
    simpa only [Nat.cast_ofNat, Nat.cast_one, div_one, eta] using eta_sound (n := 3) (d := 1) (hd := by decide)
      (b := geometryBox 6) (l := .singleton (5/2)) (x := 5/2)
      (by norm_num [IntervalRat.mem_def,IntervalRat.singleton]) (by decide +kernel)
  have hd : eta 3 (11/5) ∈ geometryBox 7 := by
    simpa only [Nat.cast_ofNat, Nat.cast_one, div_one, eta] using eta_sound (n := 3) (d := 1) (hd := by decide)
      (b := geometryBox 7) (l := .singleton (11/5)) (x := 11/5)
      (by norm_num [IntervalRat.mem_def,IntervalRat.singleton]) (by decide +kernel)
  have hg : eta 3 (Real.sqrt (13/2)) ∈ geometryBox 10 := by
    simpa only [Nat.cast_ofNat, Nat.cast_one, div_one, eta] using eta_sound (n := 3) (d := 1) (hd := by decide)
      (b := geometryBox 10) hgate (by decide +kernel)
  iterate 12 (rcases i with _ | i; first | exact IntervalRat.mem_singleton _ | exact hp | exact hn | exact hd | exact hg)
  exact_mod_cast IntervalRat.mem_singleton 0

private def Sample.lo (s : Sample) : ℝ × ℝ := (s.q.lo,s.b.lo)
private def Sample.hi (s : Sample) : ℝ × ℝ := (s.q.hi,s.b.hi)
def Sample.box (s : Sample) := Set.Icc s.lo s.hi
private theorem Sample.ordered (s : Sample) : s.lo ≤ s.hi :=
  ⟨by change (s.q.lo:ℝ) ≤ s.q.hi; exact_mod_cast s.q.le, by change (s.b.lo:ℝ) ≤ s.b.hi; exact_mod_cast s.b.le⟩

private noncomputable def past (side : Bool) (x : ℝ × ℝ) :=
  (previous side).eval realTF (binding x.1 x.2 static)

private theorem past_continuous (side : Bool) : Continuous (past side) := by
  have hlog (z : ℝ) : 0 ≤ Real.log (1+Real.exp z) := Real.log_nonneg (by linarith [Real.exp_pos z])
  have hden (z : ℝ) : 1 + (10:ℝ)⁻¹ * Real.log (1+Real.exp z) ≠ 0 := by
    have := hlog z; positivity
  change Continuous (fun x : ℝ × ℝ => past side x)
  cases side <;> simp only [past,previous,drive,c,PExpr.eval,binding,realTF,QRat.eval,
    Bool.false_eq_true, ↓reduceIte, Nat.cast_ofNat, Int.cast_ofNat, Int.cast_one, Nat.cast_one, div_one, one_div] <;>
    fun_prop (disch := intros; first | exact hden _ | positivity)

private def pick (s : Sample) (side : Bool) := if side then s.b else s.q
private def coord (x : ℝ × ℝ) (side : Bool) := if side then x.2 else x.1

private theorem onFace {s : Sample} {x : ℝ × ℝ} (hx : x ∈ s.box) (side high : Bool)
    (hf : coord x side = ((if high then (pick s side).hi else (pick s side).lo : ℚ) : ℝ)) :
    ∀ i, binding x.1 x.2 static i ∈ faceEnv s side high i := by
  intro i
  rcases i with _ | _ | i
  · cases side <;> cases high <;>
      simp_all [coord, pick, faceEnv, binding, IntervalRat.mem_def, IntervalRat.singleton,
        Sample.box, Set.mem_Icc, Sample.lo, Sample.hi, Prod.le_def]
  · cases side <;> cases high <;>
      simp_all [coord, pick, faceEnv, binding, IntervalRat.mem_def, IntervalRat.singleton,
        Sample.box, Set.mem_Icc, Sample.lo, Sample.hi, Prod.le_def]
  · exact static_mem _

private theorem face_sign {old next : Sample} (side high : Bool) (ok : checkFace old next side high)
    {x y : ℝ × ℝ} (hy : y ∈ old.box) (hx : x ∈ next.box)
    (hf : coord x side = ((if high then (pick next side).hi else
      (pick next side).lo : ℚ) : ℝ)) :
    if high then coord y side ≤ past side x else past side x ≤ coord y side := by
  cases he : enclose (faceEnv next side high) (previous side) with
  | none => simp [checkFace,he] at ok
  | some v =>
    have hv : past side x ∈ v := enclose_sound _ _ _ (onFace hx side high hf) he
    have hcoord : coord y side ∈ pick old side := by
      cases side
      · exact ⟨hy.1.1,hy.2.1⟩
      · exact ⟨hy.1.2,hy.2.2⟩
    cases high
    · simp [checkFace,he] at ok
      exact hv.2.trans ((show (v.hi:ℝ) ≤ (pick old side).lo by exact_mod_cast ok).trans hcoord.1)
    · simp [checkFace,he] at ok
      exact hcoord.2.trans ((show ((pick old side).hi:ℝ) ≤ v.lo by exact_mod_cast ok).trans hv.1)

private theorem step_exists {old next : Sample} (ok : ∀ side high, checkFace old next side high)
    {y : ℝ × ℝ} (hy : y ∈ old.box) :
    ∃ x ∈ next.box, past false x = y.1 ∧ past true x = y.2 := by
  let s := next
  let f (x : ℝ × ℝ) := (past false x - y.1, past true x - y.2)
  have hc : Continuous f := ((past_continuous false).sub continuous_const).prodMk
    ((past_continuous true).sub continuous_const)
  obtain ⟨x,hx,hr⟩ := rectangle_root s.lo s.hi s.ordered f hc.continuousOn
    (fun _ hx e => sub_nonpos.mpr (face_sign false false (ok ..) hy hx e))
    (fun _ hx e => sub_nonneg.mpr (face_sign false true (ok ..) hy hx e))
    (fun _ hx e => sub_nonpos.mpr (face_sign true false (ok ..) hy hx e))
    (fun _ hx e => sub_nonneg.mpr (face_sign true true (ok ..) hy hx e))
  exact ⟨x,hx,sub_eq_zero.mp (congrArg Prod.fst hr),sub_eq_zero.mp (congrArg Prod.snd hr)⟩

private theorem admissible (k : Fin 21) :
    (-1/20 : ℚ) ≤ (sample k).q.lo ∧ (sample k).q.hi ≤ 4/5 ∧
    (-1/20 : ℚ) ≤ (sample k).b.lo ∧ (sample k).b.hi ≤ 4/5 := by
  revert k; decide +kernel

theorem collapse_of_boxes (sample : Nat → Sample)
    (initial : (sample 0).q.lo ≤ 7/10 ∧ 7/10 ≤ (sample 0).q.hi ∧
               (sample 0).b.lo ≤ 0 ∧ 0 ≤ (sample 0).b.hi)
    (admissible : ∀ k : Fin 21, -1/20 ≤ (sample k).q.lo ∧ (sample k).q.hi ≤ 4/5 ∧
                                  -1/20 ≤ (sample k).b.lo ∧ (sample k).b.hi ≤ 4/5)
    (failure : Fin 21) (margin : (sample failure).q.hi - (sample failure).b.lo < 3/25)
    (ok : ∀ (k : Fin 20) s h, checkFace (sample k) (sample (k.val+1)) s h) :
    Targets.Bench_03b_asap7_sram_6t_fin_collapse_sat realTF := by
  classical
  have cast {u v : ℚ} (h : u ≤ v) : (u:ℝ) ≤ v := by exact_mod_cast h
  let point k := {x : ℝ × ℝ // x ∈ (sample k).box}
  let init : point 0 := ⟨(7/10,0), by
    obtain ⟨a,b,c,d⟩ := initial
    change (((sample 0).q.lo : ℝ) ≤ 7/10 ∧ ((sample 0).b.lo : ℝ) ≤ 0) ∧
      (7/10 ≤ ((sample 0).q.hi : ℝ) ∧ 0 ≤ ((sample 0).b.hi : ℝ))
    exact ⟨⟨by simpa using cast a,by simpa using cast c⟩,by simpa using cast b,by simpa using cast d⟩⟩
  let step (k : Nat) (y : point k) : point (k+1) := if hk : k < 20 then
    ⟨(step_exists (ok ⟨k,hk⟩) y.property).choose,
     (step_exists (ok ⟨k,hk⟩) y.property).choose_spec.1⟩ else
    ⟨(sample (k+1)).lo,le_rfl,(sample (k+1)).ordered⟩
  let traj (k : Nat) : point k := Nat.rec (motive := point) init step k
  have evolution (k : Nat) (hk : k < 20) :
      past false (traj (k+1)).val = (traj k).val.1 ∧ past true (traj (k+1)).val = (traj k).val.2 := by
    change past false (step k (traj k)).val = _ ∧ past true (step k (traj k)).val = _
    simp only [step, dite_eq_left hk]
    exact (step_exists (ok ⟨k,hk⟩) (traj k).property).choose_spec.2
  let state (k i : Nat) := if i = 0 then (traj k).val.1 else (traj k).val.2
  have bounds (k : Nat) (hk : k ≤ 20) :
      (-1/20 ≤ state k 0 ∧ state k 0 ≤ 4/5) ∧ (-1/20 ≤ state k 1 ∧ state k 1 ≤ 4/5) := by
    obtain ⟨a,b,c,d⟩ := admissible ⟨k,by omega⟩
    have h := (traj k).property
    exact ⟨⟨le_trans (by simpa [Sample.lo,Sample.hi] using cast a) h.1.1, le_trans h.2.1 (by simpa [Sample.lo,Sample.hi] using cast b)⟩,
      le_trans (by simpa [Sample.lo,Sample.hi] using cast c) h.1.2, le_trans h.2.2 (by simpa [Sample.lo,Sample.hi] using cast d)⟩
  have unsafeStep : state failure 0 - state failure 1 < 3/25 := by
    have h := sub_le_sub (traj failure).property.2.1 (traj failure).property.1.2
    apply lt_of_le_of_lt h
    change ((sample failure).q.hi : ℝ) - (sample failure).b.lo < 3/25
    have cast {a b : ℚ} (h : a < b) : (a:ℝ) < b := by exact_mod_cast h
    simpa using cast margin
  refine ⟨-1/4,-83/50,12/25,5/2,5/2,Real.sqrt (13/2),5/2,11/5,Real.sqrt (13/2),state,?_,?_,failure.val,by omega,?_⟩
  · dsimp only [realTF]
    push_cast
    refine ⟨by norm_num,by norm_num,by norm_num,?_⟩
    exact bounds
  · dsimp only [realTF]
    push_cast
    repeat' apply And.intro
    all_goals try first
      | exact Real.sqrt_nonneg _
      | exact Real.mul_self_sqrt (by norm_num)
      | rfl
      | solve | norm_num
    intro k hk
    obtain ⟨hq,hb⟩ := evolution k hk
    constructor
    · apply sub_eq_iff_eq_add.mp
      norm_num [past,previous,drive,c,PExpr.eval,realTF,QRat.eval,binding,static,shift,asp,eta,state] at hq ⊢
      exact hq
    · apply sub_eq_iff_eq_add.mp
      norm_num [past,previous,drive,c,PExpr.eval,realTF,QRat.eval,binding,static,shift,asp,eta,state] at hb ⊢
      exact hb
  · simpa [realTF] using unsafeStep

theorem collapse_of_faces (ok : ∀ (k : Fin 20) s h, faceCheck k s h) :
    Targets.Bench_03b_asap7_sram_6t_fin_collapse_sat realTF :=
  collapse_of_boxes sample (by decide +kernel) admissible ⟨12,by decide⟩ (by decide +kernel) ok

end SpiceSmtBench.SramTrajectory
