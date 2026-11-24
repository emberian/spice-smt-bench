import SpiceSmtBench.RingReplay
import SpiceSmtBench.TargetsGenerated

namespace SpiceSmtBench.RingCertificate
open RingEnvelope LeanCert.Core IntervalRat IntervalCheck BoxCertificate

private noncomputable abbrev size (dt : ℝ) := 3*(2*(18+(5+dt))/12)
private noncomputable abbrev offset (dt : ℝ) := (9171467369656967/10000000000000000)*
  (1/((5+dt)*(5+dt))-1/25)
private noncomputable abbrev eta (k l : ℝ) := k*Real.exp (-(12/(2*l)))
private noncomputable abbrev cap (dl : ℝ) := (1/2)*((27/50000000000000000)/(11/2+dl))
private noncomputable abbrev fringe (dl : ℝ) := (27/50)/(11/2+dl)
private noncomputable abbrev determinant (c : ℝ) := (9/5+4*c)*(9/5+c)
private noncomputable def process (dt dl l : ℝ) : Process :=
  let c := fringe dl
  ⟨23/100+offset dt,6/25+offset dt,eta (14/5) l,eta (29/10) l,size dt,
    (9/5+2*c)/determinant c,c/determinant c⟩

private def lambdaBox : I := ⟨173/100,18383/10000,by decide +kernel⟩
private def etaExpr (q : ℚ) : PExpr :=
  .mul (.const ⟨q.num,q.den,q.den_pos⟩)
    (.exp (.neg (.div (.const ⟨12,1,by decide⟩) (.mul (.const ⟨2,1,by decide⟩) (.var 0)))))

private theorem eta_mem {l : ℝ} (hl : l ∈ lambdaBox) (q : ℚ)
    (ok : (RealInterval.enclose (fun _ => lambdaBox)
      (etaExpr q)).any
       (fun v => decide (87/1000 ≤ v.lo ∧ v.hi ≤ 111/1000))) :
    eta (q:ℝ) l ∈ diblBox := by
  cases h : RealInterval.enclose (fun _ => lambdaBox) (etaExpr q) with
  | none => simp [h] at ok
  | some v =>
    simp only [h,Option.any_some,decide_eq_true_eq] at ok
    have m := RealInterval.enclose_sound _ _ (fun _ => l) (fun _ => hl) h
    simp only [etaExpr,PExpr.eval,QRat.eval,realTF,Int.cast_ofNat,Nat.cast_one,div_one] at m
    have cast : realTF.ofRat q.num q.den = (q:ℝ) := by simp [realTF,Rat.cast_def]
    change (↑q.num / (q.den:ℝ)) * _ ∈ v at m
    rw [← Rat.cast_def] at m
    exact ⟨(Rat.cast_le.mpr ok.1).trans m.1,m.2.trans (Rat.cast_le.mpr ok.2)⟩

private theorem admissible {dt dl l : ℝ} (tl : -3/10 ≤ dt) (th : dt ≤ 3/10)
    (ll : -3/5 ≤ dl) (lh : dl ≤ 3/5) (lp : 0 ≤ l) (square : l*l=3/4*((5+dt)*(17/20))) :
    Admissible (process dt dl l) := by
  have lam : l ∈ lambdaBox := by
    norm_num [lambdaBox,mem_def]; constructor <;> nlinarith only [tl,th,lp,square]
  have lo : 47/10 ≤ 5+dt := by linarith
  have hi : 5+dt ≤ 53/10 := by linarith
  have low := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 47/10) lo
  have high := mul_self_le_mul_self (by linarith : 0 ≤ 5+dt) hi
  have sqpos : 0 < (5+dt)*(5+dt) := by linarith only [low]
  have shiftLo := one_div_le_one_div_of_le sqpos high
  have shiftHi := one_div_le_one_div_of_le (by norm_num : 0 < (47/10:ℝ)*(47/10)) low
  have cLo : 27/305 ≤ fringe dl := (le_div_iff₀ (by linarith)).2 (by linarith)
  have cHi : fringe dl ≤ 27/245 := (div_le_iff₀ (by linarith)).2 (by linarith)
  let c := fringe dl
  have denP : 0 < determinant c := by
    have : 0<c := by linarith only [cLo]
    exact mul_pos (by linarith) (by linarith)
  have c2L := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 27/305) cLo
  have c2H := mul_self_le_mul_self (by linarith : 0 ≤ c) cHi
  change 27/305 ≤ c at cLo
  change c ≤ 27/245 at cHi
  change 27/305*(27/305) ≤ c*c at c2L
  have hn := eta_mem lam (14/5) (by decide +kernel)
  have hp := eta_mem lam (29/10) (by decide +kernel)
  norm_num at shiftLo shiftHi
  constructor
  · norm_num [process,thresholdBox,mem_def,offset]; constructor <;> linarith only [shiftLo,shiftHi]
  · norm_num [process,thresholdBox,mem_def,offset]; constructor <;> linarith only [shiftLo,shiftHi]
  · simpa only [process,Rat.cast_div,Rat.cast_ofNat] using hn
  · simpa only [process,Rat.cast_div,Rat.cast_ofNat] using hp
  · change ((1135/100:ℚ):ℝ) ≤ size dt ∧ size dt ≤ ((1165/100:ℚ):ℝ); push_cast; dsimp [size]; constructor <;> linarith
  · change ((471/1000:ℚ):ℝ) ≤ (9/5+2*c)/determinant c ∧ (9/5+2*c)/determinant c ≤ ((487/1000:ℚ):ℝ)
    push_cast; rw [le_div_iff₀ denP,div_le_iff₀ denP]; dsimp [determinant]
    constructor <;> nlinarith only [cLo,cHi,c2L,c2H]
  · change ((21/1000:ℚ):ℝ) ≤ c/determinant c ∧ c/determinant c ≤ ((26/1000:ℚ):ℝ)
    push_cast; rw [le_div_iff₀ denP,div_le_iff₀ denP]; dsimp [determinant]
    constructor <;> nlinarith only [cLo,cHi,c2L,c2H]

private noncomputable def stampChannel (a geom k threshold b d g : ℝ) :=
  let gate := k*(g-(threshold-b*d))
  let f := sp (gate/(6463/125000))
  let r := sp ((gate-d)/(6463/125000))
  (a*geom*(f*f-r*r))/(1+(1/10)*f)
private noncomputable def raw (dt l d g v : ℝ) :=
  stampChannel (11/50000000) (size dt) (9/10) (6/25+offset dt) (eta (29/10) l) (v-d) (v-g) -
  stampChannel (1/4000000) (size dt) (91/100) (23/100+offset dt) (eta (14/5) l) d g

private theorem raw_eq (dt dl l d g v : ℝ) : raw dt l d g v =
    size dt/1000000*net (process dt dl l) d g v := by
  dsimp [raw,stampChannel,net,process,channel]
  simp only [sub_div]
  ring

-- The three rows share a determinant. The first diagonal groups the two
-- fringe contributions before the load because of the node traversal order.
private noncomputable def rawDet (h : ℝ) :=
  let m := -(h+h)
  let A := ((9/5000000000000000+h)+h)+((h+h)+(h+h))
  let B := ((h+h)+9/5000000000000000)+((h+h)+(h+h))
  B*(A*A-m*m)+(m*(m*m-m*A)+m*(m*m-A*m))

private noncomputable def cofactorRow (i : Nat) (h a b c : ℝ) :=
  let m := -(h+h)
  let A := ((9/5000000000000000+h)+h)+((h+h)+(h+h))
  let B := ((h+h)+9/5000000000000000)+((h+h)+(h+h))
  let numer := match i with
    | 0 => (A*A-m*m)*a+((m*m-m*A)*b+(m*m-A*m)*c)
    | 1 => (m*m-m*A)*a+((B*A-m*m)*b+(m*m-B*m)*c)
    | _ => (m*m-A*m)*a+((m*m-B*m)*b+(B*A-m*m)*c)
  numer/rawDet h

private theorem capacitance {dl : ℝ} (ll : -3/5 ≤ dl) (a b c : ℝ) (i : Fin 3) :
    let g := fringe dl
    let d := (9/5+2*g)/determinant g
    let m := g/determinant g
    cofactorRow i (cap dl) a b c / 1000000000000000 =
      match i.val with
      | 0 => d*a+m*(b+c)
      | 1 => d*b+m*(c+a)
      | _ => d*c+m*(a+b) := by
  have gp : 0 < fringe dl := div_pos (by norm_num) (by linarith)
  have h : cap dl = fringe dl/2000000000000000 := by dsimp [fringe,cap]; ring
  dsimp only
  rw [h]
  generalize hg : fringe dl = u at gp ⊢
  have determinantEq : rawDet (u/2000000000000000) =
      ((9/5+4*u)*determinant u)/10^45 := by dsimp [rawDet,determinant]; ring
  have denP : determinant u ≠ 0 := by dsimp [determinant]; positivity
  have extra : 9/5+4*u ≠ 0 := by positivity
  fin_cases i
  · change _ = (9/5+2*u)/determinant u*a+u/determinant u*(b+c)
    dsimp only [cofactorRow]; rw [determinantEq]; field_simp [denP,extra]; ring
  · change _ = (9/5+2*u)/determinant u*b+u/determinant u*(c+a)
    dsimp only [cofactorRow]; rw [determinantEq]; field_simp [denP,extra]; ring
  · change _ = (9/5+2*u)/determinant u*c+u/determinant u*(a+b)
    dsimp only [cofactorRow]; rw [determinantEq]; field_simp [denP,extra]; ring


private def next (i : Fin 3) : Fin 3 := i+1
private def prev (i : Fin 3) : Fin 3 := i+2

private theorem convertRow {dt dl l v : ℝ} (ll : -3/5 ≤ dl) (s : Fin 3 → ℝ) (i : Fin 3) :
    let j n := raw dt l (s n) (s (prev n)) v
    1/2000000000000*cofactorRow i (cap dl) (j 0) (j 1) (j 2) =
      halfStep (process dt dl l) (s i) (s (next i)) (s (prev i)) v := by
  dsimp only
  let j n := raw dt l (s n) (s (prev n)) v
  have h := capacitance ll (j 0) (j 1) (j 2) i
  change 1/2000000000000*cofactorRow _ _ _ _ _ = _
  calc
    _ = 500*(cofactorRow i (cap dl) (j 0) (j 1) (j 2)/1000000000000000) := by ring
    _ = _ := by
      rw [h]
      let p := process dt dl l
      let N (i : Fin 3) := net p (s i) (s (prev i)) v
      have hj (i : Fin 3) : j i = size dt/1000000*N i := raw_eq .. 
      rw [hj 0,hj 1,hj 2]
      fin_cases i
      · change 500*(p.diagonal*(size dt/1000000*N 0)+
          p.coupling*(size dt/1000000*N 1+size dt/1000000*N 2)) =
          1/2000*(size dt*(p.diagonal*N 0+p.coupling*(N 1+N 2)))
        ring
      · change 500*(p.diagonal*(size dt/1000000*N 1)+
          p.coupling*(size dt/1000000*N 2+size dt/1000000*N 0)) =
          1/2000*(size dt*(p.diagonal*N 1+p.coupling*(N 2+N 0)))
        ring
      · change 500*(p.diagonal*(size dt/1000000*N 2)+
          p.coupling*(size dt/1000000*N 0+size dt/1000000*N 1)) =
          1/2000*(size dt*(p.diagonal*N 2+p.coupling*(N 0+N 1)))
        ring

private theorem within {old new a b : ℝ}
    (lo : -2/25 ≤ old) (hi : old ≤ 83/100)
    (pa : -abs (old-(-2/25)) < a ∧ a < abs (old-83/100))
    (pb : -abs (new-(-2/25)) < b ∧ b < abs (new-83/100))
    (step : new=old+(a+b)) : -2/25 ≤ new ∧ new ≤ 83/100 := by
  rw [abs_of_nonneg (by linarith only [lo] : 0 ≤ old-(-2/25)),
    abs_of_nonpos (by linarith only [hi] : old-83/100 ≤ 0)] at pa
  constructor <;> by_contra! bad
  · have := pb.1; rw [abs_of_neg (by linarith only [bad])] at this; linarith only [pa.1,step,this]
  · have := pb.2; rw [abs_of_pos (by linarith only [bad])] at this; linarith only [pa.2,step,this]

set_option maxRecDepth 32000 in
theorem certified :
    Targets.Bench_08_gt2n_gaa_ring_oscillator_3stage_ode realTF := by
  intro v dt dl p1 n1 p2 n2 p3 n3 st
  dsimp only
  intro box phys
  obtain ⟨⟨vl,vh⟩,⟨tl,th⟩,⟨ll,lh⟩,bounds⟩ := box
  simp only [and_assoc] at phys
  obtain ⟨_,_,_,hp1,s1,_,_,_,hn1,s2,_,_,_,hp2,s3,_,_,_,hn2,s4,_,_,_,hp3,s5,_,_,_,hn3,s6,
    i0l,i0h,i1l,i1h,i2l,i2h,steps⟩ := phys
  dsimp only [realTF] at vl vh tl th ll lh hp1 s1 hn1 s2 hp2 s3 hn2 s4 hp3 s5 hn3 s6 bounds i0l i0h i1l i1h i2l i2h
  push_cast at vl vh tl th ll lh hp1 s1 hn1 s2 hp2 s3 hn2 s4 hp3 s5 hn3 s6 bounds i0l i0h i1l i1h i2l i2h
  have unique {x : ℝ} (h : 0 ≤ x) (s : x*x=3/4*((5+dt)*(17/20))) : x=p1 :=
    (mul_self_inj_of_nonneg h hp1).mp (s.trans s1.symm)
  have eq2 := unique hn1 s2
  subst n1
  have eq3 := unique hp2 s3
  subst p2
  have eq4 := unique hn2 s4
  subst n2
  have eq5 := unique hp3 s5
  subst p3
  have eq6 := unique hn3 s6
  subst n3
  let p := process dt dl p1
  have good : Admissible p := admissible tl th ll lh hp1 s1
  let s (k : Nat) (i : Fin 3) := st k i
  let j (k : Nat) (i : Fin 3) := raw dt p1 (s k i) (s k (prev i)) v
  let f (k : Nat) (i : Fin 3) := cofactorRow i (cap dl) (j k 0) (j k 1) (j k 2)
  let inc (k : Nat) (i : Fin 3) := halfStep p (s k i) (s k (next i)) (s k (prev i)) v
  have transform (k : Nat) (i : Fin 3) : 1/2000000000000*f k i = inc k i := convertRow ll (s k) i
  have recurrence (k : Nat) (hk : k < 40) (i : Fin 3) :
      s (k+1) i = s k i+(inc k i+inc (k+1) i) := by
    obtain ⟨a,b,c⟩ := steps k hk
    dsimp only [realTF] at a b c
    push_cast at a b c
    rw [← transform,← transform,← mul_add]
    fin_cases i
    · exact a
    · exact b
    · exact c
  have sv : v ∈ supplyBox := by simpa [supplyBox,mem_def] using And.intro vl vh
  have safe (k : Nat) (hk : k ≤ 40) (i : Fin 3) :
      -abs (s k i-(-2/25)) < inc k i ∧ inc k i < abs (s k i-83/100) := by
    have mem (a : Fin 3) : s k a ∈ nodeBox := by
      have b := bounds k hk
      simp only [neg_div] at b
      fin_cases a <;> norm_num only [s,nodeBox,mem_def,Rat.cast_neg,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat,neg_div] <;>
        first | exact b.1 | exact b.2.1 | exact b.2.2
    exact barrier good (mem i) (mem (next i)) (mem (prev i)) sv
  have all (k : Nat) (hk : k≤40) (i : Fin 3) : -2/25 ≤ s k i ∧ s k i ≤ 83/100 := by
    induction k with
    | zero =>
      fin_cases i <;> constructor <;> dsimp [s] <;>
        linarith only [i0l,i0h,i1l,i1h,i2l,i2h]
    | succ k ih =>
      have old := ih (by omega)
      exact within old.1 old.2 (safe k (by omega) i) (safe (k+1) hk i) (recurrence k (by omega) i)
  rintro ⟨k,hk,bad⟩
  have a := all k hk 0
  have b := all k hk 1
  have c := all k hk 2
  dsimp only [realTF] at bad
  push_cast at bad
  change -2/25 ≤ st k 0 ∧ st k 0 ≤ 83/100 at a
  change -2/25 ≤ st k 1 ∧ st k 1 ≤ 83/100 at b
  change -2/25 ≤ st k 2 ∧ st k 2 ≤ 83/100 at c
  rcases bad with h|h|h|h|h|h <;> linarith only [h,a.1,a.2,b.1,b.2,c.1,c.2]

end SpiceSmtBench.RingCertificate
