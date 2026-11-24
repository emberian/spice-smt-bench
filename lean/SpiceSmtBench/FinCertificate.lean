import SpiceSmtBench.FinTransport
import SpiceSmtBench.TargetsGenerated

namespace SpiceSmtBench.FinCertificate

open FinMesh FinTransport SgConductance

private noncomputable def triple (a b c : ℝ) : Nat → ℝ
  | 0 => a | 1 => b | _ => c

-- Use real literals in the stamp adapter. The interval certificate stores the
-- same constants as rationals so its endpoint computations are executable.
private noncomputable abbrev kB : ℝ := 4308666631/50000000000000
private noncomputable abbrev band (t : ℝ) := (6498530148177529/1000000000000)*
  (6666666666666667/2000000000000000000-1/t)
private noncomputable abbrev confinement (tf : ℝ) (j : Nat) :=
  if j=1 then (8357/10000)/(tf*tf) else (27/20)*((8357/10000)/(tf*tf))
private noncomputable abbrev prefactor (t root tf : ℝ) :=
  (801088317/50000000000000000000000000)*
    ((10000000000*((t/300*root)*Real.exp (band t)))*
    ((300/(t/300*root))*(tf*(5333333333333333/500000000000000)/(64+tf))))

private noncomputable def term (t root tf dx v u l r e b : ℝ) (j : Nat) :=
  prefactor t root tf * ((kB*t)*
    (b*e*Real.exp ((v-confinement tf j-l)/(kB*t))-
     b*Real.exp ((u-confinement tf j-r)/(kB*t))))/dx

private theorem weight {z b : ℝ} (lo : 1-z/2+z*z/12-(z*z)*(z*z)/720 ≤ b)
    (hi : b ≤ 1-z/2+z*z/12) (hz : z=0) : b=1 := by
  subst z; linarith

private theorem term_eq {t root tf dx v u l r e b : ℝ} (j : Nat)
    (tp : 0<t) (rp : 0<root)
    (he : e=Real.exp ((u-v)/(kB*t))) (hb : b*(e-1)=(u-v)/(kB*t))
    (hn : (u-v)/(kB*t)=0 → b=1) :
    term t root tf dx v u l r e b j =
    scale t tf dx * conductance (arg v t tf j) (arg u t tf j) *
      (Real.exp (-l/(kB*t))-Real.exp (-r/(kB*t))) := by
  subst e
  let s := confinement tf j
  have hsub : (u-s)-(v-s)=u-v := by ring
  have f := flux (a := v-s) (b := u-s) (l := l) (r := r) (act := band t)
    (vt := kB*t) (w := b) (by rwa [hsub]) (by rwa [hsub])
  rw [hsub] at f
  have hs : shift tf j = s := by
    dsimp [shift,wall,s,confinement]; split <;> norm_num
  unfold arg; rw [hs, mul_assoc]
  simp only [activation,beta,ambientInv,kb,Rat.cast_div,Rat.cast_ofNat]
  rw [← f]
  dsimp [term,scale,prefactor,charge,areaFactor,kb,s,kB,band]
  push_cast
  field_simp [tp.ne',rp.ne']

private theorem left_row {a w z top d : ℝ} (hd : 0 < d)
    (h : 0 ≤ a+(w/d+z/(d*d))+top) : 0 ≤ (a+top)*(d*d)+w*d+z := by
  have := mul_nonneg h (mul_self_nonneg d)
  field_simp [hd.ne'] at this
  linarith only [this]

private theorem right_row {a w z top d : ℝ} (hd : 0 < d)
    (h : 0 ≤ a+(z/(d*d)+w/d)+top) : 0 ≤ (a+top)*(d*d)+w*d+z := by
  apply left_row hd
  rwa [add_comm (w/d)]

private theorem center_row {a u v top d : ℝ} (hd : 0 < d)
    (h : 0 ≤ a+(u/(d*d)+v/(d*d))+top) : 0 ≤ (a+top)*(d*d)+(u+v) := by
  have := mul_nonneg h (mul_self_nonneg d)
  field_simp [hd.ne'] at this
  linarith only [this]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 280000 in
theorem certified : Targets.Bench_13_asap7_finfet_2d_poisson_qconfinement realTF := by
  intro dt dl metal t root p10 p11 p12 p20 p21 p22 p30 p31 p32 f1 f2 f3
    e00 b00 e01 b01 e02 b02 e10 b10 e11 b11 e12 b12 e20 b20 e21 b21 e22 b22 e30 b30 e31 b31 e32 b32 current mid box phys fail
  simp only [and_assoc] at phys box
  obtain ⟨dtl,dth,dll,_,ml,_,_,th,_⟩ := box
  obtain ⟨tp,rp,square,
    r10,r11,r12,r20,r21,r22,r30,r31,r32,
    _,E00,B00,L00,H00,_,E01,B01,L01,H01,_,E02,B02,L02,H02,
    _,E10,B10,L10,H10,_,E11,B11,L11,H11,_,E12,B12,L12,H12,
    _,E20,B20,L20,H20,_,E21,B21,L21,H21,_,E22,B22,L22,H22,
    _,E30,B30,L30,H30,_,E31,B31,L31,H31,_,E32,B32,L32,H32,
    c1,c2,c3,terminal,_⟩ := phys
  dsimp only [realTF] at *
  push_cast at *
  let tf := 13/2+dt
  let dx := (21+dl)/4
  let dy := tf/4
  let gate := -(7/50+metal)
  have tfL : 6 ≤ tf := by dsimp [tf]; linarith only [dtl]
  have tfH : tf ≤ 7 := by dsimp [tf]; linarith only [dth]
  have dxL : 99/20 ≤ dx := by dsimp [dx]; linarith only [dll]
  have dyL : 3/2 ≤ dy := by dsimp [dy]; linarith only [tfL]
  have dyH : dy ≤ 7/4 := by dsimp [dy]; linarith only [tfH]
  have dyP : 0 < dy := by linarith only [dyL]
  have tfP : 0 < tf := by linarith only [tfL]
  have rootP : 0 < root := by nlinarith only [rp,square,tp]
  let p : Grid ℝ
    | 0, _ => 13/25
    | 1, j => triple p10 p11 p12 j
    | 2, j => triple p20 p21 p22 j
    | 3, j => triple p30 p31 p32 j
    | _, _ => 61/50
  have nonneg {x y : ℝ} (h : x=y) (s : 0≤y) : 0≤x := h ▸ s
  have bounded := enclosure p (gate := gate) (by dsimp [gate]; linarith only [ml]) (dx := dx) (by linarith only [dxL]) dyL dyH
    (by intro j; norm_num [p,W,barrier]) (by intro j; norm_num [p,W,barrier]) (by
      intro i j
      fin_cases i <;> fin_cases j <;>
        norm_num only [row,axial,lateral,robin,p,triple,Fin.val_zero,Fin.val_one,
          Fin.val_ofNat,Nat.reduceAdd,Nat.reduceSub,↓reduceIte,zero_add,add_zero,zero_mul] <;>
        first
        | exact left_row dyP (nonneg r10 (by positivity))
        | exact center_row dyP (nonneg r11 (by positivity))
        | exact right_row dyP (nonneg r12 (by positivity))
        | exact left_row dyP (nonneg r20 (by positivity))
        | exact center_row dyP (nonneg r21 (by positivity))
        | exact right_row dyP (nonneg r22 (by positivity))
        | exact left_row dyP (nonneg r30 (by positivity))
        | exact center_row dyP (nonneg r31 (by positivity))
        | exact right_row dyP (nonneg r32 (by positivity)))
  let f : Nat → ℝ | 0 => 0 | 1 => f1 | 2 => f2 | 3 => f3 | _ => 7/10
  let b : Grid ℝ
    | 0, j => triple b00 b01 b02 j
    | 1, j => triple b10 b11 b12 j
    | 2, j => triple b20 b21 b22 j
    | _, j => triple b30 b31 b32 j
  let e : Grid ℝ
    | 0, j => triple e00 e01 e02 j
    | 1, j => triple e10 e11 e12 j
    | 2, j => triple e20 e21 e22 j
    | _, j => triple e30 e31 e32 j
  let lane (i j : Nat) := term t root tf dx (p i j) (p (i+1) j) (f i) (f (i+1)) (e i j) (b i j) j
  let edge (i : Nat) := lane i 0 + lane i 1 + lane i 2
  have curr (i : Fin 4) : current = edge i := by
    fin_cases i
    · simpa only [edge,lane,p,triple,f,e,b,term,confinement,tf,dx,Fin.val_zero,Fin.val_one,Fin.val_ofNat,Nat.reduceAdd,Nat.reduceEqDiff,↓reduceIte,sub_zero,prefactor,band,kB] using (terminal |>.trans c3 |>.trans c2 |>.trans c1)
    · simpa only [edge,lane,p,triple,f,e,b,term,confinement,tf,dx,Fin.val_zero,Fin.val_one,Fin.val_ofNat,Nat.reduceAdd,Nat.reduceEqDiff,↓reduceIte,sub_zero,prefactor,band,kB] using (terminal |>.trans c3 |>.trans c2)
    · simpa only [edge,lane,p,triple,f,e,b,term,confinement,tf,dx,Fin.val_zero,Fin.val_one,Fin.val_ofNat,Nat.reduceAdd,Nat.reduceEqDiff,↓reduceIte,sub_zero,prefactor,band,kB] using (terminal |>.trans c3)
    · simpa only [edge,lane,p,triple,f,e,b,term,confinement,tf,dx,Fin.val_zero,Fin.val_one,Fin.val_ofNat,Nat.reduceAdd,Nat.reduceEqDiff,↓reduceIte,sub_zero,prefactor,band,kB] using (terminal)
  let g (i j : Nat) := conductance (arg (p i j) t tf j) (arg (p (i+1) j) t tf j)
  let G (i : Nat) := scale t tf dx * (g i 0 + g i 1 + g i 2)
  let X (i : Nat) := Real.exp (-(f i)/(kB*t))
  have law (i : Fin 4) : current = G i * (X i-X (i.val+1)) := by
    have termLaw (j : Fin 3) : lane i j = scale t tf dx * g i j * (X i-X (i.val+1)) := by
      apply term_eq j tp rootP <;> fin_cases i <;> fin_cases j <;>
        first | assumption | apply weight <;> assumption
    rw [curr i]; dsimp only [edge,G]; have h0 := termLaw 0
    have h1 := termLaw 1
    have h2 := termLaw 2
    simp only [Fin.val_zero,Fin.val_one] at h0 h1
    change lane i 2 = scale t tf dx * g i 2 * (X i-X (i.val+1)) at h2
    rw [h0,h1,h2]; ring
  obtain ⟨spos,smax⟩ := scale_bound (tfin := tf) (dx := dx) tp th tfP tfH dxL
  have gp (i : Nat) : 0<G i := mul_pos spos (add_pos (add_pos (conductance_pos ..)
    (conductance_pos ..)) (conductance_pos ..))
  have posI : 0<current := by linarith only [fail]
  have firstDrop : 0<X 0-X 1 := pos_of_mul_pos_right ((law 0) ▸ posI) (gp 0).le
  have start : X 0=1 := by simp [X,f]
  have total : (X 1-X 2)+(X 2-X 3)≤1 := by linarith only [start,firstDrop,Real.exp_pos (-(f 3)/(kB*t))]
  have upper (i : Fin 5) (j : Fin 3) (small : barrier i j ≤ 1/5) :=
    peak_bound (bounded i j) small tp th tfP tfH
  have compare (i : Nat) (h : i=1 ∨ i=2) : G i ≤ (scaleMax:ℝ)*
      ((conductance (peak i 0) (peak (i+1) 0)+conductance (peak i 1) (peak (i+1) 1))+
        conductance (peak i 2) (peak (i+1) 2)) := by
    apply mul_le_mul smax _ ((add_pos (add_pos (conductance_pos ..) (conductance_pos ..)) (conductance_pos ..)).le) (spos.le.trans smax)
    apply add_le_add (add_le_add _ _) _ <;> apply monotone <;>
      rcases h with rfl | rfl <;>
      first
      | exact upper 1 0 (by decide +kernel)
      | exact upper 1 1 (by decide +kernel)
      | exact upper 1 2 (by decide +kernel)
      | exact upper 2 0 (by decide +kernel)
      | exact upper 2 1 (by decide +kernel)
      | exact upper 2 2 (by decide +kernel)
      | exact upper 3 0 (by decide +kernel)
      | exact upper 3 1 (by decide +kernel)
      | exact upper 3 2 (by decide +kernel)
  exact (not_lt_of_ge (leakage_bound (law 1) (law 2) (gp 1) (gp 2) total
    (compare 1 (Or.inl rfl)) (compare 2 (Or.inr rfl)))) fail

end SpiceSmtBench.FinCertificate
