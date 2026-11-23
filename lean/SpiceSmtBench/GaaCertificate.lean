import SpiceSmtBench.BoxCertificate
import SpiceSmtBench.TargetsGenerated

namespace SpiceSmtBench.GaaCertificate
open IntervalCheck BoxCertificate

-- Closed-form 1-D SG transport eliminates four quasi-Fermi potentials at
-- fixed temperature. The remaining system consists of four Poisson rows.
private def c (n : Int) (d : Nat := 1) (hd : 0 < d := by decide) : PExpr := .const ⟨n,d,hd⟩
local instance : Add PExpr := ⟨PExpr.add⟩
local instance : Sub PExpr := ⟨PExpr.sub⟩
local instance : Mul PExpr := ⟨PExpr.mul⟩
local instance : Div PExpr := ⟨PExpr.div⟩
local instance : Neg PExpr := ⟨PExpr.neg⟩

private def vt := c 4308666631 50000000000000 * c 432
private def thick := c 5 + c 11 20
private def qm := c 2293 2500 / (thick*thick)
private def dos := c 432 / c 300 * c 6 5
private def ni := c 10000000000 * (dos * .exp (c 6498530148177529 1000000000000 *
  (c 6666666666666667 2000000000000000000 - c 1 / c 432)))
private def mobility := c 300 / dos
private def psi : Nat → PExpr
  | 0 => c 13 25
  | 1 => .var 0
  | 2 => .var 1
  | 3 => .var 2
  | 4 => .var 3
  | _ => c 127 100

private def dropV (i : Nat) := psi (i+1)-psi i
private def delta (i : Nat) := dropV i / vt
private def edgeExp (i : Nat) := (delta i).exp
private def bern (i : Nat) := delta i / (edgeExp i-c 1)
private def weight (i : Nat) := ((psi 0-psi i)/vt).exp
private def resistance (i : Nat) := (weight i-weight (i+1))/dropV i
private def drainZ := (-(c 3 4)/vt).exp

private def sum (lo : Nat) : Nat → PExpr
  | 0 => c 0
  | n+1 => resistance lo + sum (lo+1) n
private def total := sum 0 5
private def z (i : Nat) := (sum i (5-i) + sum 0 i * drainZ)/total
private def carrier (i : Nat) := ((psi i-qm)/vt).exp * z i

private def poisson (i : Nat) :=
  let lap := (psi (i-1)+psi (i+1)-c 2*psi i)/c 144 25
  let wrap := (c 61 100-psi i)/(c 3 4*(thick*c 17 20))
  let fringe (p : PExpr) := c 9 50*(p-psi i)/((c 11 2-c 3 20)*c 12 5)
  let gate := if i=1 then wrap+fringe (psi 0) else if i=4 then wrap+fringe (psi 5) else wrap
  c 7732960760567449 500000000000000000000*(ni/c 10000000000000000*carrier i+c 1) - (lap+gate)

private def rows (i : Fin 4) := poisson (i.val+1)
private def band (v w : ℚ) (h : 0 ≤ w := by decide +kernel) : RealInterval.I :=
  ⟨v-w,v+w,by linarith⟩
private def mesh : Box 4 := ![
  band 0.56448392818715 0.00000000635, band 0.59996191202310 0.00000000632,
  band 0.65871232031739 0.00000000407, band 0.81386273159884 0.00000000177]

set_option maxRecDepth 32000
set_option maxHeartbeats 6000000
private theorem domain : ∀ i, checkDomain mesh (rows i) := by decide +kernel
private theorem faces : ∀ i h, checkFace mesh (rows i) i h := by decide +kernel

private def upperB (i : Nat) := c 1-delta i/c 2+delta i*delta i/c 12
private def lowerB (i : Nat) := upperB i-(delta i*delta i)*(delta i*delta i)/c 720
private def driveFlux := ((psi 0-qm)/vt).exp/vt*((c 1-drainZ)/total)
private def stack (flux : PExpr) :=
  c 801088317 50000000000000000000000000000*(ni*mobility)*
    ((c 3*(c 18*thick))*(vt*flux))/c 12 5
private def ambient := c 432-(c 1 1000000*c 900000)*(c 3 4*stack driveFlux)

private theorem edgeGuards : ∀ i : Fin 5,
    checkPositive mesh (dropV i) true ∧ checkPositive mesh (bern i-lowerB i) false ∧
    checkPositive mesh (upperB i-bern i) false := by decide +kernel
private theorem nodeGuards : ∀ i : Fin 4,
    checkPositive mesh (psi (i+1)-c (-2) 5) false ∧ checkPositive mesh (c 11 5-psi (i+1)) false ∧
    checkPositive mesh (z (i+1)-(-(c 2)/vt).exp) false ∧ checkPositive mesh (c 1-z (i+1)) false := by
  decide +kernel
private theorem auxGuards : checkPositive mesh total true ∧
    checkPositive mesh (ambient-c 355) false ∧ checkPositive mesh (c 385-ambient) false := by decide +kernel

private noncomputable def ev (x : Fin 4 → ℝ) (e : PExpr) := e.eval realTF (values x)
@[simp] private theorem ev_c (x : Fin 4 → ℝ) (n d h) : ev x (c n d h) = (n:ℝ)/d := rfl
@[simp] private theorem ev_add (x : Fin 4 → ℝ) (a b : PExpr) : ev x (a+b) = ev x a+ev x b := rfl
@[simp] private theorem ev_sub (x : Fin 4 → ℝ) (a b : PExpr) : ev x (a-b) = ev x a-ev x b := rfl
@[simp] private theorem ev_mul (x : Fin 4 → ℝ) (a b : PExpr) : ev x (a*b) = ev x a*ev x b := rfl
@[simp] private theorem ev_div (x : Fin 4 → ℝ) (a b : PExpr) : ev x (a/b) = ev x a/ev x b := rfl
@[simp] private theorem ev_neg (x : Fin 4 → ℝ) (a : PExpr) : ev x (-a) = -ev x a := rfl
@[simp] private theorem ev_exp (x : Fin 4 → ℝ) (a : PExpr) : ev x a.exp = Real.exp (ev x a) := rfl

private noncomputable def phi (x : Fin 4 → ℝ) (i : Nat) := -(ev x vt)*Real.log (ev x (z i))
private theorem vt_pos (x : Fin 4 → ℝ) : 0 < ev x vt := by norm_num [vt]

private theorem phi_range {x : Fin 4 → ℝ} (hx : ∀ i, x i ∈ mesh i) (i : Fin 4) :
    -(1/5) ≤ phi x (i+1) ∧ phi x (i+1) ≤ 2 ∧ 0 < ev x (z (i+1)) := by
  have h1 := positive_of_check _ _ false hx (nodeGuards i).2.2.1
  have h2 := positive_of_check _ _ false hx (nodeGuards i).2.2.2
  change 0 ≤ ev x (z (i+1)) - ev x (-(c 2)/vt).exp at h1
  change 0 ≤ ev x (c 1) - ev x (z (i+1)) at h2
  simp at h1 h2
  have hp : 0 < ev x (z (i+1)) := (Real.exp_pos _).trans_le h1
  have logLo := Real.log_le_log (Real.exp_pos _) h1
  rw [Real.log_exp] at logLo
  have logHi := Real.log_nonpos hp.le (by linarith : ev x (z (i+1)) ≤ 1)
  have ht := vt_pos x
  have lower := mul_le_mul_of_nonneg_left logLo ht.le
  field_simp [ht.ne'] at lower
  dsimp [phi]; exact ⟨by nlinarith [mul_nonpos_of_nonneg_of_nonpos ht.le logHi], by nlinarith, hp⟩

private theorem carrier_eq {x : Fin 4 → ℝ} (i : Nat) (hz : 0 < ev x (z i)) :
    Real.exp ((ev x (psi i)-ev x qm-phi x i)/ev x vt) = ev x (carrier i) := by
  simp only [carrier,ev_mul,ev_exp,ev_div,ev_sub,phi]
  rw [sub_div, Real.exp_sub]
  have h : -(ev x vt)*Real.log (ev x (z i))/ev x vt = -Real.log (ev x (z i)) := by
    field_simp [(vt_pos x).ne']
  rw [h,Real.exp_neg,Real.exp_log hz,div_inv_eq_mul]

-- Consecutive partial sums give exactly the same current on all five edges.
private theorem z_drop {x : Fin 4 → ℝ} (i : Fin 5) :
    ev x (z i) - ev x (z (i.val+1)) = ev x (resistance i) * ((1-ev x drainZ)/ev x total) := by
  fin_cases i <;> norm_num [z,sum,Fin.isValue] <;> ring

private theorem sg_flux {x : Fin 4 → ℝ} (i : Nat) (hi : 0 < ev x (dropV i))
    (zstep : ev x (z i)-ev x (z (i+1)) =
      ev x (resistance i)*((1-ev x drainZ)/ev x total)) :
    ev x (bern i)*ev x (edgeExp i)*ev x (carrier i) -
        ev x (bern i)*ev x (carrier (i+1)) = ev x driveFlux := by
  let v := ev x vt
  let p := ev x (psi i)
  let p' := ev x (psi (i+1))
  let q := ev x qm
  let p0 := ev x (psi 0)
  let E := Real.exp ((p'-p)/v)
  have hv : 0 < v := vt_pos x
  change 0 < p'-p at hi
  have hE : 1 < E := Real.one_lt_exp_iff.mpr (div_pos hi hv)
  have exp_id : E*Real.exp ((p-q)/v) = Real.exp ((p'-q)/v) := by
    dsimp [E]; rw [← Real.exp_add]; congr 1; ring
  have w_id : Real.exp ((p'-q)/v) * (Real.exp ((p0-p)/v) - Real.exp ((p0-p')/v)) =
      Real.exp ((p0-q)/v)*(E-1) := by
    dsimp [E]; rw [mul_sub,mul_sub,← Real.exp_add,← Real.exp_add,← Real.exp_add,mul_one]
    congr 2 <;> ring
  let b := (p'-p)/v/(E-1)
  simp only [bern,driveFlux,ev_div,ev_sub,ev_mul,ev_c,Int.cast_one,Nat.cast_one,div_one]
  change b*E*(Real.exp ((p-q)/v)*ev x (z i)) - b*(Real.exp ((p'-q)/v)*ev x (z (i+1))) =
    Real.exp ((p0-q)/v)/v*((1-ev x drainZ)/ev x total)
  calc
    _ = b*Real.exp ((p'-q)/v)*(ev x (z i)-ev x (z (i+1))) := by rw [← exp_id]; ring
    _ = _ := by
      rw [zstep]
      change b*Real.exp ((p'-q)/v)*(((Real.exp ((p0-p)/v)-Real.exp ((p0-p')/v))/(p'-p))*_) = _
      dsimp only [b]
      field_simp [ne_of_gt hi, ne_of_gt hv, ne_of_gt (sub_pos.mpr hE)]
      linear_combination (norm := ring) ((1-ev x drainZ)/ev x total) * w_id

private noncomputable def quasi (x : Fin 4 → ℝ) (i : Nat) : ℝ :=
  if i = 0 then 0 else if i = 5 then 3/4 else phi x i

private noncomputable def density (x : Fin 4 → ℝ) (i : Nat) :=
  Real.exp ((ev x (psi i)-ev x qm-quasi x i)/ev x vt)

private theorem density_eq {x : Fin 4 → ℝ} (hx : ∀ i, x i ∈ mesh i) (i : Fin 6) :
    density x i = ev x (carrier i) := by
  have ht := positive_of_check _ _ true hx auxGuards.1
  change 0 < ev x total at ht
  have z0 : ev x (z 0) = 1 := by
    change (ev x total + ev x (c 0)*ev x drainZ)/ev x total = 1
    simp [ht.ne']
  have z5 : ev x (z 5) = ev x drainZ := by
    change (ev x (c 0) + ev x total*ev x drainZ)/ev x total = ev x drainZ
    simp [ht.ne']
  fin_cases i
  · simp [density,quasi,carrier,z0]
  · exact carrier_eq 1 (phi_range hx 0).2.2
  · exact carrier_eq 2 (phi_range hx 1).2.2
  · exact carrier_eq 3 (phi_range hx 2).2.2
  · exact carrier_eq 4 (phi_range hx 3).2.2
  · simp [density,quasi,carrier,z5,drainZ,← Real.exp_add]; ring

private noncomputable def edgeCurrent (x : Fin 4 → ℝ) (i : Nat) :=
  801088317/50000000000000000000000000000*(ev x ni*ev x mobility)*
    ((3*(18*ev x thick))*(ev x vt*
      (ev x (bern i)*ev x (edgeExp i)*density x i - ev x (bern i)*density x (i+1))))/(12/5)

private theorem constant_current {x : Fin 4 → ℝ} (hx : ∀ i, x i ∈ mesh i) (i : Fin 5) :
    edgeCurrent x i = ev x (stack driveFlux) := by
  have h := sg_flux i (positive_of_check _ _ true hx (edgeGuards i).1) (z_drop i)
  have l := density_eq hx i.castSucc
  have r := density_eq hx i.succ
  change density x i = _ at l
  change density x (i.val+1) = _ at r
  simp [edgeCurrent,stack,l,r,h]

private theorem coordinate_bounds {x : Fin 4 → ℝ} (hx : ∀ i, x i ∈ mesh i) (i : Fin 4) :
    -(2/5) ≤ ev x (psi (i+1)) ∧ ev x (psi (i+1)) ≤ 11/5 := by
  have hl := positive_of_check _ _ false hx (nodeGuards i).1
  have hh := positive_of_check _ _ false hx (nodeGuards i).2.1
  change 0 ≤ ev x (psi (i+1)-c (-2) 5) at hl
  change 0 ≤ ev x (c 11 5-psi (i+1)) at hh
  norm_num at hl hh; constructor <;> linarith

private theorem bern_eq {x : Fin 4 → ℝ} (hx : ∀ i, x i ∈ mesh i) (i : Fin 5) :
    ev x (bern i)*(ev x (edgeExp i)-1) = ev x (delta i) := by
  have hd : 0 < ev x (dropV i) := positive_of_check _ _ true hx (edgeGuards i).1
  have h : 1 < ev x (edgeExp i) := Real.one_lt_exp_iff.mpr (div_pos hd (vt_pos x))
  simp [bern, ne_of_gt (sub_pos.mpr h)]

-- Normalize the rational geometry and the common material coefficients on
-- both sides of the bridge to the generated stamp.
local macro "stamp " h:term : tactic => `(tactic|
  (have fact := $h
   norm_num [realTF, vt, qm, thick, ni, mobility, dos, psi, quasi, density, edgeCurrent,
     delta, dropV, edgeExp, upperB, lowerB] at fact ⊢ <;> exact fact))

theorem certified : Targets.Bench_14b_gt2n_gaa_nanosheet_thermal_runaway_sat realTF := by
  obtain ⟨x,hx,zero⟩ := checked_root mesh rows domain faces
  have ab : 355 ≤ ev x ambient ∧ ev x ambient ≤ 385 := by
    have lo := positive_of_check _ _ false hx auxGuards.2.1
    have hi := positive_of_check _ _ false hx auxGuards.2.2
    change 0 ≤ ev x (ambient-c 355) at lo
    change 0 ≤ ev x (c 385-ambient) at hi
    norm_num at lo hi; exact ⟨lo,hi⟩
  have node (i : Fin 4) : ev x (rows i) = 0 := zero i
  have B (i : Fin 5) : ev x (lowerB i) ≤ ev x (bern i) ∧ ev x (bern i) ≤ ev x (upperB i) :=
    ⟨sub_nonneg.mp (positive_of_check _ _ false hx (edgeGuards i).2.1),
     sub_nonneg.mp (positive_of_check _ _ false hx (edgeGuards i).2.2)⟩
  refine ⟨11/20, -(3/20), ev x ambient, 900000, 432, 6/5,
    ev x (psi 1), quasi x 1, ev x (psi 2), quasi x 2, ev x (psi 3), quasi x 3,
    ev x (psi 4), quasi x 4, ev x (edgeExp 0), ev x (bern 0), ev x (edgeExp 1), ev x (bern 1),
    ev x (edgeExp 2), ev x (bern 2), ev x (edgeExp 3), ev x (bern 3), ev x (edgeExp 4), ev x (bern 4),
    ev x (stack driveFlux), ?_⟩
  dsimp only [realTF]
  push_cast
  repeat' apply And.intro
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact ab.1
  · exact ab.2
  · norm_num
  · norm_num
  · rw [neg_div]; exact (coordinate_bounds hx 0).1
  · exact (coordinate_bounds hx 0).2
  · rw [neg_div]; exact (phi_range hx 0).1
  · exact (phi_range hx 0).2.1
  · rw [neg_div]; exact (coordinate_bounds hx 1).1
  · exact (coordinate_bounds hx 1).2
  · rw [neg_div]; exact (phi_range hx 1).1
  · exact (phi_range hx 1).2.1
  · rw [neg_div]; exact (coordinate_bounds hx 2).1
  · exact (coordinate_bounds hx 2).2
  · rw [neg_div]; exact (phi_range hx 2).1
  · exact (phi_range hx 2).2.1
  · rw [neg_div]; exact (coordinate_bounds hx 3).1
  · exact (coordinate_bounds hx 3).2
  · rw [neg_div]; exact (phi_range hx 3).1
  · exact (phi_range hx 3).2.1
  · norm_num
  · norm_num
  · norm_num
  · have h := node 0
    change ev x (poisson 1) = 0 at h
    have densityNode := density_eq hx (1 : Fin 6)
    change density x 1 = ev x (carrier 1) at densityNode
    norm_num [poisson, ← densityNode, ni, dos, thick, density, quasi, qm, vt, psi] at h ⊢
    linarith only [h]
  · have h := node 1
    change ev x (poisson 2) = 0 at h
    have densityNode := density_eq hx (2 : Fin 6)
    change density x 2 = ev x (carrier 2) at densityNode
    norm_num [poisson, ← densityNode, ni, dos, thick, density, quasi, qm, vt, psi] at h ⊢
    linarith only [h]
  · have h := node 2
    change ev x (poisson 3) = 0 at h
    have densityNode := density_eq hx (3 : Fin 6)
    change density x 3 = ev x (carrier 3) at densityNode
    norm_num [poisson, ← densityNode, ni, dos, thick, density, quasi, qm, vt, psi] at h ⊢
    linarith only [h]
  · have h := node 3
    change ev x (poisson 4) = 0 at h
    have densityNode := density_eq hx (4 : Fin 6)
    change density x 4 = ev x (carrier 4) at densityNode
    norm_num [poisson, ← densityNode, ni, dos, thick, density, quasi, qm, vt, psi] at h ⊢
    linarith only [h]
  · exact Real.exp_pos _
  · stamp (show ev x (edgeExp 0) = Real.exp (ev x (delta 0)) from rfl)
  · stamp bern_eq hx (0 : Fin 5)
  · stamp (B 0).1
  · stamp (B 0).2
  · exact Real.exp_pos _
  · stamp (show ev x (edgeExp 1) = Real.exp (ev x (delta 1)) from rfl)
  · stamp bern_eq hx (1 : Fin 5)
  · stamp (B 1).1
  · stamp (B 1).2
  · exact Real.exp_pos _
  · stamp (show ev x (edgeExp 2) = Real.exp (ev x (delta 2)) from rfl)
  · stamp bern_eq hx (2 : Fin 5)
  · stamp (B 2).1
  · stamp (B 2).2
  · exact Real.exp_pos _
  · stamp (show ev x (edgeExp 3) = Real.exp (ev x (delta 3)) from rfl)
  · stamp bern_eq hx (3 : Fin 5)
  · stamp (B 3).1
  · stamp (B 3).2
  · exact Real.exp_pos _
  · stamp (show ev x (edgeExp 4) = Real.exp (ev x (delta 4)) from rfl)
  · stamp bern_eq hx (4 : Fin 5)
  · stamp (B 4).1
  · stamp (B 4).2
  · stamp (constant_current hx (1 : Fin 5)).trans (constant_current hx (0 : Fin 5)).symm
  · stamp (constant_current hx (2 : Fin 5)).trans (constant_current hx (1 : Fin 5)).symm
  · stamp (constant_current hx (3 : Fin 5)).trans (constant_current hx (2 : Fin 5)).symm
  · stamp (constant_current hx (4 : Fin 5)).trans (constant_current hx (3 : Fin 5)).symm
  · stamp (constant_current hx (4 : Fin 5)).symm
  · norm_num [ambient]
  · norm_num

end SpiceSmtBench.GaaCertificate
