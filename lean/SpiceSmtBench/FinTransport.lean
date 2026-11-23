import SpiceSmtBench.FinMesh
import SpiceSmtBench.SgConductance
import SpiceSmtBench.BoxCertificate

namespace SpiceSmtBench.FinTransport
open FinMesh SgConductance IntervalCheck BoxCertificate

def kb : ℚ := 4308666631/50000000000000
def beta : ℚ := 6498530148177529/1000000000000
def ambientInv : ℚ := 6666666666666667/2000000000000000000
def areaFactor : ℚ := 5333333333333333/500000000000000
def charge : ℚ := 801088317/50000000000000000000000000
def wall (j : Nat) : ℚ := if j=1 then 1 else 27/20
noncomputable def activation (t : ℝ) := (beta:ℝ)*((ambientInv:ℝ)-1/t)
noncomputable def shift (tfin : ℝ) (j : Nat) := (wall j : ℝ)*((8357/10000)/(tfin*tfin))
noncomputable def arg (v t tfin : ℝ) (j : Nat) := activation t + (v-shift tfin j)/((kb:ℝ)*t)

def peak (i j : Nat) : ℚ :=
  beta*(ambientInv-1/360)+(barrier i j-wall j*(8357/10000)/(7*7))/(kb*360)
def scaleMax : ℚ := charge*10000000000*300*(7*areaFactor/(64+7))*(kb*360)/(99/20)
noncomputable def scale (t tfin dx : ℝ) :=
  (charge:ℝ)*10000000000*300*(tfin*(areaFactor:ℝ)/(64+tfin))*((kb:ℝ)*t)/dx

theorem scale_bound {t tfin dx : ℝ} (tp : 0 < t) (th : t ≤ 360) (tl : 0 < tfin)
    (tw : tfin ≤ 7) (dl : 99/20 ≤ dx) : 0 < scale t tfin dx ∧ scale t tfin dx ≤ (scaleMax:ℝ) := by
  have w : tfin*(areaFactor:ℝ)/(64+tfin) ≤ 7*(areaFactor:ℝ)/(64+7) := (div_le_iff₀ (by positivity)).2 (by norm_num [areaFactor]; linarith)
  have den : 0 < dx := by linarith
  have hk : 0 < (kb : ℝ) := by norm_num [kb]
  have hc : 0 < (charge : ℝ) := by norm_num [charge]
  have ha : 0 < (areaFactor : ℝ) := by norm_num [areaFactor]
  constructor
  · dsimp [scale,charge,areaFactor,kb]; norm_num; positivity
  · dsimp [scaleMax,scale]; push_cast
    apply div_le_div₀ _ _ (by norm_num) dl
    · positivity
    · apply mul_le_mul _ (mul_le_mul_of_nonneg_left th (by norm_num [kb])) (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left w (by norm_num [charge])

theorem peak_bound {p t tf : ℝ} {i j : Nat} (hp : p ≤ W i j) (small : barrier i j ≤ 1/5)
    (tp : 0 < t) (th : t ≤ 360) (fp : 0 < tf) (fh : tf ≤ 7) : arg p t tf j ≤ (peak i j : ℝ) := by
  have kpos : 0 < (kb:ℝ) := by norm_num [kb]
  have wallPos : 0 ≤ (wall j : ℝ) := by unfold wall; split <;> norm_num
  let Q := (wall j:ℝ)*(8357/10000)/(7*7)
  have qpos : 0 ≤ Q := by dsimp [Q]; positivity
  have qlo : Q ≤ shift tf j := by
    dsimp [shift,Q]; rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by norm_num)
      (mul_pos fp fp) (mul_self_le_mul_self fp.le fh)) wallPos
  have num : p-shift tf j ≤ W i j-Q := by linarith
  have sub : (W i j-Q)/(kb:ℝ) ≤ (beta:ℝ) := (div_le_iff₀ kpos).2 (by
    have h : W i j ≤ 1/5 := by simpa [W] using (Rat.cast_le (K := ℝ)).mpr small
    norm_num [kb,beta]; linarith)
  have monot := div_le_div_of_nonneg_left (sub_nonneg.mpr sub) tp th
  unfold arg activation peak
  push_cast
  change _ ≤ (beta:ℝ)*((ambientInv:ℝ)-1/360)+(W i j-Q)/((kb:ℝ)*360)
  calc
    _ ≤ (beta:ℝ)*((ambientInv:ℝ)-1/t)+(W i j-Q)/((kb:ℝ)*t) :=
      add_le_add_right (div_le_div_of_nonneg_right num (mul_pos kpos tp).le) _
    _ = (beta:ℝ)*ambientInv - ((beta:ℝ)-(W i j-Q)/kb)/t := by ring
    _ ≤ (beta:ℝ)*ambientInv - ((beta:ℝ)-(W i j-Q)/kb)/360 := by linarith only [monot]
    _ = _ := by ring

-- The SG conductance at each comparison edge is evaluated only at the two
-- upper endpoint potentials. Either orientation gives a positive denominator.
private def qc (q : ℚ) : PExpr := .const ⟨q.num,q.den,q.den_pos⟩
private def endpointG (a b : ℚ) : PExpr :=
  if a < b then .div (qc (b-a)) (.sub (.exp (qc (-a))) (.exp (qc (-b))))
  else .div (qc (a-b)) (.sub (.exp (qc (-b))) (.exp (qc (-a))))
private def edgeSum (i : Nat) :=
  let g j := endpointG (peak i j) (peak (i+1) j)
  PExpr.mul (qc scaleMax) (.add (.add (g 0) (g 1)) (g 2))

private theorem qc_eval (q : ℚ) (ρ : Nat → ℝ) : (qc q).eval realTF ρ = (q:ℝ) := by
  simp [qc,PExpr.eval,QRat.eval,realTF,Rat.cast_def]
private theorem g_eval (a b : ℚ) (neq : a ≠ b) (ρ : Nat → ℝ) :
    (endpointG a b).eval realTF ρ = conductance a b := by
  rw [formula (by exact_mod_cast neq)]
  unfold endpointG
  split
  · change (qc (b-a)).eval realTF ρ / (Real.exp ((qc (-a)).eval realTF ρ) - Real.exp ((qc (-b)).eval realTF ρ)) = _
    simp [qc_eval]
  · change (qc (a-b)).eval realTF ρ / (Real.exp ((qc (-b)).eval realTF ρ) - Real.exp ((qc (-a)).eval realTF ρ)) = _
    simp only [qc_eval,Rat.cast_sub,Rat.cast_neg]
    rw [← neg_sub (b:ℝ) a, ← neg_sub (Real.exp (-(a:ℝ))) (Real.exp (-(b:ℝ))),neg_div_neg_eq]

private theorem g_bound (i : Nat) (bound : ℚ) (neq : ∀ j : Fin 3, peak i j ≠ peak (i+1) j)
    (ok : checkPositive (n := 0) (fun _ => .singleton 0) (.sub (qc bound) (edgeSum i)) false) :
    let g j := conductance (peak i j) (peak (i+1) j)
    (scaleMax:ℝ)*((g 0+g 1)+g 2) ≤ (bound:ℝ) := by
  let x : Fin 0 → ℝ := Fin.elim0
  have h := positive_of_check _ _ false (x := x) (fun i => Fin.elim0 i) ok
  change 0 ≤ (qc bound).eval realTF (values x) - (qc scaleMax).eval realTF (values x)*
    (((endpointG (peak i 0) (peak (i+1) 0)).eval realTF (values x) + _) + _) at h
  have N (j : Nat) (hj : j < 3 := by decide) : peak i j ≠ peak (i+1) j := neq ⟨j,hj⟩
  simpa only [qc_eval,g_eval _ _ (N 0),g_eval _ _ (N 1),g_eval _ _ (N 2),sub_nonneg] using h

set_option maxRecDepth 16000 in
theorem two_edges :
    let g (i j : Nat) := conductance (peak i j) (peak (i+1) j)
    (scaleMax:ℝ)*((g 1 0+g 1 1)+g 1 2) ≤ 12/1000000 ∧
    (scaleMax:ℝ)*((g 2 0+g 2 1)+g 2 2) ≤ 34/1000000 := by
  constructor
  · simpa using g_bound 1 (12/1000000) (by decide +kernel) (by decide +kernel)
  · simpa using g_bound 2 (34/1000000) (by decide +kernel) (by decide +kernel)

-- Gauge transform of one stamped transverse quadrature contribution. The
-- quasi-Fermi drop is common to all three transverse nodes at an axial edge.
theorem flux {a b l r act vt w : ℝ}
    (eqn : w*(Real.exp ((b-a)/vt)-1)=(b-a)/vt)
    (neutral : (b-a)/vt=0 → w=1) :
    Real.exp act*(w*Real.exp ((b-a)/vt)*Real.exp ((a-l)/vt) - w*Real.exp ((b-r)/vt)) =
    conductance (act+a/vt) (act+b/vt) * (Real.exp (-l/vt)-Real.exp (-r/vt)) := by
  have diff : (act+b/vt)-(act+a/vt) = (b-a)/vt := by ring
  have h := bernoulli (a := act+a/vt) (b := act+b/vt) (w := w) (by rw [diff]; exact eqn)
    (fun he => neutral (by rw [← diff, he,sub_self]))
  have fwd : Real.exp act * (w * Real.exp ((b-a)/vt) * Real.exp ((a-l)/vt)) =
      (w*Real.exp (act+b/vt))*Real.exp (-l/vt) := by
    calc
      _ = w*(Real.exp act*(Real.exp ((b-a)/vt)*Real.exp ((a-l)/vt))) := by ring
      _ = _ := by rw [← Real.exp_add,← Real.exp_add,mul_assoc,← Real.exp_add]; congr 2; ring
  have rev : Real.exp act*(w*Real.exp ((b-r)/vt)) = (w*Real.exp (act+b/vt))*Real.exp (-r/vt) := by
    calc
      _ = w*(Real.exp act*Real.exp ((b-r)/vt)) := by ring
      _ = _ := by rw [← Real.exp_add,mul_assoc,← Real.exp_add]; congr 2; ring
  rw [mul_sub,mul_sub,← h,fwd,rev]

/-- Current through the two interior edges of the comparison mesh, in µA/µm.
The same current must cross both edges, and the total normalized drop across
them is at most one for a positive source-to-drain current. -/
theorem leakage_bound {g₁ g₂ drop₁ drop₂ current : ℝ}
    (h₁ : current = g₁ * drop₁) (h₂ : current = g₂ * drop₂)
    (p₁ : 0 < g₁) (p₂ : 0 < g₂) (total : drop₁ + drop₂ ≤ 1)
    (b₁ : g₁ ≤ (scaleMax : ℝ) *
      ((conductance (peak 1 0) (peak 2 0) + conductance (peak 1 1) (peak 2 1)) +
        conductance (peak 1 2) (peak 2 2)))
    (b₂ : g₂ ≤ (scaleMax : ℝ) *
      ((conductance (peak 2 0) (peak 3 0) + conductance (peak 2 1) (peak 3 1)) +
        conductance (peak 2 2) (peak 3 2))) : current ≤ 1/100000 := by
  by_contra! fail
  have hi : 0 < current := by linarith only [fail]
  have d₁ : 0 ≤ drop₁ := le_of_lt (pos_of_mul_pos_right (h₁ ▸ hi) p₁.le)
  have d₂ : 0 ≤ drop₂ := le_of_lt (pos_of_mul_pos_right (h₂ ▸ hi) p₂.le)
  have e₁ := mul_le_mul_of_nonneg_right (b₁.trans two_edges.1) d₁
  have e₂ := mul_le_mul_of_nonneg_right (b₂.trans two_edges.2) d₂
  linarith only [h₁,h₂,total,e₁,e₂,fail]

end SpiceSmtBench.FinTransport
