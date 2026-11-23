import SpiceSmtBench.RealPhysics
import SpiceSmtBench.IntervalCheck

namespace SpiceSmtBench.SramCertificate
open IntervalCheck

def c (n : Int) (d : Nat := 1) (hd : 0 < d := by decide) : PExpr :=
  .const ⟨n,d,hd⟩

-- Parameters are the threshold including quantum shift, DIBL coefficient,
-- and geometry-scaled saturation current. Source and drain share the same fin.
def drive (vds vgs kappa threshold eta scale : PExpr) : PExpr :=
  let gate := PExpr.mul kappa (.sub vgs (.sub threshold (.mul eta vds)))
  let thermal := c 6463 125000
  let f := PExpr.softplus (.div gate thermal)
  let r := PExpr.softplus (.div (.sub gate vds) thermal)
  .div (.mul scale (.sub (.mul f f) (.mul r r))) (.add (c 1) (.mul (c 1 10) f))

/-- Recover the previous sample from the implicit backward-Euler equation. -/
def previous (otherSide : Bool) : PExpr :=
  let v := PExpr.var (if otherSide then 1 else 0)
  let w := PExpr.var (if otherSide then 0 else 1)
  let drop := PExpr.sub (c 7 10) v
  let pu := drive drop (.sub (c 7 10) w) (c 21 25) (.var 2)
    (.var (if otherSide then 4 else 3)) (.var 5)
  let pd := drive v w (c 17 20) (.var (if otherSide then 7 else 6))
    (.var (if otherSide then 9 else 8)) (.var (if otherSide then 11 else 10))
  let pg := drive drop drop (c 17 20) (c 8 25)
    (.var (if otherSide then 13 else 12)) (c 2517857142857143 2500000000000000000000)
  .sub v (.mul (c 1 100000000000) (.div (.add (.sub pu pd) pg) (c 1 1000000000000000)))

private def constraints (lowQ : Bool) : List PConstraint :=
  [(if lowQ then (.gtZero, .sub (c 29 50) (.var 0)) else (.gtZero, .sub (.var 1) (c 1 5))),
   (.geZero, .sub (previous false) (c 29 50)),
   (.geZero, .sub (c 1 5) (previous true))]

def range (l u : Int) (d : Nat) (hd : 0 < d := by decide) : QInterval := ⟨⟨l,d,hd⟩,⟨u,d,hd⟩⟩

def rootBox : List QInterval :=
  [range (-1) 16 20, range (-1) 16 20,
   range 327 333 1000, range 4 7 100, range 4 7 100, range 86 89 100000000,
   range 317 323 1000, range 302 338 1000, range 4 7 100, range 4 7 100,
   range 199 204 100000000, range 199 204 100000000, range 4 7 100, range 4 7 100]

private def tree : PavingTree :=
    (.split 0 ⟨29, 50, by decide⟩
    (.split 1 ⟨1, 5, by decide⟩
    (.split 0 ⟨53, 200, by decide⟩ (.leaf 1)
    (.split 0 ⟨169, 400, by decide⟩ (.leaf 1)
    (.split 1 ⟨3, 40, by decide⟩
    (.split 0 ⟨401, 800, by decide⟩ (.leaf 1)
    (.split 1 ⟨1, 80, by decide⟩
    (.split 0 ⟨173, 320, by decide⟩ (.leaf 1)
    (.split 1 ⟨-3, 160, by decide⟩ (.leaf 1) (.leaf 1)))
    (.split 0 ⟨173, 320, by decide⟩ (.leaf 1)
    (.split 1 ⟨7, 160, by decide⟩ (.leaf 1)
    (.split 0 ⟨1793, 3200, by decide⟩ (.leaf 1)
    (.split 1 ⟨19, 320, by decide⟩ (.leaf 1) (.leaf 1)))))))
    (.split 0 ⟨401, 800, by decide⟩ (.leaf 1)
    (.split 1 ⟨11, 80, by decide⟩
    (.split 0 ⟨173, 320, by decide⟩ (.leaf 1)
    (.split 1 ⟨17, 160, by decide⟩
    (.split 0 ⟨1793, 3200, by decide⟩ (.leaf 1)
    (.split 1 ⟨29, 320, by decide⟩ (.leaf 1) (.leaf 1)))
    (.split 0 ⟨1793, 3200, by decide⟩ (.leaf 1)
    (.split 1 ⟨39, 320, by decide⟩ (.leaf 1) (.leaf 1)))))
    (.split 0 ⟨173, 320, by decide⟩ (.leaf 1)
    (.split 1 ⟨27, 160, by decide⟩
    (.split 0 ⟨1793, 3200, by decide⟩ (.leaf 1)
    (.split 1 ⟨49, 320, by decide⟩ (.leaf 1)
    (.split 0 ⟨3649, 6400, by decide⟩ (.leaf 1)
    (.split 1 ⟨103, 640, by decide⟩ (.leaf 1) (.leaf 1)))))
    (.split 0 ⟨1793, 3200, by decide⟩ (.leaf 1)
    (.split 1 ⟨59, 320, by decide⟩
    (.split 0 ⟨3649, 6400, by decide⟩ (.leaf 1)
    (.split 1 ⟨113, 640, by decide⟩ (.leaf 1) (.leaf 1)))
    (.split 0 ⟨3649, 6400, by decide⟩ (.leaf 1)
    (.split 1 ⟨123, 640, by decide⟩
    (.split 0 ⟨7361, 12800, by decide⟩ (.leaf 1)
    (.split 1 ⟨241, 1280, by decide⟩ (.leaf 1) (.leaf 1)))
    (.split 0 ⟨7361, 12800, by decide⟩ (.leaf 1)
    (.split 1 ⟨251, 1280, by decide⟩ (.leaf 1)
    (.split 0 ⟨2957, 5120, by decide⟩ (.leaf 1)
    (.split 1 ⟨507, 2560, by decide⟩ (.leaf 1) (.leaf 1))))))))))))))))
    (.split 0 ⟨53, 200, by decide⟩
    (.split 1 ⟨1, 2, by decide⟩
    (.split 0 ⟨43, 400, by decide⟩ (.leaf 1)
    (.split 1 ⟨7, 20, by decide⟩ (.leaf 1)
    (.split 0 ⟨149, 800, by decide⟩ (.leaf 1)
    (.split 1 ⟨17, 40, by decide⟩ (.leaf 1) (.leaf 1)))))
    (.split 0 ⟨43, 400, by decide⟩
    (.split 1 ⟨13, 20, by decide⟩
    (.split 0 ⟨23, 800, by decide⟩ (.leaf 1)
    (.split 1 ⟨23, 40, by decide⟩ (.leaf 1) (.leaf 1))) (.leaf 2)) (.leaf 2)))
    (.split 1 ⟨1, 2, by decide⟩
    (.split 0 ⟨169, 400, by decide⟩
    (.split 1 ⟨7, 20, by decide⟩ (.leaf 1) (.leaf 2))
    (.split 1 ⟨7, 20, by decide⟩
    (.split 0 ⟨401, 800, by decide⟩
    (.split 1 ⟨11, 40, by decide⟩ (.leaf 1)
    (.split 0 ⟨739, 1600, by decide⟩ (.leaf 1) (.leaf 2)))
    (.split 1 ⟨11, 40, by decide⟩
    (.split 0 ⟨173, 320, by decide⟩ (.leaf 1)
    (.split 1 ⟨19, 80, by decide⟩
    (.split 0 ⟨1793, 3200, by decide⟩ (.leaf 1)
    (.split 1 ⟨7, 32, by decide⟩
    (.split 0 ⟨3649, 6400, by decide⟩ (.leaf 1)
    (.split 1 ⟨67, 320, by decide⟩
    (.split 0 ⟨7361, 12800, by decide⟩ (.leaf 1)
    (.split 1 ⟨131, 640, by decide⟩
    (.split 0 ⟨2957, 5120, by decide⟩ (.leaf 1)
    (.split 1 ⟨259, 1280, by decide⟩
    (.split 0 ⟨29633, 51200, by decide⟩ (.leaf 1)
    (.split 1 ⟨103, 512, by decide⟩ (.leaf 1) (.leaf 1))) (.leaf 2))) (.leaf 2))) (.leaf 2))) (.leaf 2))) (.leaf 2))) (.leaf 2))) (.leaf 2))) (.leaf 2))))
    (.split 1 ⟨1, 5, by decide⟩ (.leaf 0)
    (.split 1 ⟨1, 2, by decide⟩
    (.split 1 ⟨7, 20, by decide⟩
    (.split 0 ⟨69, 100, by decide⟩
    (.split 1 ⟨11, 40, by decide⟩
    (.split 0 ⟨127, 200, by decide⟩
    (.split 1 ⟨19, 80, by decide⟩
    (.split 0 ⟨243, 400, by decide⟩
    (.split 1 ⟨7, 32, by decide⟩
    (.split 0 ⟨19, 32, by decide⟩
    (.split 1 ⟨67, 320, by decide⟩
    (.split 0 ⟨939, 1600, by decide⟩
    (.split 1 ⟨131, 640, by decide⟩
    (.split 0 ⟨1867, 3200, by decide⟩
    (.split 1 ⟨259, 1280, by decide⟩
    (.split 0 ⟨3723, 6400, by decide⟩
    (.split 1 ⟨103, 512, by decide⟩
    (.split 0 ⟨1487, 2560, by decide⟩
    (.split 1 ⟨1027, 5120, by decide⟩
    (.split 0 ⟨14859, 25600, by decide⟩ (.leaf 1) (.leaf 2)) (.leaf 2)) (.leaf 2)) (.leaf 2))
    (.split 1 ⟨103, 512, by decide⟩ (.leaf 2) (.leaf 2))) (.leaf 2))
    (.split 1 ⟨259, 1280, by decide⟩
    (.split 0 ⟨749, 1280, by decide⟩ (.leaf 2) (.leaf 2)) (.leaf 2))) (.leaf 2))
    (.split 1 ⟨131, 640, by decide⟩
    (.split 0 ⟨1889, 3200, by decide⟩ (.leaf 2) (.leaf 2)) (.leaf 2))) (.leaf 2))
    (.split 1 ⟨67, 320, by decide⟩
    (.split 0 ⟨961, 1600, by decide⟩ (.leaf 2) (.leaf 2)) (.leaf 2))) (.leaf 2))
    (.split 1 ⟨7, 32, by decide⟩
    (.split 0 ⟨497, 800, by decide⟩
    (.split 1 ⟨67, 320, by decide⟩ (.leaf 2) (.leaf 2)) (.leaf 2)) (.leaf 2))) (.leaf 2))
    (.split 1 ⟨19, 80, by decide⟩
    (.split 0 ⟨53, 80, by decide⟩
    (.split 1 ⟨7, 32, by decide⟩
    (.split 0 ⟨519, 800, by decide⟩ (.leaf 2) (.leaf 2)) (.leaf 2)) (.leaf 2)) (.leaf 2))) (.leaf 2))
    (.split 1 ⟨11, 40, by decide⟩
    (.split 0 ⟨149, 200, by decide⟩
    (.split 1 ⟨19, 80, by decide⟩
    (.split 0 ⟨287, 400, by decide⟩ (.leaf 2) (.leaf 2)) (.leaf 2))
    (.split 1 ⟨19, 80, by decide⟩
    (.split 0 ⟨309, 400, by decide⟩ (.leaf 2) (.leaf 2)) (.leaf 2))) (.leaf 2))) (.leaf 2)) (.leaf 2))))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private theorem checked (lowQ : Bool) :
    verifyPaving (checkConcreteLeaf (constraints lowQ)) tree rootBox = true := by
  cases lowQ <;> decide +kernel

theorem invariantStep (env : Nat → ℝ)
    (box : memBox realTF rootBox env)
    (hq : 29/50 ≤ (previous false).eval realTF env)
    (hb : (previous true).eval realTF env ≤ 1/5) :
    29/50 ≤ env 0 ∧ env 1 ≤ 1/5 := by
  have reject (which : Bool) := paving_unsat_sound realTF _ _
    (checkConcreteLeaf_sound realTF (constraints which)) tree rootBox env (checked which) box
  have solve (which : Bool) (bad : (if which then env 0 < 29/50 else 1/5 < env 1)) : False := by
    apply reject which
    intro x hx
    simp only [constraints, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · cases which <;> simp_all [PCmp.holds, PExpr.eval, realTF, c, QRat.eval]
    · exact sub_nonneg.mpr hq
    · simpa [PCmp.holds, PExpr.eval, c, QRat.eval, realTF] using sub_nonneg.mpr hb
  exact ⟨le_of_not_gt (solve true), le_of_not_gt (solve false)⟩

end SpiceSmtBench.SramCertificate
