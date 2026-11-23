import SpiceSmtBench.StoredEnergy
import SpiceSmtBench.RealPhysics

namespace SpiceSmtBench.Stitched
open StoredEnergy
noncomputable section

structure Line where
  cp : ℝ
  cn : ℝ
  cm : ℝ
  lp : ℝ
  ln : ℝ
  lm : ℝ
  via : ℝ
  ret : ℝ
  k : ℝ
  r : ℝ

@[simp] def massValues (p : Line) : Fin 14 → ℝ :=
  ![1*(p.cn*(1-p.k)+p.cm), 0, -(1*p.cm), 1*(p.cp*(1-p.k)+p.cm), 3/2000000000000, (1/2)*(p.cn*(1-p.k)+p.cm), -((1/2)*p.cm), (1/2)*(p.cp*(1-p.k)+p.cm), (p.lp+p.via)/2500, p.lm/2500, (p.ln+p.via)/2500, (p.lp)/2500, (p.ln)/2500, p.ret/2500]

@[simp] def massIndex : Fin 16 → Fin 16 → Fin 14 :=
  ![![0, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 0, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![2, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 5, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 6, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 6, 7, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 9, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 10, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 9, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 12, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 9, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 12, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 13]]

def mass (p : Line) : Coeff 16 := fun i j => massValues p (massIndex i j)

private theorem index_symmetric : ∀ i j : Fin 16, massIndex i j=massIndex j i := by decide +kernel

theorem mass_symmetric (p : Line) (i j : Fin 16) : mass p i j=mass p j i :=
  congrArg (massValues p) (index_symmetric i j)

def network (p : Line) : Coeff 16 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, -1, 0, 0, 0, 1, 0, 0, -p.r/50, 0, 0, 0, 0, 0, 0],
    ![-1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -p.r/50, 0, 0, 0, 0, 0],
    ![0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, -p.r/50, 0, 0, 0, 0],
    ![1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -p.r/50, 0, 0, 0],
    ![0, 0, 0, 1, -1, 0, 0, 0, -1, 0, 0, 0, 0, -p.r/50, 0, 0],
    ![0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, -p.r/50, 0],
    ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1/5000]]

def port (u _d : ℝ) : State 16 :=
  ![0, 0, 0, 0, 0, -(1/10)*2*u, (1/10)*2*u, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def coordinates (s : State 16) : State 16 :=
  ![s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7-s 4, s 8-s 4, 50*s 9, 50*s 10, 50*s 11, 50*s 12, 50*s 13, 50*s 14, 50*s 15]

theorem coordinate_delta (x y r : State 16) (t : ℝ) (h : ∀ j, y j=x j+t*r j) (i : Fin 16) :
    coordinates y i - coordinates x i = t*coordinates r i := by
  fin_cases i <;> simp [coordinates,h] <;> ring

def halfStep : ℝ := 1/10

def metric (p : Line) (i j : Fin 16) := (10:ℝ)^12 * mass p i j
end
end SpiceSmtBench.Stitched
