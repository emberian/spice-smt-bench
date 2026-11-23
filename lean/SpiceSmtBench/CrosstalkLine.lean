import SpiceSmtBench.StoredEnergy
import SpiceSmtBench.RealPhysics

namespace SpiceSmtBench.Crosstalk
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
  ![(1/2)*(p.cp*(1-p.k)+p.cm), 0, -((1/2)*p.cm), (1/2)*(p.cp*(1-p.k)+p.cm)+(1/500000000000), (1/2)*(p.cn*(1-p.k)+p.cm), (1/2)*(p.cn*(1-p.k)+p.cm)+(1/400000000000), 1*(p.cn*(1-p.k)+p.cm), -(1*p.cm), 1*(p.cp*(1-p.k)+p.cm), (p.lp+p.via)/2500, p.lm/2500, (p.ln+p.via)/2500, (p.lp)/2500, (p.ln)/2500]

@[simp] def massIndex : Fin 14 → Fin 14 → Fin 14 :=
  ![![0, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![2, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 6, 1, 7, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 6, 1, 7, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 7, 1, 8, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 7, 1, 8, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 9, 10, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 10, 11, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12, 10, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 13, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12, 10],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 13]]

def mass (p : Line) : Coeff 14 := fun i j => massValues p (massIndex i j)

private theorem index_symmetric : ∀ i j : Fin 14, massIndex i j=massIndex j i := by decide +kernel

theorem mass_symmetric (p : Line) (i j : Fin 14) : mass p i j=mass p j i :=
  congrArg (massValues p) (index_symmetric i j)

def network (p : Line) : Coeff 14 :=
  ![![-50/28, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    ![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0],
    ![1, 0, 0, 0, 0, 0, -1, 0, -p.r/50, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, -1, 0, 0, 0, 0, -p.r/50, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, -1, 0, 0, -p.r/50, 0, 0, 0],
    ![0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, -p.r/50, 0, 0],
    ![0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -p.r/50, 0],
    ![0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, -p.r/50]]

def port (u d : ℝ) : State 14 :=
  ![(6/5)*(u*50/28), 0, 0, (6/5)*50*d, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def coordinates (s : State 14) : State 14 :=
  ![s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7, 50*s 8, 50*s 9, 50*s 10, 50*s 11, 50*s 12, 50*s 13]

theorem coordinate_delta (x y r : State 14) (t : ℝ) (h : ∀ j, y j=x j+t*r j) (i : Fin 14) :
    coordinates y i - coordinates x i = t*coordinates r i := by
  fin_cases i <;> simp [coordinates,h] <;> ring

def halfStep : ℝ := 6/5

def metric (p : Line) (i j : Fin 14) := (10:ℝ)^12 * mass p i j
end
end SpiceSmtBench.Crosstalk
