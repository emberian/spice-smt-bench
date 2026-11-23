import SpiceSmtBench.StitchedMaterial

namespace SpiceSmtBench.Stitched
open LineBounds Enclosed Microstrip StoredEnergy PolynomialEnvelope
noncomputable section

private def family (L k R via a b c : ℝ) : Line :=
  let cp := (831/500+27/500*a)/1000000000000
  let cn := (291/200+9/200*b)/1000000000000
  ⟨cp,cn,1/2*(k*(cp+cn)),L,L,1/2*(k*(L+L)),via,(17/200+9/250*c)/1000000000,k,R⟩

private def model := family (inductance substrate).val (exp (fraction (-171) 50)).val
  (resistance substrate).val (fraction 1 5000000000).val

private theorem centered_model (a b c : Enclosed) : components (centered a b c) = model a.val b.val c.val := by
  simp only [components,centered,model,family,add_val,div_val,mul_val,numeral_val]
  norm_num

private theorem material_model (ep en pitch : Enclosed) :
    let p := material ep en pitch
    components p = model (normP p).val (normN p).val (normL p).val := by
  dsimp only
  simp only [components,material,model,family,normP,normN,normL,div_val,mul_val,add_val,sub_val,numeral_val]
  congr 1 <;> ring

private theorem mass_affine (L k R via a b c : ℝ) (i j : Fin 16) :
    let m := fun u v w => metric (family L k R via u v w) i j
    m a b c = m 0 0 0 + a*(m 1 0 0-m 0 0 0)+b*(m 0 1 0-m 0 0 0)+c*(m 0 0 1-m 0 0 0) := by
  simp only [metric,mass]
  generalize massIndex i j = t
  fin_cases t <;> simp [family] <;> ring

theorem affine_metric (ep en pitch : Enclosed) (i j : Fin 16) :
    let p := material ep en pitch
    metric (components p) i j = evaluate (mon1 (normP p).val (normN p).val (normL p).val)
      (fun q => (baseMass q i j).val) := by
  dsimp only
  rw [material_model]
  simp [evaluate,mon1,Fin.sum_univ_succ,baseMass,origin,centered_model]
  unfold model
  apply (mass_affine ..).trans
  ring

theorem fixed_network (ep en pitch : Enclosed) (i j : Fin 16) :
    (baseNetwork i j).val = halfStep*network (components (material ep en pitch)) i j := by
  norm_num [baseNetwork,halfStep]
  rfl

end
end SpiceSmtBench.Stitched
