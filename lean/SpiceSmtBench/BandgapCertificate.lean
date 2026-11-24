import SpiceSmtBench.BoxCertificate
import SpiceSmtBench.TargetsGenerated

/-! Low-current branch of the unguarded SiGe reference at 3 V and 300 K.
The seven coordinates are the four node voltages, both Kirk factors and
the supply current. Device assignments are reconstructed from their stamp. -/

namespace SpiceSmtBench.BandgapCertificate

open IntervalCheck BoxCertificate

private def p0 : PExpr := (.const ⟨3, 1, by decide⟩) -- vdd
private def p1 : PExpr := (.const ⟨300, 1, by decide⟩) -- temp_k
private def p2 : PExpr := (.const ⟨17, 200, by decide⟩) -- deg_ge
private def p3 : PExpr := .var 0 -- v_ref
private def p4 : PExpr := .var 1 -- v_vc1
private def p5 : PExpr := .var 2 -- v_e0
private def p6 : PExpr := .var 3 -- v_ve2
private def p7 : PExpr := .var 4 -- skirk_Q1
private def p8 : PExpr := .var 5 -- skirk_Q2
private def p9 : PExpr := .var 6 -- i_Vsup
private def p10 : PExpr := p0 -- v_vdd
private def p11 : PExpr := (.softplus (.div (.sub (.mul (.const ⟨37, 50, by decide⟩) (.sub (.sub p10 p4) (.add (.const ⟨43, 100, by decide⟩) (.mul (.const ⟨-17, 20000, by decide⟩) (.sub p1 (.const ⟨300, 1, by decide⟩)))))) (.sub p10 p10)) (.mul (.const ⟨2, 1, by decide⟩) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))) -- y_sp_Mp1_f_1
private def p12 : PExpr := (.softplus (.div (.sub (.mul (.const ⟨37, 50, by decide⟩) (.sub (.sub p10 p4) (.add (.const ⟨43, 100, by decide⟩) (.mul (.const ⟨-17, 20000, by decide⟩) (.sub p1 (.const ⟨300, 1, by decide⟩)))))) (.sub p10 p3)) (.mul (.const ⟨2, 1, by decide⟩) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))) -- y_sp_Mp1_r_2
private def p13 : PExpr := (.neg (.mul (.const ⟨51, 12500000, by decide⟩) (.sub (.mul p11 p11) (.mul p12 p12)))) -- i_Mp1
private def p14 : PExpr := (.softplus (.div (.sub (.mul (.const ⟨37, 50, by decide⟩) (.sub (.sub p10 p4) (.add (.const ⟨43, 100, by decide⟩) (.mul (.const ⟨-17, 20000, by decide⟩) (.sub p1 (.const ⟨300, 1, by decide⟩)))))) (.sub p10 p10)) (.mul (.const ⟨2, 1, by decide⟩) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))) -- y_sp_Mp2_f_3
private def p15 : PExpr := (.softplus (.div (.sub (.mul (.const ⟨37, 50, by decide⟩) (.sub (.sub p10 p4) (.add (.const ⟨43, 100, by decide⟩) (.mul (.const ⟨-17, 20000, by decide⟩) (.sub p1 (.const ⟨300, 1, by decide⟩)))))) (.sub p10 p4)) (.mul (.const ⟨2, 1, by decide⟩) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))) -- y_sp_Mp2_r_4
private def p16 : PExpr := (.neg (.mul (.const ⟨51, 12500000, by decide⟩) (.sub (.mul p14 p14) (.mul p15 p15)))) -- i_Mp2
private def p17 : PExpr := (.sub (.sub (.mul (.div (.mul (.mul (.const ⟨1, 312500000000000000, by decide⟩) (.mul (.mul (.mul (.div p1 (.const ⟨300, 1, by decide⟩)) (.div p1 (.const ⟨300, 1, by decide⟩))) (.div p1 (.const ⟨300, 1, by decide⟩))) (.exp (.sub (.const ⟨270772089507397, 6250000000000, by decide⟩) (.div (.sub (.const ⟨28, 25, by decide⟩) p2) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))))) (.sub (.exp (.div (.sub p3 p5) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) (.const ⟨1, 1, by decide⟩))) p7) (.add (.const ⟨1, 1, by decide⟩) (.div (.sub p3 p5) (.const ⟨45, 1, by decide⟩)))) (.mul (.mul (.const ⟨1, 312500000000000000, by decide⟩) (.mul (.mul (.mul (.div p1 (.const ⟨300, 1, by decide⟩)) (.div p1 (.const ⟨300, 1, by decide⟩))) (.div p1 (.const ⟨300, 1, by decide⟩))) (.exp (.sub (.const ⟨270772089507397, 6250000000000, by decide⟩) (.div (.sub (.const ⟨28, 25, by decide⟩) p2) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))))) (.sub (.exp (.div (.sub p3 p3) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) (.const ⟨1, 1, by decide⟩)))) (.div (.mul (.mul (.const ⟨1, 312500000000000000, by decide⟩) (.mul (.mul (.mul (.div p1 (.const ⟨300, 1, by decide⟩)) (.div p1 (.const ⟨300, 1, by decide⟩))) (.div p1 (.const ⟨300, 1, by decide⟩))) (.exp (.sub (.const ⟨270772089507397, 6250000000000, by decide⟩) (.div (.sub (.const ⟨28, 25, by decide⟩) p2) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))))) (.sub (.exp (.div (.sub p3 p3) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) (.const ⟨1, 1, by decide⟩))) (.const ⟨8, 1, by decide⟩))) -- ic_Q1
private def p18 : PExpr := (.add (.div (.mul (.mul (.const ⟨1, 312500000000000000, by decide⟩) (.mul (.mul (.mul (.div p1 (.const ⟨300, 1, by decide⟩)) (.div p1 (.const ⟨300, 1, by decide⟩))) (.div p1 (.const ⟨300, 1, by decide⟩))) (.exp (.sub (.const ⟨270772089507397, 6250000000000, by decide⟩) (.div (.sub (.const ⟨28, 25, by decide⟩) p2) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))))) (.sub (.exp (.div (.sub p3 p5) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) (.const ⟨1, 1, by decide⟩))) (.const ⟨380, 1, by decide⟩)) (.div (.mul (.mul (.const ⟨1, 312500000000000000, by decide⟩) (.mul (.mul (.mul (.div p1 (.const ⟨300, 1, by decide⟩)) (.div p1 (.const ⟨300, 1, by decide⟩))) (.div p1 (.const ⟨300, 1, by decide⟩))) (.exp (.sub (.const ⟨270772089507397, 6250000000000, by decide⟩) (.div (.sub (.const ⟨28, 25, by decide⟩) p2) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))))) (.sub (.exp (.div (.sub p3 p3) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) (.const ⟨1, 1, by decide⟩))) (.const ⟨8, 1, by decide⟩))) -- ib_Q1
private def p19 : PExpr := (.sub (.sub (.mul (.div (.mul (.mul (.const ⟨1, 39062500000000000, by decide⟩) (.mul (.mul (.mul (.div p1 (.const ⟨300, 1, by decide⟩)) (.div p1 (.const ⟨300, 1, by decide⟩))) (.div p1 (.const ⟨300, 1, by decide⟩))) (.exp (.sub (.const ⟨270772089507397, 6250000000000, by decide⟩) (.div (.sub (.const ⟨28, 25, by decide⟩) p2) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))))) (.sub (.exp (.div (.sub p3 p6) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) (.const ⟨1, 1, by decide⟩))) p8) (.add (.const ⟨1, 1, by decide⟩) (.div (.sub p4 p6) (.const ⟨45, 1, by decide⟩)))) (.mul (.mul (.const ⟨1, 39062500000000000, by decide⟩) (.mul (.mul (.mul (.div p1 (.const ⟨300, 1, by decide⟩)) (.div p1 (.const ⟨300, 1, by decide⟩))) (.div p1 (.const ⟨300, 1, by decide⟩))) (.exp (.sub (.const ⟨270772089507397, 6250000000000, by decide⟩) (.div (.sub (.const ⟨28, 25, by decide⟩) p2) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))))) (.sub (.exp (.div (.sub p3 p4) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) (.const ⟨1, 1, by decide⟩)))) (.div (.mul (.mul (.const ⟨1, 39062500000000000, by decide⟩) (.mul (.mul (.mul (.div p1 (.const ⟨300, 1, by decide⟩)) (.div p1 (.const ⟨300, 1, by decide⟩))) (.div p1 (.const ⟨300, 1, by decide⟩))) (.exp (.sub (.const ⟨270772089507397, 6250000000000, by decide⟩) (.div (.sub (.const ⟨28, 25, by decide⟩) p2) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))))) (.sub (.exp (.div (.sub p3 p4) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) (.const ⟨1, 1, by decide⟩))) (.const ⟨8, 1, by decide⟩))) -- ic_Q2
private def p20 : PExpr := (.add (.div (.mul (.mul (.const ⟨1, 39062500000000000, by decide⟩) (.mul (.mul (.mul (.div p1 (.const ⟨300, 1, by decide⟩)) (.div p1 (.const ⟨300, 1, by decide⟩))) (.div p1 (.const ⟨300, 1, by decide⟩))) (.exp (.sub (.const ⟨270772089507397, 6250000000000, by decide⟩) (.div (.sub (.const ⟨28, 25, by decide⟩) p2) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))))) (.sub (.exp (.div (.sub p3 p6) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) (.const ⟨1, 1, by decide⟩))) (.const ⟨380, 1, by decide⟩)) (.div (.mul (.mul (.const ⟨1, 39062500000000000, by decide⟩) (.mul (.mul (.mul (.div p1 (.const ⟨300, 1, by decide⟩)) (.div p1 (.const ⟨300, 1, by decide⟩))) (.div p1 (.const ⟨300, 1, by decide⟩))) (.exp (.sub (.const ⟨270772089507397, 6250000000000, by decide⟩) (.div (.sub (.const ⟨28, 25, by decide⟩) p2) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))))) (.sub (.exp (.div (.sub p3 p4) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) (.const ⟨1, 1, by decide⟩))) (.const ⟨8, 1, by decide⟩))) -- ib_Q2

private def rootBox : Box 7 := ![⟨-1/1000, 1/100, by decide +kernel⟩, ⟨599/200, 601/200, by decide +kernel⟩, ⟨-9/100000, 9/100000, by decide +kernel⟩, ⟨-1/10000, 1/10000, by decide +kernel⟩, ⟨99/100, 101/100, by decide +kernel⟩, ⟨99/100, 101/100, by decide +kernel⟩, ⟨-1/1000, 1/1000, by decide +kernel⟩]
private def rows : Fin 7 → PExpr := ![(.sub (.add (.add (.add (.add p13 p17) p18) p20) (.div p3 (.const ⟨10000000, 1, by decide⟩))) (.const ⟨0, 1, by decide⟩)),
  (.sub (.add p16 p19) (.const ⟨0, 1, by decide⟩)),
  (.sub (.add (.sub (.sub (.neg p17) p18) (.div (.sub p6 p5) (.const ⟨2200, 1, by decide⟩))) (.div p5 (.const ⟨10400, 1, by decide⟩))) (.const ⟨0, 1, by decide⟩)),
  (.sub (.add (.sub (.neg p19) p20) (.div (.sub p6 p5) (.const ⟨2200, 1, by decide⟩))) (.const ⟨0, 1, by decide⟩)),
  (.sub (.mul p7 p7) (.add (.const ⟨1, 1, by decide⟩) (.div (.mul (.mul (.mul (.const ⟨1, 312500000000000000, by decide⟩) (.mul (.mul (.mul (.div p1 (.const ⟨300, 1, by decide⟩)) (.div p1 (.const ⟨300, 1, by decide⟩))) (.div p1 (.const ⟨300, 1, by decide⟩))) (.exp (.sub (.const ⟨270772089507397, 6250000000000, by decide⟩) (.div (.sub (.const ⟨28, 25, by decide⟩) p2) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))))) (.sub (.exp (.div (.sub p3 p5) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) (.const ⟨1, 1, by decide⟩))) (.mul (.mul (.const ⟨1, 312500000000000000, by decide⟩) (.mul (.mul (.mul (.div p1 (.const ⟨300, 1, by decide⟩)) (.div p1 (.const ⟨300, 1, by decide⟩))) (.div p1 (.const ⟨300, 1, by decide⟩))) (.exp (.sub (.const ⟨270772089507397, 6250000000000, by decide⟩) (.div (.sub (.const ⟨28, 25, by decide⟩) p2) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))))) (.sub (.exp (.div (.sub p3 p5) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) (.const ⟨1, 1, by decide⟩)))) (.const ⟨9, 62500, by decide⟩)))),
  (.sub (.mul p8 p8) (.add (.const ⟨1, 1, by decide⟩) (.div (.mul (.mul (.mul (.const ⟨1, 39062500000000000, by decide⟩) (.mul (.mul (.mul (.div p1 (.const ⟨300, 1, by decide⟩)) (.div p1 (.const ⟨300, 1, by decide⟩))) (.div p1 (.const ⟨300, 1, by decide⟩))) (.exp (.sub (.const ⟨270772089507397, 6250000000000, by decide⟩) (.div (.sub (.const ⟨28, 25, by decide⟩) p2) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))))) (.sub (.exp (.div (.sub p3 p6) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) (.const ⟨1, 1, by decide⟩))) (.mul (.mul (.const ⟨1, 39062500000000000, by decide⟩) (.mul (.mul (.mul (.div p1 (.const ⟨300, 1, by decide⟩)) (.div p1 (.const ⟨300, 1, by decide⟩))) (.div p1 (.const ⟨300, 1, by decide⟩))) (.exp (.sub (.const ⟨270772089507397, 6250000000000, by decide⟩) (.div (.sub (.const ⟨28, 25, by decide⟩) p2) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1)))))) (.sub (.exp (.div (.sub p3 p6) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) (.const ⟨1, 1, by decide⟩)))) (.const ⟨144, 15625, by decide⟩)))),
  (.sub (.sub (.sub p9 p13) p16) (.const ⟨0, 1, by decide⟩))]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 300000 in
theorem certified : Targets.Bench_04a_ihp_sige_bandgap_trojan_sat realTF := by
  obtain ⟨x,hx,hr⟩ := checked_root rootBox rows (by decide +kernel) (by decide +kernel)
  refine ⟨p0.eval realTF (values x), p1.eval realTF (values x), p2.eval realTF (values x), p10.eval realTF (values x), p9.eval realTF (values x), p3.eval realTF (values x), p4.eval realTF (values x), p11.eval realTF (values x), p12.eval realTF (values x), p13.eval realTF (values x), p14.eval realTF (values x), p15.eval realTF (values x), p16.eval realTF (values x), p5.eval realTF (values x), p7.eval realTF (values x), p17.eval realTF (values x), p18.eval realTF (values x), p6.eval realTF (values x), p8.eval realTF (values x), p19.eval realTF (values x), p20.eval realTF (values x), ?_⟩
  simp only [realTF.zero_eq_ofRat, realTF.one_eq_ofRat, realTF.ofInt_eq_ofRat]
  repeat' apply And.intro
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub p0 (.const ⟨27, 10, by decide⟩)) false hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub (.const ⟨33, 10, by decide⟩) p0) false hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub p1 (.const ⟨273, 1, by decide⟩)) false hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub (.const ⟨373, 1, by decide⟩) p1) false hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub p2 (.const ⟨2, 25, by decide⟩)) false hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub (.const ⟨9, 100, by decide⟩) p2) false hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub p10 (.const ⟨-1, 10, by decide⟩)) false hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub (.const ⟨18, 5, by decide⟩) p10) false hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub p3 (.const ⟨-1, 20, by decide⟩)) false hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub (.const ⟨8, 5, by decide⟩) p3) false hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub p4 (.const ⟨-1, 10, by decide⟩)) false hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub (.const ⟨18, 5, by decide⟩) p4) false hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub p5 (.const ⟨-1, 10, by decide⟩)) false hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub (.const ⟨18, 5, by decide⟩) p5) false hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub p6 (.const ⟨-1, 10, by decide⟩)) false hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub (.const ⟨18, 5, by decide⟩) p6) false hx (by decide +kernel))
  · exact rfl
  · exact sub_pos.mp (positive_of_check rootBox (.sub p1 (.const ⟨0, 1, by decide⟩)) true hx (by decide +kernel))
  · exact sub_pos.mp (positive_of_check rootBox (.sub (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1) (.const ⟨0, 1, by decide⟩)) true hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub p11 (.const ⟨0, 1, by decide⟩)) false hx (by decide +kernel))
  · exact exp_softplus (((.div (.sub (.mul (.const ⟨37, 50, by decide⟩) (.sub (.sub p10 p4) (.add (.const ⟨43, 100, by decide⟩) (.mul (.const ⟨-17, 20000, by decide⟩) (.sub p1 (.const ⟨300, 1, by decide⟩)))))) (.sub p10 p10)) (.mul (.const ⟨2, 1, by decide⟩) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) : PExpr).eval realTF (values x))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub p12 (.const ⟨0, 1, by decide⟩)) false hx (by decide +kernel))
  · exact exp_softplus (((.div (.sub (.mul (.const ⟨37, 50, by decide⟩) (.sub (.sub p10 p4) (.add (.const ⟨43, 100, by decide⟩) (.mul (.const ⟨-17, 20000, by decide⟩) (.sub p1 (.const ⟨300, 1, by decide⟩)))))) (.sub p10 p3)) (.mul (.const ⟨2, 1, by decide⟩) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) : PExpr).eval realTF (values x))
  · exact rfl
  · exact sub_pos.mp (positive_of_check rootBox (.sub p1 (.const ⟨0, 1, by decide⟩)) true hx (by decide +kernel))
  · exact sub_pos.mp (positive_of_check rootBox (.sub (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1) (.const ⟨0, 1, by decide⟩)) true hx (by decide +kernel))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub p14 (.const ⟨0, 1, by decide⟩)) false hx (by decide +kernel))
  · exact exp_softplus (((.div (.sub (.mul (.const ⟨37, 50, by decide⟩) (.sub (.sub p10 p4) (.add (.const ⟨43, 100, by decide⟩) (.mul (.const ⟨-17, 20000, by decide⟩) (.sub p1 (.const ⟨300, 1, by decide⟩)))))) (.sub p10 p10)) (.mul (.const ⟨2, 1, by decide⟩) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) : PExpr).eval realTF (values x))
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub p15 (.const ⟨0, 1, by decide⟩)) false hx (by decide +kernel))
  · exact exp_softplus (((.div (.sub (.mul (.const ⟨37, 50, by decide⟩) (.sub (.sub p10 p4) (.add (.const ⟨43, 100, by decide⟩) (.mul (.const ⟨-17, 20000, by decide⟩) (.sub p1 (.const ⟨300, 1, by decide⟩)))))) (.sub p10 p4)) (.mul (.const ⟨2, 1, by decide⟩) (.mul (.const ⟨4308666631, 50000000000000, by decide⟩) p1))) : PExpr).eval realTF (values x))
  · exact rfl
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub p7 (.const ⟨0, 1, by decide⟩)) false hx (by decide +kernel))
  · exact (sub_eq_zero.mp (hr 4))
  · exact rfl
  · exact rfl
  · exact sub_nonneg.mp (positive_of_check rootBox (.sub p8 (.const ⟨0, 1, by decide⟩)) false hx (by decide +kernel))
  · exact (sub_eq_zero.mp (hr 5))
  · exact rfl
  · exact rfl
  · exact (sub_eq_zero.mp (hr 2))
  · exact (sub_eq_zero.mp (hr 0))
  · exact (sub_eq_zero.mp (hr 1))
  · exact (sub_eq_zero.mp (hr 6))
  · exact (sub_eq_zero.mp (hr 3))
  · exact sub_pos.mp (positive_of_check rootBox (.sub (.const ⟨3, 20, by decide⟩) p3) true hx (by decide +kernel))

end SpiceSmtBench.BandgapCertificate
