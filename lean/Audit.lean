import SpiceSmtBench.Targets

/-! Axiom dependencies of the published target proofs specialized to the reals. -/

namespace SpiceSmtBench.Targets.Audit

private theorem bench01_diode_clipper_pvt_proved_real : Bench_01_diode_clipper_pvt realTF :=
  bench01_diode_clipper_pvt_proved realTF
#print axioms bench01_diode_clipper_pvt_proved_real

private theorem bench01_paving_certificate_proved_real : Bench_01_diode_clipper_pvt realTF :=
  bench01_paving_certificate_proved realTF
#print axioms bench01_paving_certificate_proved_real

private theorem bench06_rc_diode_glitch_filter_proved_real : Bench_06_rc_diode_glitch_filter_ode realTF :=
  bench06_rc_diode_glitch_filter_proved realTF
#print axioms bench06_rc_diode_glitch_filter_proved_real

private theorem bench09a_pcb_microstrip_dfm_proved_real : Bench_09a_pcb_microstrip_dfm_unsat realTF :=
  bench09a_pcb_microstrip_dfm_proved realTF
#print axioms bench09a_pcb_microstrip_dfm_proved_real

#print axioms bench02_asap7_inverter_snm_proved
#print axioms bench03a_asap7_sram_read_margin_proved
#print axioms bench05_cmos_scr_latchup_holding_proved
#print axioms bench09b_pcb_microstrip_overetch_proved
#print axioms bench04b_sige_bandgap_guarded_proved
#print axioms bench03b_asap7_sram_fin_collapse_proved
#print axioms bench04a_sige_bandgap_trojan_proved
#print axioms bench07_gan_soa_proved
#print axioms bench11_pdn_droop_proved
#print axioms bench14a_gaa_thermal_safety_proved
#print axioms bench14b_gaa_thermal_excursion_proved

end SpiceSmtBench.Targets.Audit
