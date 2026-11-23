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
#print axioms bench08_ring_envelope_proved
#print axioms bench10_esd_crosstalk_proved
#print axioms bench11_pdn_droop_proved
#print axioms bench12a_split_plane_bounce_proved
#print axioms bench12b_stitched_return_proved
#print axioms bench13_finfet_leakage_proved
#print axioms bench14a_gaa_thermal_safety_proved
#print axioms bench14b_gaa_thermal_excursion_proved

/-- Fail the audit if a generated target lacks a real proof or a published real
proof gains an axiom outside Lean's standard three. -/
private def checkRealProofs : Lean.CoreM Unit := do
  let env ← Lean.getEnv
  let declarations (moduleName : Lean.Name) : Lean.CoreM (Array Lean.Name) := do
    let some idx := env.getModuleIdx? moduleName | throwError "missing audit input {moduleName}"
    return env.header.moduleData[idx.toNat]!.constNames
  let generated := (← declarations `SpiceSmtBench.TargetsGenerated).filter fun name =>
    name.getPrefix == `SpiceSmtBench.Targets && name.getString!.startsWith "Bench_"
  let proofs := env.constants.foldStage2 (fun acc name _ => acc.push name) (← declarations `SpiceSmtBench.Targets)
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut covered : Lean.NameSet := {}
  for name in proofs do
    let info ← Lean.getConstInfo name
    if !info.isTheorem then continue
    let .app head interpretation := info.type | continue
    let some target := head.getAppFn.constName? | continue
    if !interpretation.isConstOf ``realTF || !generated.contains target then continue
    let extra := (← Lean.collectAxioms name).filter fun axiomName => !allowed.contains axiomName
    unless extra.isEmpty do throwError "{name} uses unexpected axioms {extra}"
    covered := covered.insert target
  let missing := generated.filter fun target => !covered.contains target
  unless !generated.isEmpty && missing.isEmpty do throwError "real proof coverage failed: {missing}"
  Lean.logInfo m!"Verified standard-axiom proofs for {covered.size}/{generated.size} generated targets over ℝ."

run_cmd Lean.Elab.Command.liftCoreM checkRealProofs

end SpiceSmtBench.Targets.Audit
