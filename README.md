# `spice-smt-bench`: Multi-PDK SPICE, Continuous-Defect PCB & Nanoscale TCAD Benchmarks for Transcendental + ODE SMT and Lean 4

[![License: MIT OR Apache-2.0](https://img.shields.io/badge/License-MIT%20OR%20Apache--2.0-blue.svg)](#license)

**`spice-smt-bench`** compiles SPICE circuit netlists, **multi-PDK nanoscale transistor models** (`asap7` 7nm FinFET, `gt2n` 2nm Gate-All-Around stacked nanosheet, `ihp_sg13g2` 130nm SiGe BiCMOS HBT, `gan_sic` wide-bandgap HEMT, and `gf180mcu`/`sky130` planar CMOS), **continuous-defect PCB electromagnetic interconnects**, and **2D/electro-thermal Scharfetter–Gummel TCAD device meshes** directly into:

1. **Pure-`exp` SMT-LIB (`--dialect smt2-exp`)** — uses `ALL` by default, with an explicit `--logic` override. Transients use discrete Backward-Euler or Trapezoidal collocation and test unsafe states at every sample, including time zero. These samples do not establish continuous-time safety.
2. **Native Continuous-Time ODE SMT2 (`--dialect dreal-ode`)** — `(define-ode flow_1 ...)` + `(forall_t ...)` trajectory reachability queries over explicit nonlinear state-space flows $\dot{x} = C(x)^{-1}(Bu(t) - Gx - i_{\text{nl}}(x))$, including symbolically differentiated drive waveforms, depletion Miller $C_{gd}(v_{dg})$, and MLCC DC-bias derating $C(v)$.
3. **Lean 4 target specifications (`--dialect lean4` or `emit-lean`)** — all 19 generated propositions have a concrete interpretation over `ℝ`. Nine have complete proofs: the diode clipper (01), FinFET inverter (02), nominal and damaged SRAM (03a, 03b), guarded SiGe bandgap (04b), CMOS latchup (05), RC glitch filter (06), and both PCB microstrips (09a, 09b).

Numeric literals in both emitters denote the exact shortest-roundtrip decimal rational selected by `src/numeral.rs` from the stamped binary64 AST. Decimal input parsing and constant folding still use binary64 arithmetic. The Rust interval checker encloses exponentials using outward-rounded Taylor arithmetic and repeated squaring; it does not rely on platform transcendental accuracy. Native ODE output uses `QF_NRA_ODE`; DC input to that dialect is algebraic output under `ALL`.

After building the Lean workspace, export and replay a certificate from the repository root:

```sh
cargo run -- generate-paving benchmarks/sp/01_diode_clipper_pvt.sp v_out=0.84 i_D1=0.005 -o /tmp/Diode.lean
cargo run -- emit-witness benchmarks/sp/03b_asap7_sram_6t_fin_collapse_sat.sp -o /tmp/Collapse.lean
(cd lean && lake env lean /tmp/Diode.lean && lake env lean /tmp/Collapse.lean)
```

An existing JSON tree can be exported with `verify-paving DECK TREE.json -o TREE.lean`. Each Lean split carries its indexed variable and exact binary64 dyadic. The stamped model constants keep their decimal rational semantics. Lean checks the leaf reason on each sub-box and proves the stamped real proposition.

`emit-witness DECK name=num/den ... -o Witness.lean` accepts exact rational assignments to the parameters and solver variables of algebraic SAT decks. Omitting assignments selects the checked witnesses for 03b and 09b. For an alternative 03b trajectory at the certified damaged-fin corner, pass `--sram-boxes boxes.txt k` before `-o`. Supply 21 rows of four rational voltages (`q.lo q.hi qb.lo qb.hi`) and the zero-based failure sample `k`. The checker proves a simultaneous root of the two backward-Euler residuals at each step. The bundled witness crosses the read threshold by sample 12.

---

## Why Verify the Physics Formulation Instead of Simulator Source Code or Corner Sweeps?

Point simulators (`ngspice`, `Xyce`, `DEVSIM`) and discrete Monte Carlo corner sweeps evaluate **one initial guess at one parameter tuple at a time**:

- **Analog Startup Trojans (`04a` vs `04b`):** Self-biased bandgap and bias generators frequently possess a desired operating point $x^*_{\text{nom}}$ that Newton–Raphson converges to from default seeds—plus a **hidden zero-current Trojan equilibrium** $x^*_{\text{trojan}}$ reachable under slow power-supply ramps or cold-temperature corners. An existential/universal SMT query encodes all equilibria in the supplied continuous parameter and state boxes.
- **Anti-Sweep Continuous-Defect PCB Multiphysics (`09a`–`12b`):** High-speed board failures arise from narrow multi-parameter interactions among trapezoidal copper etch undercut $\Delta w_{\text{etch}}$, coupled gap $\Delta s$, prepreg lamination $\Delta h$, FR-4 fiber-weave skew $(\varepsilon_{r,+}, \varepsilon_{r,-})$, split return-plane slot inductance $L_{\text{slot}}$, solder-ball voiding $R_{\text{void}}$, and Class-II MLCC DC-bias capacitance collapse $C(v) = C_0 / (1 + (v/V_{\text{sat}})^2)$. Encoding the manufacturing defect polytope $\mathcal{D}_{\text{fab}} \subset \mathbb{R}^d$ symbolically replaces $10^6$-point grid sweeps with a single universal `UNSAT` proof (or exact `SAT` counterexample recipe).
- **Sub-10nm Multi-Gate Quantum & Electro-Thermal Couplings (`02`–`03b`, `08`, `13`–`14b`):** In `asap7` 7nm FinFETs and `gt2n` 2nm Gate-All-Around nanosheets, $\pm 0.5\text{ nm}$ fin/sheet thickness roughness shifts ground-subband quantum confinement $\Delta V_{\text{th,QM}} = \frac{\hbar^2 \pi^2}{2 m^* q T_{\text{body}}^2}$ and short-channel scaling length $\lambda$, while buried-oxide thermal resistance $R_{\text{th}}$ creates a coupled transcendental fixed point $T_{\text{ch}} = T_{\text{amb}} + R_{\text{th}} V_{DS} I_{DS}(V_{GS}, V_{DS}, T_{\text{ch}})$.

See [`docs/DESIGN_SPACE.md`](docs/DESIGN_SPACE.md) and [`docs/PCB_AND_TCAD_MODELS.md`](docs/PCB_AND_TCAD_MODELS.md) for full derivations and solver integration architectures.

---

## Built-In Multi-PDK Registry (`src/pdk.rs`)

`spice2smt` is **not** locked to legacy 1D planar CMOS. Every deck selects a technology profile via `.pdk <profile>` (or CLI `--pdk <profile>`):

| PDK ID | Technology Node & Geometry | Key Physical Couplings Stamped |
| :--- | :--- | :--- |
| **`asap7`** | **7nm Tri-Gate FinFET** ($L_g = 21\text{ nm}$, $T_{\text{fin}} = 6.5\text{ nm}$, $H_{\text{fin}} = 32\text{ nm}$, $\text{HfO}_2$ EOT $= 1.0\text{ nm}$; `SLVT`/`RVT`/`SRAM` workfunctions) | Subband quantum confinement $\Delta V_{\text{QM}} \propto T_{\text{fin}}^{-2}$, tri-gate scaling length $\lambda_{\text{fin}}$, exponentially coupled DIBL, 2D $(x,y)$ cross-section Poisson + SG transport |
| **`gt2n`** (`gaa2n`) | **2nm Gate-All-Around Stacked Nanosheet** ($N_{\text{sheet}} = 3$, $W_{\text{ns}} = 18\text{ nm}$, $T_{\text{ns}} = 5.0\text{ nm}$, EOT $= 0.85\text{ nm}$) | 4-sided gate wrap $\lambda_{\text{GAA}}$, inner-spacer fringing capacitance $C_{\text{isp}}(L_{\text{isp}} + \Delta L_{\text{isp}})$, coupled self-heating fixed point $T_{\text{ch}} = T_{\text{amb}} + R_{\text{th}} V_{DS} I_{\text{stack}}(T_{\text{ch}})$ |
| **`ihp_sg13g2`** | **Open 130nm SiGe BiCMOS** ($350/450\text{ GHz}$ npn SiGe HBT + 3.3V CMOS) | Graded-Ge base bandgap narrowing $\exp(\Delta E_{g,\text{Ge}} / k_B T)$, Early effect, monotone high-injection Kirk collector gain roll-off |
| **`gan_sic`** | **Wide-Bandgap GaN-on-SiC Power HEMT** ($V_{\text{bus}} = 48\text{ V}$, compact polarization-charge EKV channel) | High-$dv/dt$ nonlinear depletion Miller capacitance $C_{gd}(v) = C_{gd0}/\sqrt{1 + (v/V_{\text{bi}})^2}$ ($dQ/dt$ chain-rule stamped), dynamic SOA |
| **`gf180mcu`** | **Open 180nm Planar Bulk CMOS** (3.3V/5V I/O, ESD diodes, parasitic well/substrate BJTs) | High-current Shockley ESD clamps, parasitic pnp/npn thyristor SCR latchup holding physics |
| **`sky130`** | **Open 130nm Planar Bulk CMOS** (optional planar baseline) | All-region EKV planar MOSFETs, 1D p–n junction drift-diffusion baseline |

---

## Graded 19-Benchmark Suite (`benchmarks/sp/` & `benchmarks/smt2/`)

Every unsafe threshold and manufacturing tolerance box is verified non-vacuous in `tests/integration.rs`: all 14 `UNSAT` safety benchmarks have inhabited physical equilibria/trajectories inside their variable boxes, and all 5 `SAT` defect/Trojan twins (`03b`, `04a`, `09b`, `12a`, `14b`) have concrete numerical counterexample witnesses.

| ID | Suite | Deck (`benchmarks/sp/*.sp`) | PDK / Domain | Mode | Expected | Physical Property / Failure Mode |
| :--- | :---: | :--- | :--- | :---: | :---: | :--- |
| `01` | A | `01_diode_clipper_pvt.sp` | `gf180mcu` | DC | `unsat` | Shockley ESD diode clipper $v(\text{out}) \le 0.85\text{ V}$ over continuous $(V_{\text{sup}}, V_T)$ box (**proved in Lean 4!**) |
| `02` | A | `02_asap7_finfet_inverter_snm.sp` | `asap7` | DC | `unsat` | 7nm FinFET CMOS inverter static noise margin under $(\Delta T_{\text{fin}}, \Delta L_g, T)$ variation |
| `03a` | A | `03a_asap7_sram_6t_fin_etch_unsat.sp` | `asap7` | ODE | `unsat` | Stored-1 six-transistor SRAM read-disturb, 20 backward-Euler steps of 10 ps; $v(q)-v(qb) \ge 0.12$ V |
| `03b` | A | `03b_asap7_sram_6t_fin_collapse_sat.sp` | `asap7` | ODE | **`sat`** | Same SRAM read-disturb circuit with severe pull-down fin etch and threshold mismatch; $v(q)-v(qb) < 0.12$ V |
| `04a` | A | `04a_ihp_sige_bandgap_trojan_sat.sp` | `ihp_sg13g2` | DC | **`sat`** | Unguarded SiGe HBT bandgap reference admits hidden zero-current Trojan equilibrium $v(\text{ref}) < 0.15\text{ V}$ |
| `04b` | A | `04b_ihp_sige_bandgap_guarded_unsat.sp` | `ihp_sg13g2` | DC | `unsat` | Shared PMOS-mirror/area-ratio SiGe core plus startup diode eliminates zero-current Trojan across full PVT + $\Delta E_{g,\text{Ge}}$ box |
| `05` | A | `05_cmos_scr_latchup_holding.sp` | `gf180mcu` | DC | `unsat` | Guard-ringed pnp/npn SCR: 6–14 Ω well taps, 5–12 Ω substrate taps, 20 Ω emitter ballast; supply 0.70–0.88 V and 273–398 K. Full-box interval UNSAT without a supply-current clamp; unguarded 1.2 V twin latches |
| `06` | B | `06_rc_diode_glitch_filter_ode.sp` | `gf180mcu` | ODE | `unsat` | Nonlinear RC + ESD diode filter keeps a Gaussian fault-current pulse up to 35 mA below the 1.10 V comparator threshold (proved in Lean) |
| `07` | B | `07_gan_sic_halfbridge_shootthrough_soa_ode.sp` | `gan_sic` | ODE | `unsat` | 48V GaN-on-SiC half-bridge with depletion Miller feedback, coupled switching/gate states, and sampled gate/current/power SOA guard |
| `08` | B | `08_gt2n_gaa_ring_oscillator_3stage_ode.sp` | `gt2n` | ODE | `unsat` | 2nm GAA 3-stage ring oscillator with coupled Miller/inner-spacer capacitance; all three stage voltages remain within −0.08–0.83 V at the sampled steps |
| `09a` | C | `09a_pcb_microstrip_dfm_unsat.sp` | PCB EM | DC | `unsat` | IPC Class-3 5D fab polytope $(\Delta w, \Delta s, \Delta h, t_{\text{cu}}, \varepsilon_r)$ keeps $Z_0 \in [45, 55]\,\Omega \land Z_{\text{diff}} \in [90, 110]\,\Omega$ |
| `09b` | C | `09b_pcb_microstrip_overetch_sat.sp` | PCB EM | DC | **`sat`** | Over-etched copper + thick prepreg defect corner violates $Z_0 > 56\,\Omega$ impedance envelope |
| `10` | C | `10_pcb_coupled_trace_esd_crosstalk_ode.sp` | `gf180mcu` + PCB | ODE | `unsat` | Coupled differential trace + fiber-weave skew + via stub + receiver ESD clamp crosstalk limit |
| `11` | C | `11_pcb_pdn_mlcc_derating_droop_ode.sp` | PCB PDN | ODE | `unsat` | Voltage-derated Class-II MLCC $C(v)$ + BGA solder-void $R_{\text{void}}$ transient PDN droop envelope |
| `12a` | C | `12a_pcb_split_plane_slot_emi_sat.sp` | PCB signal integrity | ODE | **`sat`** | Split return-plane slot inductance $L_{\text{slot}}$ + fiber-weave skew induces $> 0.025\text{ V}$ ground bounce |
| `12b` | C | `12b_pcb_stitched_return_fence_unsat.sp` | PCB signal integrity | ODE | `unsat` | Stitched return-via fence keeps sampled receiver ground bounce within ±25 mV across the weave-skew box; no radiated-EMI claim |
| `13` | D | `13_asap7_finfet_2d_poisson_qconfinement.sp` | `asap7` 2D TCAD | DC | `unsat` | 7nm $5\times 3$ 2D cross-section FinFET Poisson + quantum confinement + SG off-state DIBL leakage limit of 10 pA/µm |
| `14a` | D | `14a_gt2n_gaa_nanosheet_electrothermal_unsat.sp` | `gt2n` TCAD | DC | `unsat` | 2nm 3-sheet GAA nanosheet coupled electro-thermal fixed point stays $\le 410\text{ K}$ over nominal $R_{\text{th}}$ |
| `14b` | D | `14b_gt2n_gaa_nanosheet_thermal_runaway_sat.sp` | `gt2n` TCAD | DC | **`sat`** | Degraded buried-oxide $R_{\text{th}}$ + overdrive triggers coupled electro-thermal excursion $T_{\text{ch}} > 410\text{ K}$ |

---

## Quickstart (No External Crates)

### 1. Build & Run the `spice2smt` Compiler (`std`-only Rust)

```bash
cargo test
cargo clippy --all-targets -- -D warnings

# Inspect built-in multi-PDK technology cards:
cargo run -- list-pdks

# Compile a single SPICE deck to pure-exp SMT-LIB2, native dReal ODE, or Lean 4:
cargo run -- compile benchmarks/sp/04a_ihp_sige_bandgap_trojan_sat.sp --dialect smt2-exp
cargo run -- compile benchmarks/sp/07_gan_sic_halfbridge_shootthrough_soa_ode.sp --dialect dreal-ode
cargo run -- compile benchmarks/sp/01_diode_clipper_pvt.sp --dialect lean4 --name Bench01Spec

# Override `(set-logic ...)` header for cvc5 / z3 / veriT transcendental modes:
cargo run -- compile benchmarks/sp/02_asap7_finfet_inverter_snm.sp --dialect smt2-exp --logic QF_NRAT

# Batch-regenerate all 38 SMT-LIB2 files + all 19 Lean 4 target specifications:
cargo run -- batch benchmarks/sp \
  --out-smt2-exp benchmarks/smt2/smt2-exp \
  --out-dreal-ode benchmarks/smt2/dreal-ode \
  --out-lean lean/SpiceSmtBench/TargetsGenerated.lean

# Verify an outward-rounded branch-and-bound UNSAT sub-box paving certificate:
cargo run -- verify-paving benchmarks/sp/01_diode_clipper_pvt.sp examples/diode_clipper_paving.json
```

### 2. Run Solver Queries (`dReal`, `cvc5`, `z3`)

```bash
# dReal delta-complete transcendental + ODE solver:
dreal --precision 1e-4 benchmarks/smt2/smt2-exp/04a_ihp_sige_bandgap_trojan_sat.smt2
dreal --precision 1e-3 benchmarks/smt2/dreal-ode/07_gan_sic_halfbridge_shootthrough_soa_ode.smt2

# cvc5 nonlinear transcendental real arithmetic (re-emit with --logic QF_NRAT):
cargo run -- compile benchmarks/sp/01_diode_clipper_pvt.sp --dialect smt2-exp --logic QF_NRAT -o /tmp/01_nrat.smt2
cvc5 /tmp/01_nrat.smt2
```

### 3. Build the Companion Lean 4 Proof Workspace (`lean/`)

The workspace pins Lean 4.35, Mathlib, LeanCert rational Taylor bounds, and Brouwer’s fixed-point theorem in its Lake manifest.

```bash
cd lean
lake exe cache get
lake build
```

Key Lean 4 modules:
- [`lean/SpiceSmtBench/PcbCertificate.lean`](lean/SpiceSmtBench/PcbCertificate.lean): Kernel-checked 23-box PCB paving data, regenerated by `python3 scripts/generate_pcb_certificate.py`. The script also regenerates the explicit bridge in `Targets.lean`.
- [`lean/SpiceSmtBench/PhysicsModels.lean`](lean/SpiceSmtBench/PhysicsModels.lean): `TranscendentalField R`, Shockley diode laws, pure-`exp` EKV softplus witness equivalence (`ekv_softplus_witness_nonneg`), GAA non-self-cooling theorem (`gaa_self_heating_ge_ambient`), cancellation-free Scharfetter–Gummel Bernoulli identity (`sg_cancellation_free_identity`), plus solver-synthesis Taylor targets `ExpHalfTaylor12Target` and `BernSmallTaylor10Target`.
- [`lean/SpiceSmtBench/IntervalCheck.lean`](lean/SpiceSmtBench/IntervalCheck.lean): Exact arbitrary-precision `QRat` / `QInterval` arithmetic, scaling-and-squaring `exp_ge_qrat_iterSq`, signed multiplication, positive-denominator division, rational exponential enclosures, symbolic `PExpr` evaluation, `checkConcreteLeaf_sound`, and verified branch-and-bound replay (`paving_unsat_sound`).
- [`lean/SpiceSmtBench/TargetsGenerated.lean`](lean/SpiceSmtBench/TargetsGenerated.lean): All 19 auto-generated benchmark `Prop` targets (`Bench_01_diode_clipper_pvt` through `Bench_14b_gt2n_gaa_nanosheet_thermal_runaway_sat`).
- [`RealPhysics.lean`](lean/SpiceSmtBench/RealPhysics.lean) constructs `realTF` with Mathlib, proves rational bounds on `Real.exp`, and proves the rational doubling obstruction.
- [`Targets.lean`](lean/SpiceSmtBench/Targets.lean) collects the certified benchmark propositions. [`SramCertificate.lean`](lean/SpiceSmtBench/SramCertificate.lean) checks the nominal SRAM barrier. [`SramTrajectory.lean`](lean/SpiceSmtBench/SramTrajectory.lean) connects the damaged-fin interval witness to the same stamped transistor currents.

---

## Repository Layout

```text
spice-smt-bench/
├── Cargo.toml                  # Zero-dependency Rust 2021 crate (`spice2smt`)
├── src/
│   ├── ast.rs                  # Symbolic Expr/Formula AST, waveforms, PCB/TCAD directives
│   ├── pdk.rs                  # 6-PDK registry (asap7, gt2n, ihp_sg13g2, gan_sic, gf180mcu, sky130)
│   ├── parser.rs               # SPICE + parametric defect-box netlist parser
│   ├── stamp.rs                # MNA + Multi-PDK + PCB EM + 2D/GAA TCAD + explicit ODE compiler
│   ├── emit_smt2.rs            # Pure-exp SMT-LIB 2.6 & native dReal `define-ode` emitters
│   ├── emit_lean.rs            # Exact rational Lean 4 `TranscendentalField` target emitter
│   ├── numeral.rs              # Shortest-roundtrip decimal rational conversion
│   ├── paving.rs               # IEEE-754 outward-ULP interval evaluator & paving tree verifier
│   ├── lib.rs                  # Library entrypoints
│   └── main.rs                 # CLI (`compile`, `batch`, `emit-lean`, `generate-paving`, `verify-paving`, `emit-witness`, `list-pdks`)
├── benchmarks/
│   ├── sp/                     # 19 graded multi-PDK / PCB / TCAD `.sp` benchmark decks
│   └── smt2/
│       ├── smt2-exp/           # 19 pure-`exp` SMT-LIB 2.6 files (`ALL` + `exp`)
│       └── dreal-ode/          # 19 native continuous-ODE `dReal` files (`define-ode` + `forall_t`)
├── examples/
│   └── diode_clipper_paving.json  # Verified 3-leaf UNSAT paving certificate for Benchmark 01
├── lean/                       # Lean 4.35 verification workspace
├── docs/
│   ├── DESIGN_SPACE.md         # Architectural rationale, anti-sweep verification & solver-to-Lean paths
│   └── PCB_AND_TCAD_MODELS.md  # Full equations for all 6 PDKs, PCB multiphysics & SG TCAD
└── tests/
    └── integration.rs          # Non-vacuity equilibria, SAT witnesses, 32-corner DFM & paving tests
```

---

## License

Dual-licensed under either [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE) at your option.
