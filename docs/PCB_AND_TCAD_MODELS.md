# Multi-PDK Transistor, Continuous-Defect PCB & 2D/GAA TCAD Mathematical Models

This reference describes the reduced conservation laws and constitutive equations stamped by `spice2smt` (`src/pdk.rs` and `src/stamp.rs`) across all 19 benchmarks.

---

## 1. Modified Nodal Analysis (MNA) & Explicit Nonlinear ODE Extraction

### 1.1 DC Equilibrium Stamp (`.mode dc`)
For a circuit with $N$ non-ground nodes, voltage sources $V_m$, resistors/conductances, and nonlinear multi-terminal devices, KCL at every non-ground node $i$ asserts that total branch current leaving node $i$ equals zero:
$$\sum_{j \sim i} G_{ij}(p)\,(v_i - v_j) + \sum_{d \in \mathcal{D}_i} s_{i,d}\,i_d(v, p) + \sum_{m \in \mathcal{V}_i} s_{i,m}\,i_{V_m} = 0,$$
paired with $v_{n^+(m)} - v_{n^-(m)} = E_m(p)$ for each independent voltage source $V_m$.

### 1.2 Transient Nonlinear State-Space ODE Extraction (`.mode tran`)
In transient mode, node voltages are partitioned into:
- **Stiff source-pinned nodes** driven directly by voltage sources $v_s(t)$ (`DC`, Gaussian fault pulse `GAUSS`, or smooth hyperbolic-tangent `STEP`), whose time derivatives $\dot{v}_s(t)$ are computed by **exact symbolic differentiation** in the waveform stamper.
- **Dynamic capacitive state nodes** $v_C \in \mathbb{R}^{n_C}$ and **inductor branch currents** $i_L \in \mathbb{R}^{n_L}$.

Capacitor branches include both linear capacitances (including floating coupling capacitors $C_{ij}$ between dynamic nodes, inverted per connected component via exact $1\times 1$, $2\times 2$, and $3\times 3$ symmetric cofactor/Cramer's rule) and voltage-dependent nonlinear capacitances:
- **Class-II Ceramic MLCC DC-Bias Derating (`11`):**
  $$C_{\text{mlcc}}(v) = C_{\min} + \frac{C_0}{1 + (v / V_{\text{sat}})^2}, \qquad i_C = C_{\text{mlcc}}(v)\,\frac{dv}{dt}.$$
- **GaN-on-SiC Depletion Miller Capacitance (`07`):**
  $$C_{gd}(v_{dg}) = C_{\min} + \frac{C_{gd0}}{\sqrt{1 + (v_{dg} / V_{\text{bi}})^2}}, \qquad i_{gd} = C_{gd}(v_{dg})\,\left(\frac{dv_g}{dt} - \frac{dv_d}{dt}\right),$$
  where $\frac{dv_d}{dt}$ on a slew-driven switching node is differentiated symbolically in closed form so full Miller displacement current $C_{gd}(v_{dg})\,\dot{V}_{\text{sw}}(t)$ is injected into the gate node ODE!

Coupled inductor pairs $K_{ab}$ (`L1`, `L2`, coupling $k \in (-1, 1)$, mutual inductance $M = k\sqrt{L_1 L_2}$) are inverted via the exact $2\times 2$ inductance determinant $\Delta_L = L_1 L_2 - M^2 > 0$:
$$\frac{di_1}{dt} = \frac{L_2\,\tilde{v}_1 - M\,\tilde{v}_2}{L_1 L_2 - M^2}, \qquad \frac{di_2}{dt} = \frac{L_1\,\tilde{v}_2 - M\,\tilde{v}_1}{L_1 L_2 - M^2}.$$

---

## 2. Six-Regime Multi-PDK Compact Device Physics (`src/pdk.rs`, `src/stamp.rs`)

Thermal voltage is stamped from junction temperature $T$ via exact Boltzmann-over-charge $V_T(T) = \frac{k_B}{q} T$ with $\frac{k_B}{q} = 8.617333262 \times 10^{-5}\text{ V/K}$.

### 2.1 `asap7` — 7nm Multi-Gate FinFET (`SLVT` / `RVT` / `SRAM`)
For fin count $N_{\text{fin}}$, effective gate length $L_{\text{eff}} = L_g + \Delta L_g$, fin thickness $T_{\text{eff}} = T_{\text{fin}} + \Delta T_{\text{fin}}$, fin height $H_{\text{fin}} = 32\text{ nm}$, and $\text{HfO}_2$ EOT $t_{\text{ox}} = 1.0\text{ nm}$:
1. **Tri-Gate Natural Scaling Length:**
   $$\lambda_{\text{fin}} = \sqrt{\frac{\varepsilon_{\text{Si}}}{3\,\varepsilon_{\text{ox}}}\,T_{\text{eff}}\,t_{\text{ox}}} = \sqrt{T_{\text{eff}}\,t_{\text{ox}}} \quad (\varepsilon_{\text{Si}} / \varepsilon_{\text{ox}} = 11.7 / 3.9 = 3).$$
2. **1D Carrier Quantum Confinement Shift ($\alpha_{\text{QM}} = \frac{\hbar^2 \pi^2}{2 m^* q} \approx 0.836\text{ V}\cdot\text{nm}^2$):**
   $$\Delta V_{\text{th,QM}}(T_{\text{eff}}) = \alpha_{\text{QM}}\left(\frac{1}{T_{\text{eff}}^2} - \frac{1}{T_{\text{fin,0}}^2}\right).$$
   Etching a $6.5\text{ nm}$ fin thinner by $\Delta T_{\text{fin}} = -1.0\text{ nm}$ raises $V_{\text{th}}$ by $+7.8\text{ mV}$, while over-widening increases $\lambda_{\text{fin}}$ and degrades short-channel control.
3. **Short-Channel DIBL & Smooth All-Region Inversion Charge:**
   $$V_{\text{th,eff}} = V_{\text{th,0}} + \Delta\Phi_m + \Delta V_{\text{th,QM}}(T_{\text{eff}}) - \eta_{\text{DIBL}}\,\exp\!\left(-\frac{L_{\text{eff}}}{2\lambda_{\text{fin}}}\right) V_{\text{ov,ds}},$$
   $$I_{DS} = I_{\text{spec}}(N_{\text{fin}}, L_{\text{eff}})\,\Bigl(y_f^2 - y_r^2\Bigr), \qquad \exp(y_{f,r}) = 1 + \exp(z_{f,r}).$$

### 2.2 `gt2n` (`gaa2n`) — 2nm Gate-All-Around Stacked Nanosheet
Models $N_{\text{sheet}} = 3$ vertically stacked silicon channels ($W_{\text{ns}} = 18\text{ nm}, T_{\text{ns}} = 5.0\text{ nm}, \text{EOT} = 0.85\text{ nm}$):
- **4-Sided Gate Wrap Scaling Length:** $\lambda_{\text{GAA}} = \sqrt{\frac{3}{4}\,T_{\text{ns}}\,t_{\text{ox}}}$ (tighter electrostatic screening than tri-gate FinFETs).
- **Inner-Spacer Parasitic Fringing Capacitance (`08`):**
  $$C_{\text{isp}}(L_{\text{isp}} + \Delta L_{\text{isp}}) = N_{\text{sheet}}\,\frac{\varepsilon_{\text{isp}}\,A_{\text{ext}}}{L_{\text{isp}} + \Delta L_{\text{isp}}},$$
  coupling gate-to-source/drain delay directly to sub-nanometer inner-spacer etch tolerance $\Delta L_{\text{isp}}$.

### 2.3 `ihp_sg13g2` — 130nm SiGe Heterojunction Bipolar (`SG13_NPN_HBT`)
Models collector current enhancement from graded-Ge base bandgap narrowing $\Delta E_{g,\text{Ge}} \in [80, 90]\text{ meV}$ and monotone high-injection **Kirk base push-out**:
$$I_{\text{fwd,0}} = A \cdot I_{S0}\,\exp\!\left(\frac{\Delta E_{g,\text{Ge}}}{V_T(T)}\right)\left(\exp\!\left(\frac{V_{BE}}{n_F V_T(T)}\right) - 1\right),$$
$$I_{C,\text{fwd}} = \frac{I_{\text{fwd,0}}}{\sqrt{1 + (I_{\text{fwd,0}} / (A I_{\text{Kirk}}))^2}}\left(1 + \frac{V_{CE}}{V_{AF}}\right), \qquad I_B = \frac{I_{\text{fwd,0}}}{\beta_F} + \frac{I_{\text{rev,0}}}{\beta_R}.$$
Crucially, base injection $I_B$ scales with un-collapsed $I_{\text{fwd,0}}/\beta_F$ while collector transport $I_{C,\text{fwd}}$ saturates smoothly at the area-scaled Kirk current before Early modulation without unphysical current collapse at high $V_{BE}$.

### 2.4 `gan_sic` — Wide-Bandgap GaN-on-SiC Power HEMT
Models high-voltage 2DEG polarization transport ($V_{\text{th}} \approx 1.45\text{ V}$, $V_{\text{bus}} = 48\text{ V}$) with velocity/field saturation and nonlinear depletion-mode $C_{gd}(v_{dg})$ Miller feedback (`07`).

---

## 3. Continuous-Defect PCB Electromagnetic Interconnect Models (`Suite C`)

### 3.1 Single-Ended Microstrip (`Hammerstad–Jensen` + Copper Thickness Correction)
Given nominal trace width $w_0$, trapezoidal etch undercut $\Delta w_{\text{etch}}$, dielectric height $h = h_0 + \Delta h_{\text{lam}}$, plated copper thickness $t_{\text{cu}}$, and laminate permittivity $\varepsilon_r$:
$$w_{\text{eff}} = (w_0 + \Delta w_{\text{etch}}) + \frac{t_{\text{cu}}}{\pi}\left(1 + \ln\!\left(\frac{2 h}{t_{\text{cu}}}\right)\right), \qquad u = \frac{w_{\text{eff}}}{h},$$
$$\varepsilon_{\text{eff}} = \frac{\varepsilon_r + 1}{2} + \frac{\varepsilon_r - 1}{2\,\sqrt{1 + 12 / u}}, \qquad Z_0 = \frac{60}{\sqrt{\varepsilon_{\text{eff}}}}\,\ln\!\left(\frac{8}{u} + \frac{u}{4}\right).$$
Per-unit-length parameters $L' = Z_0 \sqrt{\varepsilon_{\text{eff}}} / c_0$ and $C' = \sqrt{\varepsilon_{\text{eff}}} / (c_0 Z_0)$ are stamped into lumped $\Pi$-equivalent sections with rectangular-cross-section DC copper resistance $R_{\text{cu}} = \frac{\rho_{\text{Cu}}\,\ell}{w_{\text{metal}}\,t_{\text{cu}}}$.

### 3.2 Edge-Coupled Differential Pair, Fiber-Weave Skew & Return-Plane Slot (`09a`, `10`, `12a`, `12b`)
For a differential pair over glass/epoxy weave, the $+$ and $-$ legs experience independent local permittivities $\varepsilon_{r,+}$ and $\varepsilon_{r,-}$ (`10`, `12a`, `12b`), producing propagation-velocity skew $\Delta \tau = \frac{\ell}{c_0}\left(\sqrt{\varepsilon_{\text{eff},+}} - \sqrt{\varepsilon_{\text{eff},-}}\right)$ that converts differential edges into common-mode noise!
- Edge proximity coupling factor $k_c = \exp\!\left(-1.9\,\frac{s_0 + \Delta s_{\text{etch}}}{h}\right)$ determines differential impedance $Z_{\text{diff}} = (Z_{0,+} + Z_{0,-})\sqrt{(1-k_c)/(1+k_c)}$, mutual capacitance $C_m$, and inductive coupling.
- When a differential pair crosses a split reference-plane gap (`12a`), return current detours around the slot inductance $L_{\text{slot}} \in [3.5, 6.0]\text{ nH}$, elevating receiver reference bounce $v(\text{gnd\_rx})$ above logic noise margins unless shunted by stitching vias (`12b`).

---

## 4. 2D Multi-Gate FinFET & Coupled Electro-Thermal 2nm GAA TCAD (`Suite D`)

### 4.1 2D Cross-Section `ASAP7` FinFET Mesh (`.tcad_finfet_2d`, `13`)
Discretizes the $(x, y) \in [0, L_g] \times [0, T_{\text{fin}}]$ silicon body on an $N_x \times N_y$ finite-volume grid with:
- Source/drain Dirichlet contacts $\psi_{0,j} = \psi_{\text{bi}}$, $\psi_{N_x-1,j} = \psi_{\text{bi}} + V_{DS}$, $\phi_{n,0} = 0$, $\phi_{n,N_x-1} = V_{DS}$.
- High-$\kappa$ $\text{HfO}_2$ Robin oxide-flux boundary conditions on both sidewalls ($j = 0, N_y - 1$) plus top-gate wrap coupling:
  $$\frac{\psi_{i-1,j} - 2\psi_{i,j} + \psi_{i+1,j}}{\Delta x^2} + \mathcal{F}_y(\psi_{i,\cdot}) + \gamma_{\text{top}}\frac{V_{G,\text{eff}} - \psi_{i,j}}{\text{EOT}} = \frac{q}{\varepsilon_{\text{Si}}}\Bigl(n_{i,j}(\psi_{i,j}, \phi_{n,i}, \Delta V_{\text{QM}}) + N_A\Bigr).$$
- Singularity-free axial Scharfetter–Gummel electron continuity summed across transverse rows with a shared axial quasi-Fermi potential with positive drain-to-source current $J_e \propto B(-\Delta_e)\,n_e - B(\Delta_e)\,n_{e+1}$.

### 4.2 Coupled Electro-Thermal 2nm GAA Stacked Nanosheet (`.tcad_gaa_electrothermal`, `14a` & `14b`)
Couples 4-sided Gate-All-Around Poisson electrostatics (with inner-spacer source/drain fringing through $L_{\text{isp}} + \Delta L_{\text{isp}}$), axial Scharfetter–Gummel stack current $I_{\text{stack}}(\psi, \phi_n, T_{\text{ch}})$, and steady-state lattice heat flow:
$$T_{\text{ch}} = T_{\text{amb}} + R_{\text{th}} \cdot V_{DS} \cdot I_{\text{stack}}(\psi, \phi_n, T_{\text{ch}}),$$
where $T_{\text{ch}}$ feeds back into both thermal voltage $V_T(T_{\text{ch}}) = \frac{k_B}{q} T_{\text{ch}}$ and thermally activated carrier concentration $\Delta\phi_{\text{th}}(T_{\text{ch}})$—creating a genuine coupled transcendental fixed point distinguishing safe BEOL heat sinking (`14a`, `UNSAT`) from buried-oxide thermal excursion (`14b`, `SAT`).


## Implementation details and verification scope

For the wide-strip regime used by the PCB decks, the impedance equation is
$Z_0=120\pi/[\sqrt{\varepsilon_{\rm eff}}(u+1.393+0.667\ln(u+1.444))]$.
The logarithmic narrow-strip equation above applies to the narrow branch.
Copper resistance uses the physical metal width and the supplied conductivity.
The coupled ladder uses $C_{\rm ground}=C_0(1-k_c)$, $C_m=k_c C_0$,
$L_m=k_c\sqrt{L_pL_n}$ and uncoupled via inductances. `n_seg` controls the
number of cascaded sections (default three).

When `Temp` is supplied, the junction saturation current is
$I_S(T)=A I_{S0}(T/300)^3\exp[E_{g0}/(nV_{T0})-(E_{g0}-\Delta E_g)/(nV_T)]$,
with $E_{g0}=1.12$ eV. This replaces the fixed-temperature prefactor in the
SiGe expression above. The model's Early voltage is 45 V.

MOS instance `W` and `L` are in meters. FinFET and GAA confinement coefficients
come from $\hbar^2\pi^2/(2qm^*)$, with masses 0.45 and 0.41 times the free-electron
mass, respectively. The GAA default is three sheets. Source-referenced EKV
arguments are $z_f=\kappa(V_{GS}-V_{th})/(2V_T)$ and
$z_r=[\kappa(V_{GS}-V_{th})-V_{DS}]/(2V_T)$, with polarity reversal for PMOS.
The finite-width models apply smooth inversion-charge drive degradation.
`Tamb` supplies threshold temperature dependence; `Rth` adds thermal balance.
The GaN channel is a compact polarization-charge EKV model.

Benchmark 11 uses 8 nF BGA and 3 nF die capacitances, plus a nonlinear 22 µF
MLCC with 1.5 µF floor, 3 mΩ ESR and 0.14 nH ESL. Its 16 backward-Euler steps
of 0.25 ns cover 4 ns. The MLCC-removal regression tests the 0.80 V floor.
Benchmark 12a maps slot width 7–12 mm to 3.5–6 nH and tests ±25 mV bounce.
The complementary smooth steps start near zero; their logistic tails are not
an exact zero-voltage DC equilibrium at time zero.

SMT exponential and Lean transient targets describe the selected finite
backward-Euler or trapezoidal recurrence. Native ODE output describes continuous
time. Sampled witnesses and finite-step safety do not establish continuous-time
safety. Lean theorems are conditional on `TranscendentalField`; this library does
not construct a concrete real-exponential instance.


### Bipolar reverse transport and guard-ringed SCR

For both polarities, let forward-oriented junction voltages be `V_BE` and `V_BC`
(the PNP voltages and terminal currents reverse sign). With the temperature-scaled
area-inclusive saturation current above, the stamp uses

$$I_F=I_S(T)(e^{V_{BE}/V_T}-1),\qquad I_R=I_S(T)(e^{V_{BC}/V_T}-1),$$
$$I_C=I_{C,\mathrm{fwd}}-I_R-I_R/\beta_R,\qquad I_B=I_F/\beta_F+I_R/\beta_R.$$

For ordinary parasitic BJTs, the forward collector term is `I_F`; HBTs apply
Kirk roll-off and the model's Early modulation as described above. The built-in
SCR NPN and PNP both use reverse beta 2. Benchmark 05 adds 20 Ω ballast at each
emitter, well taps of 6–14 Ω, substrate taps of 5–12 Ω, supply 0.70–0.88 V,
and temperature 273–398 K. Supply and device currents have no implicit finite
search clamps. The regression proves its complete declared continuous box UNSAT
by interval contraction/bisection, and checks a latched unguarded counterfactual.

`IntervalCheck.lean` proves signed interval multiplication, positive-denominator
division and exponential enclosures. The exponential upper bound reciprocates a
positive rational lower bound for `exp(-x)`; `exp_neg` is derived from the
exponential and ordered-field division laws. `Targets.lean` proves Benchmark 01
both directly and by concrete paving replay, Benchmark 06 by a sampled barrier,
and Benchmark 09a by a checked forward-bound paving over the manufacturing box.
Its two bandgap startup lemmas are
component results, not proofs of the generated bandgap decks.
