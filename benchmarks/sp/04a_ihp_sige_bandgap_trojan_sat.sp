* Suite A-04a: IHP SG13G2 130nm SiGe HBT + PMOS Mirror Bandgap WITHOUT Startup Guard (Analog Trojan SAT)
.pdk ihp_sg13g2
.expected sat
.mode dc
.default_vbound [-0.1, 3.6]

* Continuous supply, temperature, and SiGe base Ge-mole-fraction bandgap narrowing box
.param vdd     [2.7, 3.3]
.param temp_k  [273.0, 373.0]
.param deg_ge  [0.080, 0.090]

.bound v(vdd) [2.7, 3.3]
.bound v(ref) [-0.05, 1.6]
.bound v(ve2) [-0.05, 1.2]
.bound v(vc1) [0.0, 3.4]

Vsup vdd 0 DC {vdd}

* Self-biased PMOS current mirror (Mp1 diode-connected at `vc1`, Mp2 mirroring into `ref`)
* + SiGe HBT PTAT core WITHOUT startup bleeder:
* Admits BOTH normal ~1.18V bandgap equilibrium AND degenerate zero-current Trojan root (v(vc1) ~ vdd, v(ref) ~ 0V)!
Mp1    vc1 vc1 vdd vdd SG13_PMOS W=12.0e-6 L=1.0e-6
Mp2    ref vc1 vdd vdd SG13_PMOS W=12.0e-6 L=1.0e-6
Q1     vc1 ref 0   SG13_NPN_HBT area=1 dEg={deg_ge} Temp={temp_k}
Q2     vc1 ref ve2 SG13_NPN_HBT area=8 dEg={deg_ge} Temp={temp_k}
R_ptat ve2 0   2200
R_bgr  ref 0   18000

* Unsafe Trojan equilibrium: reference locked below 0.40 V while supply is valid!
.unsafe v(ref) < 0.40
.end
