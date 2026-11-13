* Suite A-04b: IHP SG13G2 130nm SiGe HBT Reference WITH Startup Keeper (Trojan Eliminated UNSAT)
.pdk ihp_sg13g2
.expected unsat
.mode dc
.default_vbound [-0.1, 3.6]

.param vdd     [2.7, 3.3]
.param temp_k  [273.0, 373.0]
.param deg_ge  [0.080, 0.090]

.bound v(vdd) [2.7, 3.3]
.bound v(ref) [-0.05, 1.8]
.bound v(ve2) [-0.05, 1.4]

Vsup vdd 0 DC {vdd}

* Startup keeper pull-up + diode-connected SiGe HBT Q1 + PTAT Q2 reference network:
* Guarantees non-zero startup current and pins v(ref) cleanly around ~0.72V..0.82V across all PVT + Ge corners
R_start vdd ref 4200
R_bleed ref 0   80000
Q1      ref ref 0   SG13_NPN_HBT area=2 dEg={deg_ge} Temp={temp_k}
Q2      vdd ref ve2 SG13_NPN_HBT area=8 dEg={deg_ge} Temp={temp_k}
R_ptat  ve2 0   1800

* Prove the zero-current lockup state v(ref) < 0.40 V is unreachable across the entire PVT box
.unsafe v(ref) < 0.40
.end
