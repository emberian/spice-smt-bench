* Suite D-13: ASAP7 7nm 2D Cross-Section Multi-Gate FinFET Poisson + Quantum Confinement + SG Continuity
.pdk asap7
.expected unsat
.mode dc
.default_vbound [-0.5, 2.5]

* Continuous 4D FinFET litho/etch & thermal uncertainty box:
*   dtfin_nm : fin thickness etch variation [-0.5nm, +0.5nm] around T_fin = 6.5nm
*   dlg_nm   : gate length CD variation [-1.2nm, +1.2nm] around L_g = 21.0nm
*   dphim    : metal-gate workfunction shift [-0.020V, +0.020V]
*   temp_k   : junction temperature [273K, 360K]
.param dtfin_nm [-0.50, 0.50]
.param dlg_nm   [-1.20, 1.20]
.param dphim    [-0.020, 0.020]
.param temp_k   [273.0, 360.0]

* 2D (5 axial x 3 transverse) cross-section mesh with top + dual-sidewall HfO2 EOT=1.0nm gate wrap
* Off-state leakage bias: V_GS = 0.0 V, V_DS = 0.70 V
.tcad_finfet_2d fin7 nx=5 ny=3 lg_nm={21.0 + dlg_nm} tfin_nm={6.5 + dtfin_nm} eot_nm=1.0 vgs=0.0 vds=0.70 phim_shift={dphim} temp_k={temp_k} nbody_cm3=1.0e16

* Prove off-state subthreshold DIBL leakage never exceeds 0.15 uA/um across the entire 4D FinFET litho box
.unsafe id_leak_ua_fin7 > 0.15
.end
