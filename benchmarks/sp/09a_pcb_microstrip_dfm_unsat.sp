* Suite C-09a: IPC Class-3 Controlled-Impedance PCB Microstrip & Diffpair Over 5D Fab Defect Polytope
.expected unsat
.mode dc
.default_vbound [-0.5, 5.0]

* 5D Continuous PCB Manufacturing Defect Polytope D_fab (kills discrete parameter grid sweeps!):
*   dw_etch : trapezoidal copper etch undercut [-8um, +4um] around w0 = 180um
*   ds_etch : coupled gap etch delta [-4um, +8um] around s0 = 180um
*   dh_lam  : prepreg lamination thickness variation [-5um, +5um] around h0 = 100um
*   t_cu    : plated outer-layer copper thickness [32um, 38um]
*   er_lam  : laminate relative permittivity [4.15, 4.35]
.param dw_etch [-8.0e-6, 4.0e-6]
.param ds_etch [-4.0e-6, 8.0e-6]
.param dh_lam  [-5.0e-6, 5.0e-6]
.param t_cu    [32.0e-6, 38.0e-6]
.param er_lam  [4.15, 4.35]

Vdrv tx   0 DC 1.0
Vdp  tx_p 0 DC 0.5
Vdn  tx_n 0 DC -0.5

.pcb_microstrip tl50 tx rx 0 len=0.050 w0=180.0e-6 dw={dw_etch} h0=100.0e-6 dh={dh_lam} t_cu={t_cu} er={er_lam}
Rterm rx 0 50.0

.pcb_coupled_diffpair diff90 tx_p tx_n rx_p rx_n 0 0 len=0.050 w0=182.0e-6 dw={dw_etch} s0=180.0e-6 ds={ds_etch} h0=100.0e-6 dh={dh_lam} t_cu={t_cu} er_p={er_lam} er_n={er_lam}
Rtp rx_p 0 45.0
Rtn rx_n 0 45.0

* Prove single-ended Z0 stays strictly within [45, 55] Ohm (+/-10%) AND differential Zdiff within [90, 110] Ohm (+/-10%)
* across ALL infinitely many manufacturable boards in D_fab!
.unsafe Z0_tl50 < 45.0 || Z0_tl50 > 55.0 || Zdiff_diff90 < 90.0 || Zdiff_diff90 > 110.0
.end
