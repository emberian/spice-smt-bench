* Suite C-09b: Uncontrolled PCB Fab Over-Etch + Resin-Rich Prepreg Corner Violating Z0 Tolerance (SAT)
.expected sat
.mode dc
.default_vbound [-0.5, 5.0]

* Wide low-cost fab tolerance box: severe copper over-etch (-42um) + thick prepreg (+18um) + low Dk (3.85)
.param dw_etch [-42.0e-6, 5.0e-6]
.param dh_lam  [-12.0e-6, 18.0e-6]
.param t_cu    [28.0e-6, 38.0e-6]
.param er_lam  [3.85, 4.50]

Vdrv tx 0 DC 1.0
.pcb_microstrip tl50 tx rx 0 len=0.050 w0=180.0e-6 dw={dw_etch} h0=100.0e-6 dh={dh_lam} t_cu={t_cu} er={er_lam}
Rterm rx 0 50.0

* Solver discovers concrete multi-parameter fab corner where Z0 exceeds +12% limit (> 56 Ohm)!
.unsafe Z0_tl50 > 56.0
.end
