* Suite C-12b: Differential Pair With Stitching-Via Return Fence Suppressing EMI Bounce (UNSAT)
.expected unsat
.mode tran dt=8.0e-11 steps=6 method=be
.default_vbound [-1.5, 2.5]

* Identical fiber-weave skew box, but stitching-via return fence cuts return inductance to [0.05nH, 0.12nH]!
.param er_p   [4.40, 4.70]
.param er_n   [3.80, 4.05]
.param l_slot [0.05e-9, 0.12e-9]

.bound v(in_p)    [-0.2, 1.5]
.bound v(in_n)    [-0.2, 1.5]
.bound v(out_p)   [-0.6, 1.8]
.bound v(out_n)   [-0.6, 1.8]
.bound v(gnd_rx)  [-0.5, 0.5]

.init v(in_p)   = 0.0
.init v(in_n)   = 1.0
.init v(out_p)  = 0.0
.init v(out_n)  = 1.0
.init v(gnd_rx) = 0.0

Vdp drv_p 0 STEP(base=0.0 step=1.0  t0=8.0e-11 tau=3.5e-11)
Vdn drv_n 0 STEP(base=1.0 step=-1.0 t0=8.0e-11 tau=3.5e-11)
Rdp drv_p in_p 25.0
Rdn drv_n in_n 25.0

.pcb_coupled_diffpair bus in_p in_n out_p out_n 0 gnd_rx len=0.040 w0=160.0e-6 dw=0.0 s0=180.0e-6 ds=0.0 h0=100.0e-6 dh=0.0 t_cu=35.0e-6 er_p={er_p} er_n={er_n} l_via=0.2e-9 l_slot={l_slot} r_ret=0.01

Rtp    out_p  gnd_rx 50.0
Rtn    out_n  gnd_rx 50.0
Cplane gnd_rx 0      12.0e-12

* Stitching-via fence keeps receiver ground-reference bounce strictly within +/- 25 mV across entire skew box!
.unsafe v(gnd_rx) > 0.025 || v(gnd_rx) < -0.025
.end
