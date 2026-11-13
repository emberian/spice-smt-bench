* Suite C-10: Coupled PCB Trace Crosstalk With Fiber-Weave Skew, Via Stub & Victim ESD Diodes (ODE)
.pdk gf180mcu
.expected unsat
.mode tran dt=6.0e-11 steps=5 method=be
.default_vbound [-1.0, 3.0]

* Continuous FR-4 glass fiber-weave permittivity skew (er_agg vs er_vic), etch gap delta, and via stub L_via
.param er_agg  [4.35, 4.65]
.param er_vic  [3.85, 4.15]
.param ds_etch [-15.0e-6, 15.0e-6]
.param l_via   [0.25e-9, 0.75e-9]

.bound v(agg_in)  [-0.2, 2.2]
.bound v(agg_out) [-0.5, 2.5]
.bound v(vic_in)  [-0.5, 1.5]
.bound v(vic_out) [-0.8, 1.8]

.init v(agg_in)  = 0.0
.init v(agg_out) = 0.0
.init v(vic_in)  = 0.0
.init v(vic_out) = 0.0

* Aggressor 1.8V fast driver + quiet victim termination + coupled microstrip with fiber-weave skew + ESD clamps
Vvdd   vdd    0      DC 1.8
Vagg   drv    0      STEP(base=0.0 step=1.8 t0=1.0e-10 tau=5.0e-11)
Rdrv   drv    agg_in 28.0
Rvnear vic_in 0      50.0

.pcb_coupled_diffpair xtalk agg_in vic_in agg_out vic_out 0 0 len=0.045 w0=175.0e-6 dw=0.0 s0=200.0e-6 ds={ds_etch} h0=100.0e-6 dh=0.0 t_cu=35.0e-6 er_p={er_agg} er_n={er_vic} l_via={l_via} l_slot=0.0

Cload_agg agg_out 0   2.0e-12
Rterm_agg agg_out 0   50.0
Cload_vic vic_out 0   2.5e-12

* Victim receiver dual-rail Shockley ESD protection diodes to Vdd (1.8V) and GND
Desd_hi vic_out vdd GF180_DIODE_ESD area=80
Desd_lo 0       vic_out GF180_DIODE_ESD area=80

* Prove far-end crosstalk + via-stub ringing never false-triggers victim receiver (>= 0.65 V)
.unsafe v(vic_out) >= 0.65 || v(vic_out) <= -0.75
.end
