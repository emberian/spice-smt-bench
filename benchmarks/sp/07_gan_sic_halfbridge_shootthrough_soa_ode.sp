* Suite B-07: GaN-on-SiC 48V Half-Bridge High-dv/dt Miller Bounce & Shoot-Through Immunity (ODE)
.pdk gan_sic
.expected unsat
.mode tran dt=2.5e-10 steps=6 method=be
.default_vbound [-1.0, 55.0]

* Uncertain zero-bias Miller Cgd0 and gate driver active Miller-clamp pull-down resistance
.param cgd0 [35.0e-12, 48.0e-12]
.param r_pd [0.8, 1.5]
.param vt   [0.025, 0.034]

.bound v(g_ls) [-0.3, 3.0]

.init  v(g_ls) [0.0, 0.05]


* High-dv/dt 48V switching node + bus supply for low-side GaN eHEMT SOA check
Vsw  drive  0 STEP(base=0.0 step=48.0 t0=6.0e-10 tau=3.5e-10)
Rcomm drive sw 0.5
* Voltage-dependent AlGaN/GaN 2DEG depletion Miller capacitance C_gd(v_sw - v_g)
C_GD_gd sw g_ls GAN_CGD_MILLER C0={cgd0} Cmin=3.5e-12 Vsat=8.0 ESR=0.0 ESL=0.0
Cgs       g_ls 0  680.0e-12
Rpd       g_ls 0  {r_pd}

* Low-side GaN eHEMT monitoring drain-to-source cross-conduction into sense load
Cdpar sw 0 120p
Mls sw g_ls 0 0 GAN_EHEMT_100V W=1m L=0.25u Vt={vt}
* Unsafe if Miller bounce approaches eHEMT threshold (1.45V): guard at 1.20 V
.unsafe v(g_ls) > 1.20 || i_Mls > 0.5 || i_Mls * v(sw) > 20.0
.end
