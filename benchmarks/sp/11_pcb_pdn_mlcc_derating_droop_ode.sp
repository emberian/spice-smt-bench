* Suite C-11: Core PDN With BGA Cold-Solder Void & Voltage-Derated Class-II MLCC Under Load Step (ODE)
.expected unsat
.mode tran dt=2.5e-10 steps=6 method=be
.default_vbound [-0.2, 1.5]

* Uncertain BGA cold-solder void resistance R_void, MLCC saturation voltage V_sat, and transient load step dI
.param r_void [0.001, 0.028]
.param v_sat  [0.55, 0.80]
.param di_step [0.40, 1.10]

.bound v(bga)      [0.70, 1.00]
.bound v(vcore)    [0.75, 1.00]
.bound vc_C_MLCC1  [0.70, 1.00]
.bound i_Lplane    [-0.5, 4.0]
.bound i_C_MLCC1   [-3.0, 3.0]

.init v(bga)      = 0.90
.init v(vcore)    = 0.90
.init vc_C_MLCC1  = 0.90
.init i_Lplane    = 0.10
.init i_C_MLCC1   = 0.0

Vvrm   vrm   0     DC 0.90
Lplane vrm   bga   0.22e-9 Rser=0.002
Rvoid  bga   vcore {r_void}
Cbga   bga   0     80.0e-9

* High-k X5R MLCC (nominal 22uF at 0V, collapsing by ~3.5x at 0.9V bias via C0 / (1 + (vc/Vsat)^2))
C_MLCC1 vcore 0 C0=22.0e-6 Cmin=1.5e-6 Vsat={v_sat} ESR=0.003 ESL=0.14e-9
Cdie    vcore 0 15.0e-9

* Fast ASIC core current step from 0.1 A idle to 0.1 + dI_step
Iload vcore 0 STEP(base=0.10 step={di_step} t0=4.0e-10 tau=1.5e-10)

* Prove core voltage droop never violates 0.80 V retention floor (-11% rail budget)
.unsafe v(vcore) < 0.80
.end
