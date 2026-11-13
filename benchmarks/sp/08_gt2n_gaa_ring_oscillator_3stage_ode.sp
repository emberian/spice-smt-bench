* Suite B-08: 2nm Gate-All-Around (gt2n) 3-Stacked Nanosheet 3-Stage Ring Oscillator Envelope (ODE)
.pdk gt2n
.expected unsat
.mode tran dt=1.0e-12 steps=40 method=trap
.default_vbound [-0.25, 1.0]

* Continuous supply, nanosheet thickness etch delta, and inner-spacer thickness delta
.param vdd      [0.62, 0.68]
.param dtns_nm  [-0.30, 0.30]
.param dlisp_nm [-0.60, 0.60]

.bound v(n1) [-0.20, 0.90]
.bound v(n2) [-0.20, 0.90]
.bound v(n3) [-0.20, 0.90]

.init v(n1) [0.55, 0.62]
.init v(n2) [0.02, 0.08]
.init v(n3) [0.28, 0.35]

Vsup vdd 0 DC {vdd}

* Stage 1 (3 stacked nanosheets + inner-spacer fringing C_isp(dL_isp))
Mp1 n2 n1 vdd vdd GT2N_PFET_GAA Nsheet=3 dTns={dtns_nm} dLisp={dlisp_nm}
Mn1 n2 n1 0   0   GT2N_NFET_GAA Nsheet=3 dTns={dtns_nm} dLisp={dlisp_nm}
Cl1 n2 0 1.8e-15

* Stage 2
Mp2 n3 n2 vdd vdd GT2N_PFET_GAA Nsheet=3 dTns={dtns_nm} dLisp={dlisp_nm}
Mn2 n3 n2 0   0   GT2N_NFET_GAA Nsheet=3 dTns={dtns_nm} dLisp={dlisp_nm}
Cl2 n3 0 1.8e-15

* Stage 3
Mp3 n1 n3 vdd vdd GT2N_PFET_GAA Nsheet=3 dTns={dtns_nm} dLisp={dlisp_nm}
Mn3 n1 n3 0   0   GT2N_NFET_GAA Nsheet=3 dTns={dtns_nm} dLisp={dlisp_nm}
Cl3 n1 0 1.8e-15

* Prove Miller / inner-spacer capacitive feedthrough never causes rail over/undershoot beyond 120 mV
.unsafe v(n1) > 0.83 || v(n1) < -0.08 || v(n2) > 0.83 || v(n2) < -0.08 || v(n3) > 0.83 || v(n3) < -0.08
.end
