* Suite B-06: Nonlinear RC + Shockley Clamp Glitch Filter Rejecting Laser/EMI Fault Pulse (ODE)
.pdk gf180mcu
.expected unsat
.mode tran dt=1.0e-10 steps=6 method=be
.default_vbound [-0.5, 2.5]

* Uncertain peak laser/EMI fault current up to 35 mA (would exceed 1.1V without nonlinear diode clamp!)
.param i_peak [0.0, 0.035]
.param vt     [0.024, 0.031]

.bound v(comp) [-0.2, 2.0]
.init  v(comp) [0.0, 0.05]

* Smooth Gaussian fault-current injection into `comp` node + bleed resistor + filter cap + Shockley clamp
Ifault 0    comp GAUSS(base=0.0 amp={i_peak} t0=2.5e-10 width=1.8e-10)
Rbleed comp 0    2500
Cfilt  comp 0    8.0e-12
Dclamp comp 0    GF180_DIODE_ESD area=120 vt={vt}

* Comparator false-trigger threshold at 1.10 V
.unsafe v(comp) >= 1.10
.end
