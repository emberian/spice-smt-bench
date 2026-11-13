* Suite A-01: Shockley ESD Diode Clipper Over Continuous Supply & Temperature Box
.pdk gf180mcu
.expected unsat
.mode dc
.default_vbound [-0.5, 4.0]

* Continuous PVT box: supply v_sup in [3.0V, 3.6V], thermal voltage vt in [23.5mV, 32.2mV] (273K..373K)
.param v_sup [3.0, 3.6]
.param vt    [0.0235, 0.0322]

.bound v(in)  [3.0, 3.6]
.bound v(out) [-0.5, 3.6]
.bound i_Vdd  [-0.01, 0.01]
.bound i_D1   [-0.001, 1.0]

Vdd   in  0   DC {v_sup}
R1    in  out 1000
Rload out 0   10000
D1    out 0   GF180_DIODE_ESD area=100 vt={vt}

* Negated safety target: can clamped output ever exceed 0.85 V?
.unsafe v(out) > 0.85
.end
