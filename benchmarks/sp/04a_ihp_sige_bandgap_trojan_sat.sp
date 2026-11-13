* PMOS mirror / area-ratio SiGe HBT bandgap twin a
.expected sat
.pdk ihp_sg13g2
.mode dc
.default_vbound [-0.1, 3.6]
.param vdd [2.7, 3.3]
.param temp_k [273.0, 373.0]
.param deg_ge [0.080, 0.090]
.bound v(ref) [-0.05, 1.6]
Vsup vdd 0 DC {vdd}
* Equal-current PMOS mirror drives area-ratio HBT pair.
* Delta-Vbe across Rptat sets PTAT current; Rsum adds its voltage to CTAT Vbe.
Mp1 ref vc1 vdd vdd SG13_PMOS W=12u L=1u Tamb={temp_k}
Mp2 vc1 vc1 vdd vdd SG13_PMOS W=12u L=1u Tamb={temp_k}
Q1 ref ref e0 SG13_NPN_HBT area=1 dEg={deg_ge} Temp={temp_k}
Q2 vc1 ref ve2 SG13_NPN_HBT area=8 dEg={deg_ge} Temp={temp_k}
Rptat ve2 e0 2200
Rsum e0 0 10400
* Reference bleeder balances finite junction/mirror leakage at the low-current equilibrium.
Rbleed ref 0 10meg
.unsafe v(ref) < 0.15
.end
