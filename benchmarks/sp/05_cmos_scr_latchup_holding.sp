* Suite A-05: Parasitic 4-Layer p-n-p-n CMOS SCR Latchup Below Holding Envelope
.pdk gf180mcu
.expected unsat
.mode dc
.default_vbound [-0.1, 1.3]

* Guard-ringed n-well and p-substrate tap resistances + temperature uncertainty
.param vsupply [0.80, 1.00]
.param r_well  [80.0, 150.0]
.param r_sub   [60.0, 120.0]
.param vt      [0.024, 0.031]

.bound v(sup)   [0.80, 1.00]
.bound v(nwell) [0.00, 1.05]
.bound v(psub)  [-0.05, 1.00]
.bound i_Vsup   [-0.05, 0.05]

Vsup  sup   0     DC {vsupply}
Rwell sup   nwell {r_well}
Rsub  psub  0     {r_sub}

* Cross-coupled parasitic vertical PNP and lateral NPN forming p-n-p-n thyristor
Qpnp  psub  nwell sup GF180_SCR_PNP area=2 Vt={vt}
Qnpn  nwell psub  0   GF180_SCR_NPN area=2 Vt={vt}

* Prove total supply current drawn into the SCR cannot sustain latchup (> 5 mA) below 1.0 V
.unsafe -i_Vsup > 0.005
.end
