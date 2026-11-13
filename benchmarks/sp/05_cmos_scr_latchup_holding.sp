* Suite A-05: Parasitic 4-Layer p-n-p-n CMOS SCR Latchup Below Holding Envelope
.pdk gf180mcu
.expected unsat
.mode dc
.default_vbound [-0.1, 1.3]

* Guard-ringed n-well and p-substrate tap resistances + temperature uncertainty
.param vsupply [0.70, 0.88]
.param r_well  [6.0, 14.0]
.param r_sub   [5.0, 12.0]
.param temp_k  [273.0, 398.0]

.bound v(sup)   [0.70, 0.88]
.bound v(nwell) [0.00, 1.05]
.bound v(psub)  [-0.05, 1.00]

Vsup  sup   0     DC {vsupply}
Rwell sup   nwell {r_well}
Rsub  psub  0     {r_sub}

* Cross-coupled parasitic vertical PNP and lateral NPN forming p-n-p-n thyristor
R_ep sup ep 20
R_en en 0 20
Qpnp  psub  nwell ep GF180_SCR_PNP area=2 Temp={temp_k}
Qnpn  nwell psub  en   GF180_SCR_NPN area=2 Temp={temp_k}

* Prove total supply current drawn into the SCR cannot sustain latchup (> 5 mA) below 0.88 V
.unsafe -i_Vsup > 0.005
.end
