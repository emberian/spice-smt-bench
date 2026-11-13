* Suite A-02: ASAP7 7nm Multi-Gate FinFET Inverter Static Noise Margin (Quantum Confinement + DIBL)
.pdk asap7
.expected unsat
.mode dc
.default_vbound [-0.1, 0.9]

* Continuous 4D FinFET litho/etch & PVT uncertainty box
.param vdd       [0.65, 0.75]
.param vin_low   [0.00, 0.14]
.param dtfin_nm  [-0.45, 0.45]
.param dlg_nm    [-1.0, 1.0]
.param temp_k    [273.0, 360.0]

.bound v(vdd) [0.65, 0.75]
.bound v(in)  [0.00, 0.14]
.bound v(out) [0.00, 0.78]

Vsup vdd 0 DC {vdd}
Vin  in  0 DC {vin_low}

Mp out in vdd vdd ASAP7_PFET_RVT L={(21.0 + dlg_nm)*1e-9} Nfin=2 dTfin={dtfin_nm} Tamb={temp_k}
Mn out in 0   0   ASAP7_NFET_RVT L={(21.0 + dlg_nm)*1e-9} Nfin=2 dTfin={dtfin_nm} Tamb={temp_k}

* Negated safety target: logic-high output droop below 0.54 V under noisy low input
.unsafe v(out) < 0.54
.end
