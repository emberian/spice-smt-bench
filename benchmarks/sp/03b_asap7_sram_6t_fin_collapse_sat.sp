* Suite A-03b: ASAP7 7nm 6T FinFET SRAM Read-Upset Collapse Under Excessive Fin-Thinning + WFV (SAT)
.pdk asap7
.expected sat
.mode dc
.default_vbound [-0.05, 0.85]

* Out-of-spec fin-etch thinning + metal-gate workfunction fluctuation tail
.param vdd       [0.60, 0.70]
.param dtfin_nm  [-1.20, 1.20]
.param dlg_nm    [-2.00, 2.00]
.param dphim_q   [-0.110, 0.110]
.param dphim_qb  [-0.110, 0.110]

.bound v(vdd) [0.60, 0.70]
.bound v(q)   [-0.02, 0.72]
.bound v(qb)  [-0.02, 0.72]

Vsup vdd 0 DC {vdd}

Mp_q  q  qb vdd vdd ASAP7_PFET_SRAM L={21.0 + dlg_nm} Nfin=1 dTfin={dtfin_nm} dVth={dphim_q}
Mn_q  q  qb 0   0   ASAP7_NFET_SRAM L={21.0 + dlg_nm} Nfin=2 dTfin={dtfin_nm} dVth={dphim_q}
Mp_qb qb q  vdd vdd ASAP7_PFET_SRAM L={21.0 + dlg_nm} Nfin=1 dTfin={dtfin_nm} dVth={dphim_qb}
Mn_qb qb q  0   0   ASAP7_NFET_SRAM L={21.0 + dlg_nm} Nfin=2 dTfin={dtfin_nm} dVth={dphim_qb}

* Heavy bitline access disturbance
R_pg_q  vdd q  5500
R_pg_qb vdd qb 5500

* Read-upset / metastable collapse condition: differential storage margin < 0.20 V
.unsafe v(q) - v(qb) < 0.20
.end
