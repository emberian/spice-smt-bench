* Suite A-03a: ASAP7 7nm 6T FinFET SRAM Bitcell Read-Disturb Retention Margin (In-Spec EUV/SAQP Box)
.pdk asap7
.expected unsat
.mode dc
.default_vbound [-0.05, 0.85]

* Tight 7nm EUV + SAQP fin-etch & workfunction mismatch box
.param vdd       [0.67, 0.73]
.param dtfin_nm  [-0.35, 0.35]
.param dlg_nm    [-0.80, 0.80]
.param dphim_q   [-0.018, 0.018]
.param dphim_qb  [-0.018, 0.018]

* Focus state box on stored-'1' retention basin (q high, qb low under bitline read disturb)
.bound v(vdd) [0.67, 0.73]
.bound v(q)   [0.45, 0.75]
.bound v(qb)  [0.00, 0.28]

Vsup vdd 0 DC {vdd}

* Cross-coupled 1:1:2 FinFET SRAM inverters + precharged bitline read-access load
Mp_q  q  qb vdd vdd ASAP7_PFET_SRAM L={21.0 + dlg_nm} Nfin=1 dTfin={dtfin_nm} dVth={dphim_q}
Mn_q  q  qb 0   0   ASAP7_NFET_SRAM L={21.0 + dlg_nm} Nfin=2 dTfin={dtfin_nm} dVth={dphim_q}
Mp_qb qb q  vdd vdd ASAP7_PFET_SRAM L={21.0 + dlg_nm} Nfin=1 dTfin={dtfin_nm} dVth={dphim_qb}
Mn_qb qb q  0   0   ASAP7_NFET_SRAM L={21.0 + dlg_nm} Nfin=2 dTfin={dtfin_nm} dVth={dphim_qb}

* Pass-gate read-disturb equivalent pull-up to precharged bitlines
R_pg_q  vdd q  14000
R_pg_qb vdd qb 14000

* Negated safety target: differential state margin collapses below 0.25 V
.unsafe v(q) - v(qb) < 0.25
.end
