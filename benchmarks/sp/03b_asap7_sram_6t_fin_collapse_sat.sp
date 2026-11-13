* Six-transistor FinFET SRAM read-disturb, stored 1; manufacturing-defect twin b
.pdk asap7
.expected sat
.mode tran dt=10p steps=20 method=be
.default_vbound [-0.05, 0.80]
.param dtfin_nm [-0.35, 0.35]
.param dt_fin_pdb [-2.2, -1.4]
.param dphim [0.42, 0.48]
.bound v(q) [-0.05, 0.80]
.bound v(qb) [-0.05, 0.80]
.init v(q) = 0.70
.init v(qb) = 0.0
Vsup vdd 0 DC 0.70
Vbl bl 0 DC 0.70
Vblb blb 0 DC 0.70
Vwl wl 0 DC 0.70
Mpu_a q qb vdd vdd ASAP7_PFET_SRAM Nfin=1 dTfin={dtfin_nm}
Mpd_a q qb 0 0 ASAP7_NFET_SRAM Nfin=2 dTfin={dtfin_nm}
Mpg_a bl wl q 0 ASAP7_NFET_SRAM Nfin=1
Mpu_b qb q vdd vdd ASAP7_PFET_SRAM Nfin=1 dTfin={dtfin_nm}
Mpd_b qb q 0 0 ASAP7_NFET_SRAM Nfin=2 dTfin={dt_fin_pdb} dVth={dphim}
Mpg_b blb wl qb 0 ASAP7_NFET_SRAM Nfin=1
Cq q 0 1f
Cqb qb 0 1f
.unsafe v(q) - v(qb) < 0.12
.end
