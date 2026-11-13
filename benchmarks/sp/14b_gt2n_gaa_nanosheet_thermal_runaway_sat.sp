* Suite D-14b: 2nm Gate-All-Around (gt2n) Stacked Nanosheet Self-Heating Excursion Under Degraded Rth (SAT)
.pdk gt2n
.expected sat
.mode dc
.default_vbound [-0.5, 2.5]

* Buried-oxide / backside-PDN thermal bottleneck (high R_th) + elevated ambient + overdrive corner
.param dtns_nm  [-0.40, 0.60]
.param dlisp_nm [-0.80, 0.50]
.param tamb_k   [355.0, 385.0]
.param rth_kw   [800000.0, 1400000.0]

.tcad_gaa_electrothermal gaa2n nx=6 nsheets=3 lg_nm=12.0 wns_nm=18.0 tns_nm={5.0 + dtns_nm} eot_nm=0.85 lisp_nm={5.5 + dlisp_nm} vgs=0.75 vds=0.75 tamb_k={tamb_k} rth_kw={rth_kw}

* Coupled self-heating pushes nanosheet lattice temperature above 410 K reliability limit (SAT witness!)
.unsafe T_ch_gaa2n > 410.0
.end
