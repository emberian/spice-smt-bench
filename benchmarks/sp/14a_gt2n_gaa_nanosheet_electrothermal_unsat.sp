* Suite D-14a: 2nm Gate-All-Around (gt2n) 3-Stacked Nanosheet Coupled Electro-Thermal TCAD (Safe UNSAT)
.pdk gt2n
.expected unsat
.mode dc
.default_vbound [-0.5, 2.5]

* Continuous 4D nanosheet thickness, inner-spacer, ambient temperature, and BEOL thermal resistance box:
*   dtns_nm  : nanosheet thickness delta [-0.35nm, +0.35nm] around T_ns = 5.0nm
*   dlisp_nm : inner-spacer dielectric thickness delta [-0.50nm, +0.50nm] around L_isp = 5.5nm
*   tamb_k   : ambient die temperature [290K, 340K]
*   rth_kw   : per-stack thermal resistance to BEOL/substrate [1.2e5 K/W, 2.4e5 K/W]
.param dtns_nm  [-0.35, 0.35]
.param dlisp_nm [-0.50, 0.50]
.param tamb_k   [290.0, 340.0]
.param rth_kw   [120000.0, 240000.0]

* Active on-state self-heating point: V_GS = 0.65 V, V_DS = 0.65 V across 3 stacked nanosheets
.tcad_gaa_electrothermal gaa2n nx=6 nsheets=3 lg_nm=12.0 wns_nm=18.0 tns_nm={5.0 + dtns_nm} eot_nm=0.85 lisp_nm={5.5 + dlisp_nm} vgs=0.65 vds=0.65 tamb_k={tamb_k} rth_kw={rth_kw}

* Prove coupled electro-thermal fixed-point channel temperature T_ch stays below 410 K reliability ceiling
.unsafe T_ch_gaa2n > 410.0
.end
