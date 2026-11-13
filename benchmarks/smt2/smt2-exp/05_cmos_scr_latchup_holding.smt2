; ============================================================================
; Benchmark : Suite A-05: Parasitic 4-Layer p-n-p-n CMOS SCR Latchup Below Holding Envelope
; PDK       : gf180mcu (Open 180nm Planar Bulk CMOS (GF180MCU class: 3.3V/5V I/O + ESD diodes + parasitic well/substrate SCR))
; Dialect   : smt2-exp (QF_NRA + transcendental exp)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)

; --- Continuous Parameter / Defect / Litho Uncertainty Box ---
(declare-fun vsupply () Real)
(assert (and (>= vsupply 0.8) (<= vsupply 1.0)))
(declare-fun r_well () Real)
(assert (and (>= r_well 80.0) (<= r_well 150.0)))
(declare-fun r_sub () Real)
(assert (and (>= r_sub 60.0) (<= r_sub 120.0)))
(declare-fun vt () Real)
(assert (and (>= vt 0.024) (<= vt 0.031)))

; --- State & Auxiliary Variables ---
; Node voltage v(sup) [V]
(declare-fun v_sup () Real)
(assert (and (>= v_sup 0.8) (<= v_sup 1.0)))
; Voltage source branch current (Vsup)
(declare-fun i_Vsup () Real)
(assert (and (>= i_Vsup (- 0.05)) (<= i_Vsup 0.05)))
; Node voltage v(nwell) [V]
(declare-fun v_nwell () Real)
(assert (and (>= v_nwell 0.0) (<= v_nwell 1.05)))
; Node voltage v(psub) [V]
(declare-fun v_psub () Real)
(assert (and (>= v_psub (- 0.05)) (<= v_psub 1.0)))
; BJT/HBT collector current (Qpnp)
(declare-fun ic_Qpnp () Real)
(assert (and (>= ic_Qpnp (- 2.0)) (<= ic_Qpnp 2.0)))
; BJT/HBT base current (Qpnp)
(declare-fun ib_Qpnp () Real)
(assert (and (>= ib_Qpnp (- 1.0)) (<= ib_Qpnp 1.0)))
; BJT/HBT collector current (Qnpn)
(declare-fun ic_Qnpn () Real)
(assert (and (>= ic_Qnpn (- 2.0)) (<= ic_Qnpn 2.0)))
; BJT/HBT base current (Qnpn)
(declare-fun ib_Qnpn () Real)
(assert (and (>= ib_Qnpn (- 1.0)) (<= ib_Qnpn 1.0)))

; --- Constitutive & Conservation Laws (MNA / PCB EM / TCAD) ---
; Voltage source constitutive equation (Vsup)
(assert (= v_sup vsupply))
; BJT/SiGe-HBT collector transport current (Qpnp)
(assert (= ic_Qpnp (- (- (- (* (/ 3.6 10000000000000000.0) (- (exp (/ (- v_sup v_nwell) vt)) 1.0)) (* (/ 3.6 10000000000000000.0) (- (exp (/ (- v_psub v_nwell) vt)) 1.0))) (/ (* (/ 3.6 10000000000000000.0) (- (exp (/ (- v_psub v_nwell) vt)) 1.0)) 1.5)))))
; BJT/SiGe-HBT base recombination current (Qpnp)
(assert (= ib_Qpnp (- (+ (/ (* (/ 3.6 10000000000000000.0) (- (exp (/ (- v_sup v_nwell) vt)) 1.0)) 18.0) (/ (* (/ 3.6 10000000000000000.0) (- (exp (/ (- v_psub v_nwell) vt)) 1.0)) 1.5)))))
; BJT/SiGe-HBT collector transport current (Qnpn)
(assert (= ic_Qnpn (- (- (* (/ 5.0 10000000000000000.0) (- (exp (/ v_psub vt)) 1.0)) (* (/ 5.0 10000000000000000.0) (- (exp (/ (- v_psub v_nwell) vt)) 1.0))) (/ (* (/ 5.0 10000000000000000.0) (- (exp (/ (- v_psub v_nwell) vt)) 1.0)) 2.0))))
; BJT/SiGe-HBT base recombination current (Qnpn)
(assert (= ib_Qnpn (+ (/ (* (/ 5.0 10000000000000000.0) (- (exp (/ v_psub vt)) 1.0)) 45.0) (/ (* (/ 5.0 10000000000000000.0) (- (exp (/ (- v_psub v_nwell) vt)) 1.0)) 2.0))))
; MNA Kirchhoff Current Law at node `nwell`
(assert (= (+ (+ (- (/ (- v_sup v_nwell) r_well)) ib_Qpnp) ic_Qnpn) 0.0))
; MNA Kirchhoff Current Law at node `psub`
(assert (= (+ (+ (/ v_psub r_sub) ic_Qpnp) ib_Qnpn) 0.0))
; MNA Kirchhoff Current Law at node `sup`
(assert (= (- (- (+ i_Vsup (/ (- v_sup v_nwell) r_well)) ic_Qpnp) ib_Qpnp) 0.0))

; --- Negated Safety Specification (.unsafe) ---
(assert (> (- i_Vsup) 0.005))

(check-sat)
(exit)
