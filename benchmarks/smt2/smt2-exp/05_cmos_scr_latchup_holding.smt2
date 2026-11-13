; ============================================================================
; Benchmark : Suite A-05: Parasitic 4-Layer p-n-p-n CMOS SCR Latchup Below Holding Envelope
; PDK       : gf180mcu (Open 180nm Planar Bulk CMOS (GF180MCU class: 3.3V/5V I/O + ESD diodes + parasitic well/substrate SCR))
; Dialect   : smt2-exp (QF_NRA + transcendental exp)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic ALL)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)

; --- Continuous Parameter / Defect / Litho Uncertainty Box ---
(declare-fun vsupply () Real)
(assert (and (>= vsupply 0.7) (<= vsupply 0.88)))
(declare-fun r_well () Real)
(assert (and (>= r_well 6.0) (<= r_well 14.0)))
(declare-fun r_sub () Real)
(assert (and (>= r_sub 5.0) (<= r_sub 12.0)))
(declare-fun temp_k () Real)
(assert (and (>= temp_k 273.0) (<= temp_k 398.0)))

; --- State & Auxiliary Variables ---
; Node voltage v(sup) [V]
(declare-fun v_sup () Real)
(assert (and (>= v_sup 0.7) (<= v_sup 0.88)))
; Voltage source branch current (Vsup)
(declare-fun i_Vsup () Real)
; Node voltage v(nwell) [V]
(declare-fun v_nwell () Real)
(assert (and (>= v_nwell 0.0) (<= v_nwell 1.05)))
; Node voltage v(psub) [V]
(declare-fun v_psub () Real)
(assert (and (>= v_psub (- 0.05)) (<= v_psub 1.0)))
; Node voltage v(ep) [V]
(declare-fun v_ep () Real)
(assert (and (>= v_ep (- 0.1)) (<= v_ep 1.3)))
; Node voltage v(en) [V]
(declare-fun v_en () Real)
(assert (and (>= v_en (- 0.1)) (<= v_en 1.3)))
; BJT/HBT collector current (Qpnp)
(declare-fun ic_Qpnp () Real)
; BJT/HBT base current (Qpnp)
(declare-fun ib_Qpnp () Real)
; BJT/HBT collector current (Qnpn)
(declare-fun ic_Qnpn () Real)
; BJT/HBT base current (Qnpn)
(declare-fun ib_Qnpn () Real)

; --- Constitutive & Conservation Laws (MNA / PCB EM / TCAD) ---
; Voltage source constitutive equation (Vsup)
(assert (= v_sup vsupply))
; BJT/SiGe-HBT collector transport current (Qpnp)
(assert (= ic_Qpnp (- (- (- (* (* 0.00000000000000036 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ 1.12 (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_ep v_nwell) (* 0.00008617333262 temp_k))) 1.0)) (* (* 0.00000000000000036 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ 1.12 (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_psub v_nwell) (* 0.00008617333262 temp_k))) 1.0))) (/ (* (* 0.00000000000000036 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ 1.12 (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_psub v_nwell) (* 0.00008617333262 temp_k))) 1.0)) 2.0)))))
; BJT/SiGe-HBT base recombination current (Qpnp)
(assert (= ib_Qpnp (- (+ (/ (* (* 0.00000000000000036 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ 1.12 (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_ep v_nwell) (* 0.00008617333262 temp_k))) 1.0)) 18.0) (/ (* (* 0.00000000000000036 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ 1.12 (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_psub v_nwell) (* 0.00008617333262 temp_k))) 1.0)) 2.0)))))
; BJT/SiGe-HBT collector transport current (Qnpn)
(assert (= ic_Qnpn (- (- (* (* 0.0000000000000005 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ 1.12 (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_psub v_en) (* 0.00008617333262 temp_k))) 1.0)) (* (* 0.0000000000000005 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ 1.12 (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_psub v_nwell) (* 0.00008617333262 temp_k))) 1.0))) (/ (* (* 0.0000000000000005 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ 1.12 (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_psub v_nwell) (* 0.00008617333262 temp_k))) 1.0)) 2.0))))
; BJT/SiGe-HBT base recombination current (Qnpn)
(assert (= ib_Qnpn (+ (/ (* (* 0.0000000000000005 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ 1.12 (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_psub v_en) (* 0.00008617333262 temp_k))) 1.0)) 45.0) (/ (* (* 0.0000000000000005 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ 1.12 (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_psub v_nwell) (* 0.00008617333262 temp_k))) 1.0)) 2.0))))
; MNA Kirchhoff Current Law at node `en`
(assert (= (- (- (/ v_en 20.0) ic_Qnpn) ib_Qnpn) 0.0))
; MNA Kirchhoff Current Law at node `ep`
(assert (= (- (- (- (/ (- v_sup v_ep) 20.0)) ic_Qpnp) ib_Qpnp) 0.0))
; MNA Kirchhoff Current Law at node `nwell`
(assert (= (+ (+ (- (/ (- v_sup v_nwell) r_well)) ib_Qpnp) ic_Qnpn) 0.0))
; MNA Kirchhoff Current Law at node `psub`
(assert (= (+ (+ (/ v_psub r_sub) ic_Qpnp) ib_Qnpn) 0.0))
; MNA Kirchhoff Current Law at node `sup`
(assert (= (+ (+ i_Vsup (/ (- v_sup v_nwell) r_well)) (/ (- v_sup v_ep) 20.0)) 0.0))

(assert (=> (>= (- 43.32353432118352 (/ 1.12 (* 0.00008617333262 temp_k))) 25.0) (>= (exp (- 43.32353432118352 (/ 1.12 (* 0.00008617333262 temp_k)))) 8000000000.0)))
(assert (=> (>= (/ (- v_ep v_nwell) (* 0.00008617333262 temp_k)) 25.0) (>= (exp (/ (- v_ep v_nwell) (* 0.00008617333262 temp_k))) 8000000000.0)))
(assert (=> (>= (/ (- v_psub v_en) (* 0.00008617333262 temp_k)) 25.0) (>= (exp (/ (- v_psub v_en) (* 0.00008617333262 temp_k))) 8000000000.0)))
(assert (=> (>= (/ (- v_psub v_nwell) (* 0.00008617333262 temp_k)) 25.0) (>= (exp (/ (- v_psub v_nwell) (* 0.00008617333262 temp_k))) 8000000000.0)))
; --- Negated Safety Specification (.unsafe) ---
(assert (> (- i_Vsup) 0.005))

(check-sat)
(exit)
