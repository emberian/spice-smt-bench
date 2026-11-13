; ============================================================================
; Benchmark : Suite A-01: Shockley ESD Diode Clipper Over Continuous Supply & Temperature Box
; PDK       : gf180mcu (Open 180nm Planar Bulk CMOS (GF180MCU class: 3.3V/5V I/O + ESD diodes + parasitic well/substrate SCR))
; Dialect   : smt2-exp (QF_NRA + transcendental exp)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic ALL)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)

; --- Continuous Parameter / Defect / Litho Uncertainty Box ---
(declare-fun v_sup () Real)
(assert (and (>= v_sup 3.0) (<= v_sup 3.6)))
(declare-fun vt () Real)
(assert (and (>= vt 0.0235) (<= vt 0.0322)))

; --- State & Auxiliary Variables ---
; Node voltage v(in) [V]
(declare-fun v_in () Real)
(assert (and (>= v_in 3.0) (<= v_in 3.6)))
; Voltage source branch current (Vdd)
(declare-fun i_Vdd () Real)
(assert (and (>= i_Vdd (- 0.01)) (<= i_Vdd 0.01)))
; Node voltage v(out) [V]
(declare-fun v_out () Real)
(assert (and (>= v_out (- 0.5)) (<= v_out 3.6)))
; Shockley diode current (D1)
(declare-fun i_D1 () Real)
(assert (and (>= i_D1 (- 0.001)) (<= i_D1 1.0)))

; --- Constitutive & Conservation Laws (MNA / PCB EM / TCAD) ---
; Voltage source constitutive equation (Vdd)
(assert (= v_in v_sup))
; Shockley diode law (D1)
(assert (= i_D1 (* 0.000000000001 (- (exp (/ v_out (* 1.05 vt))) 1.0))))
; MNA Kirchhoff Current Law at node `in`
(assert (= (+ i_Vdd (/ (- v_in v_out) 1000.0)) 0.0))
; MNA Kirchhoff Current Law at node `out`
(assert (= (+ (+ (- (/ (- v_in v_out) 1000.0)) (/ v_out 10000.0)) i_D1) 0.0))

(assert (=> (>= (/ v_out (* 1.05 vt)) 25.0) (>= (exp (/ v_out (* 1.05 vt))) 8000000000.0)))
; --- Negated Safety Specification (.unsafe) ---
(assert (> v_out 0.85))

(check-sat)
(exit)
