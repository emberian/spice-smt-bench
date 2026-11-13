; ============================================================================
; Benchmark : Suite A-04b: IHP SG13G2 130nm SiGe HBT Reference WITH Startup Keeper (Trojan Eliminated UNSAT)
; PDK       : ihp_sg13g2 (Open 130nm SiGe BiCMOS (IHP SG13G2 class: heterojunction SiGe HBT with Ge bandgap narrowing + Kirk high-injection roll-off))
; Dialect   : smt2-exp (QF_NRA + transcendental exp)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)

; --- Continuous Parameter / Defect / Litho Uncertainty Box ---
(declare-fun vdd () Real)
(assert (and (>= vdd 2.7) (<= vdd 3.3)))
(declare-fun temp_k () Real)
(assert (and (>= temp_k 273.0) (<= temp_k 373.0)))
(declare-fun deg_ge () Real)
(assert (and (>= deg_ge 0.08) (<= deg_ge 0.09)))

; --- State & Auxiliary Variables ---
; Node voltage v(vdd) [V]
(declare-fun v_vdd () Real)
(assert (and (>= v_vdd 2.7) (<= v_vdd 3.3)))
; Voltage source branch current (Vsup)
(declare-fun i_Vsup () Real)
(assert (and (>= i_Vsup (- 50.0)) (<= i_Vsup 50.0)))
; Node voltage v(ref) [V]
(declare-fun v_ref () Real)
(assert (and (>= v_ref (- 0.05)) (<= v_ref 1.8)))
; Monotone Kirk high-injection collector roll-off factor (Q1)
(declare-fun skirk_Q1 () Real)
(assert (and (>= skirk_Q1 1.0) (<= skirk_Q1 10000.0)))
; BJT/HBT collector current (Q1)
(declare-fun ic_Q1 () Real)
(assert (and (>= ic_Q1 (- 2.0)) (<= ic_Q1 2.0)))
; BJT/HBT base current (Q1)
(declare-fun ib_Q1 () Real)
(assert (and (>= ib_Q1 (- 1.0)) (<= ib_Q1 1.0)))
; Node voltage v(ve2) [V]
(declare-fun v_ve2 () Real)
(assert (and (>= v_ve2 (- 0.05)) (<= v_ve2 1.4)))
; Monotone Kirk high-injection collector roll-off factor (Q2)
(declare-fun skirk_Q2 () Real)
(assert (and (>= skirk_Q2 1.0) (<= skirk_Q2 10000.0)))
; BJT/HBT collector current (Q2)
(declare-fun ic_Q2 () Real)
(assert (and (>= ic_Q2 (- 2.0)) (<= ic_Q2 2.0)))
; BJT/HBT base current (Q2)
(declare-fun ib_Q2 () Real)
(assert (and (>= ib_Q2 (- 1.0)) (<= ib_Q2 1.0)))

; --- Constitutive & Conservation Laws (MNA / PCB EM / TCAD) ---
; Voltage source constitutive equation (Vsup)
(assert (= v_vdd vdd))
; Algebraic sqrt constraint skirk_Q1^2 = radicand (Monotone Kirk high-injection collector roll-off factor (Q1))
(assert (= (* skirk_Q1 skirk_Q1) (+ 1.0 (/ (* (* (* (/ 6.4 1000000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ v_ref (* (/ 8.617333262 100000.0) temp_k))) 1.0)) (* (* (/ 6.4 1000000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ v_ref (* (/ 8.617333262 100000.0) temp_k))) 1.0))) (/ 1.44 10000.0)))))
; BJT/SiGe-HBT collector transport current (Q1)
(assert (= ic_Q1 (- (- (/ (* (* (/ 6.4 1000000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ v_ref (* (/ 8.617333262 100000.0) temp_k))) 1.0)) skirk_Q1) (* (* (/ 6.4 1000000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_ref) (* (/ 8.617333262 100000.0) temp_k))) 1.0))) (/ (* (* (/ 6.4 1000000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_ref) (* (/ 8.617333262 100000.0) temp_k))) 1.0)) 8.0))))
; BJT/SiGe-HBT base recombination current (Q1)
(assert (= ib_Q1 (+ (/ (* (* (/ 6.4 1000000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ v_ref (* (/ 8.617333262 100000.0) temp_k))) 1.0)) 380.0) (/ (* (* (/ 6.4 1000000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_ref) (* (/ 8.617333262 100000.0) temp_k))) 1.0)) 8.0))))
; Algebraic sqrt constraint skirk_Q2^2 = radicand (Monotone Kirk high-injection collector roll-off factor (Q2))
(assert (= (* skirk_Q2 skirk_Q2) (+ 1.0 (/ (* (* (* (/ 2.56 100000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_ve2) (* (/ 8.617333262 100000.0) temp_k))) 1.0)) (* (* (/ 2.56 100000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_ve2) (* (/ 8.617333262 100000.0) temp_k))) 1.0))) (/ 1.44 10000.0)))))
; BJT/SiGe-HBT collector transport current (Q2)
(assert (= ic_Q2 (- (- (/ (* (* (/ 2.56 100000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_ve2) (* (/ 8.617333262 100000.0) temp_k))) 1.0)) skirk_Q2) (* (* (/ 2.56 100000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_vdd) (* (/ 8.617333262 100000.0) temp_k))) 1.0))) (/ (* (* (/ 2.56 100000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_vdd) (* (/ 8.617333262 100000.0) temp_k))) 1.0)) 8.0))))
; BJT/SiGe-HBT base recombination current (Q2)
(assert (= ib_Q2 (+ (/ (* (* (/ 2.56 100000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_ve2) (* (/ 8.617333262 100000.0) temp_k))) 1.0)) 380.0) (/ (* (* (/ 2.56 100000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_vdd) (* (/ 8.617333262 100000.0) temp_k))) 1.0)) 8.0))))
; MNA Kirchhoff Current Law at node `ref`
(assert (= (+ (+ (+ (+ (- (/ (- v_vdd v_ref) 4200.0)) (/ v_ref 80000.0)) ic_Q1) ib_Q1) ib_Q2) 0.0))
; MNA Kirchhoff Current Law at node `vdd`
(assert (= (+ (+ i_Vsup (/ (- v_vdd v_ref) 4200.0)) ic_Q2) 0.0))
; MNA Kirchhoff Current Law at node `ve2`
(assert (= (+ (- (- ic_Q2) ib_Q2) (/ v_ve2 1800.0)) 0.0))

; --- Negated Safety Specification (.unsafe) ---
(assert (< v_ref 0.4))

(check-sat)
(exit)
