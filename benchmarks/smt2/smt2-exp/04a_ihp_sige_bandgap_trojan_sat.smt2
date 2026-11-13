; ============================================================================
; Benchmark : Suite A-04a: IHP SG13G2 130nm SiGe HBT + PMOS Mirror Bandgap WITHOUT Startup Guard (Analog Trojan SAT)
; PDK       : ihp_sg13g2 (Open 130nm SiGe BiCMOS (IHP SG13G2 class: heterojunction SiGe HBT with Ge bandgap narrowing + Kirk high-injection roll-off))
; Dialect   : smt2-exp (QF_NRA + transcendental exp)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :status sat)

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
; Node voltage v(vc1) [V]
(declare-fun v_vc1 () Real)
(assert (and (>= v_vc1 0.0) (<= v_vc1 3.4)))
; Softplus auxiliary y = ln(1 + exp(z)) for Mp1_f
(declare-fun y_sp_Mp1_f_1 () Real)
(assert (and (>= y_sp_Mp1_f_1 0.0) (<= y_sp_Mp1_f_1 2000.0)))
; Softplus auxiliary y = ln(1 + exp(z)) for Mp1_r
(declare-fun y_sp_Mp1_r_2 () Real)
(assert (and (>= y_sp_Mp1_r_2 0.0) (<= y_sp_Mp1_r_2 2000.0)))
; Transistor channel current (Mp1)
(declare-fun i_Mp1 () Real)
(assert (and (>= i_Mp1 (- 5.0)) (<= i_Mp1 5.0)))
; Node voltage v(ref) [V]
(declare-fun v_ref () Real)
(assert (and (>= v_ref (- 0.05)) (<= v_ref 1.6)))
; Softplus auxiliary y = ln(1 + exp(z)) for Mp2_f
(declare-fun y_sp_Mp2_f_3 () Real)
(assert (and (>= y_sp_Mp2_f_3 0.0) (<= y_sp_Mp2_f_3 2000.0)))
; Softplus auxiliary y = ln(1 + exp(z)) for Mp2_r
(declare-fun y_sp_Mp2_r_4 () Real)
(assert (and (>= y_sp_Mp2_r_4 0.0) (<= y_sp_Mp2_r_4 2000.0)))
; Transistor channel current (Mp2)
(declare-fun i_Mp2 () Real)
(assert (and (>= i_Mp2 (- 5.0)) (<= i_Mp2 5.0)))
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
(assert (and (>= v_ve2 (- 0.05)) (<= v_ve2 1.2)))
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
; Pure-exp softplus link exp(y) = 1 + exp(z) (Mp1_f)
(assert (= (exp y_sp_Mp1_f_1) (+ 1.0 (exp (/ (- (- (- v_vdd v_vc1) 0.43) (* 0.74 (- v_vdd v_vdd))) 0.03826096)))))
; Pure-exp softplus link exp(y) = 1 + exp(z) (Mp1_r)
(assert (= (exp y_sp_Mp1_r_2) (+ 1.0 (exp (/ (- (- (- v_vdd v_vc1) 0.43) (* 0.74 (- v_vdd v_vc1))) 0.03826096)))))
; Transistor constitutive current (Mp1, model SG13_PMOS)
(assert (= i_Mp1 (- (* (/ 4.08 1000000.0) (- (* y_sp_Mp1_f_1 y_sp_Mp1_f_1) (* y_sp_Mp1_r_2 y_sp_Mp1_r_2))))))
; Pure-exp softplus link exp(y) = 1 + exp(z) (Mp2_f)
(assert (= (exp y_sp_Mp2_f_3) (+ 1.0 (exp (/ (- (- (- v_vdd v_vc1) 0.43) (* 0.74 (- v_vdd v_vdd))) 0.03826096)))))
; Pure-exp softplus link exp(y) = 1 + exp(z) (Mp2_r)
(assert (= (exp y_sp_Mp2_r_4) (+ 1.0 (exp (/ (- (- (- v_vdd v_vc1) 0.43) (* 0.74 (- v_vdd v_ref))) 0.03826096)))))
; Transistor constitutive current (Mp2, model SG13_PMOS)
(assert (= i_Mp2 (- (* (/ 4.08 1000000.0) (- (* y_sp_Mp2_f_3 y_sp_Mp2_f_3) (* y_sp_Mp2_r_4 y_sp_Mp2_r_4))))))
; Algebraic sqrt constraint skirk_Q1^2 = radicand (Monotone Kirk high-injection collector roll-off factor (Q1))
(assert (= (* skirk_Q1 skirk_Q1) (+ 1.0 (/ (* (* (* (/ 3.2 1000000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ v_ref (* (/ 8.617333262 100000.0) temp_k))) 1.0)) (* (* (/ 3.2 1000000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ v_ref (* (/ 8.617333262 100000.0) temp_k))) 1.0))) (/ 1.44 10000.0)))))
; BJT/SiGe-HBT collector transport current (Q1)
(assert (= ic_Q1 (- (- (/ (* (* (/ 3.2 1000000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ v_ref (* (/ 8.617333262 100000.0) temp_k))) 1.0)) skirk_Q1) (* (* (/ 3.2 1000000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_vc1) (* (/ 8.617333262 100000.0) temp_k))) 1.0))) (/ (* (* (/ 3.2 1000000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_vc1) (* (/ 8.617333262 100000.0) temp_k))) 1.0)) 8.0))))
; BJT/SiGe-HBT base recombination current (Q1)
(assert (= ib_Q1 (+ (/ (* (* (/ 3.2 1000000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ v_ref (* (/ 8.617333262 100000.0) temp_k))) 1.0)) 380.0) (/ (* (* (/ 3.2 1000000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_vc1) (* (/ 8.617333262 100000.0) temp_k))) 1.0)) 8.0))))
; Algebraic sqrt constraint skirk_Q2^2 = radicand (Monotone Kirk high-injection collector roll-off factor (Q2))
(assert (= (* skirk_Q2 skirk_Q2) (+ 1.0 (/ (* (* (* (/ 2.56 100000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_ve2) (* (/ 8.617333262 100000.0) temp_k))) 1.0)) (* (* (/ 2.56 100000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_ve2) (* (/ 8.617333262 100000.0) temp_k))) 1.0))) (/ 1.44 10000.0)))))
; BJT/SiGe-HBT collector transport current (Q2)
(assert (= ic_Q2 (- (- (/ (* (* (/ 2.56 100000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_ve2) (* (/ 8.617333262 100000.0) temp_k))) 1.0)) skirk_Q2) (* (* (/ 2.56 100000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_vc1) (* (/ 8.617333262 100000.0) temp_k))) 1.0))) (/ (* (* (/ 2.56 100000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_vc1) (* (/ 8.617333262 100000.0) temp_k))) 1.0)) 8.0))))
; BJT/SiGe-HBT base recombination current (Q2)
(assert (= ib_Q2 (+ (/ (* (* (/ 2.56 100000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_ve2) (* (/ 8.617333262 100000.0) temp_k))) 1.0)) 380.0) (/ (* (* (/ 2.56 100000000000000000.0) (exp (/ deg_ge (* (/ 8.617333262 100000.0) temp_k)))) (- (exp (/ (- v_ref v_vc1) (* (/ 8.617333262 100000.0) temp_k))) 1.0)) 8.0))))
; MNA Kirchhoff Current Law at node `ref`
(assert (= (+ (+ (+ i_Mp2 ib_Q1) ib_Q2) (/ v_ref 18000.0)) 0.0))
; MNA Kirchhoff Current Law at node `vc1`
(assert (= (+ (+ i_Mp1 ic_Q1) ic_Q2) 0.0))
; MNA Kirchhoff Current Law at node `vdd`
(assert (= (- (- i_Vsup i_Mp1) i_Mp2) 0.0))
; MNA Kirchhoff Current Law at node `ve2`
(assert (= (+ (- (- ic_Q2) ib_Q2) (/ v_ve2 2200.0)) 0.0))

; --- Negated Safety Specification (.unsafe) ---
(assert (< v_ref 0.4))

(check-sat)
(exit)
