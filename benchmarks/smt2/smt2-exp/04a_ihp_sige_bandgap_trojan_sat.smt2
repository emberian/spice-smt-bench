; ============================================================================
; Benchmark : PMOS mirror / area-ratio SiGe HBT bandgap twin a
; PDK       : ihp_sg13g2 (Open 130nm SiGe BiCMOS (IHP SG13G2 class: heterojunction SiGe HBT with Ge bandgap narrowing + Kirk high-injection roll-off))
; Dialect   : smt2-exp (QF_NRA + transcendental exp)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic ALL)
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
(assert (and (>= v_vdd (- 0.1)) (<= v_vdd 3.6)))
; Voltage source branch current (Vsup)
(declare-fun i_Vsup () Real)
; Node voltage v(ref) [V]
(declare-fun v_ref () Real)
(assert (and (>= v_ref (- 0.05)) (<= v_ref 1.6)))
; Node voltage v(vc1) [V]
(declare-fun v_vc1 () Real)
(assert (and (>= v_vc1 (- 0.1)) (<= v_vc1 3.6)))
; Softplus auxiliary y = ln(1 + exp(z)) for Mp1_f
(declare-fun y_sp_Mp1_f_1 () Real)
; Softplus auxiliary y = ln(1 + exp(z)) for Mp1_r
(declare-fun y_sp_Mp1_r_2 () Real)
; Transistor channel current (Mp1)
(declare-fun i_Mp1 () Real)
; Softplus auxiliary y = ln(1 + exp(z)) for Mp2_f
(declare-fun y_sp_Mp2_f_3 () Real)
; Softplus auxiliary y = ln(1 + exp(z)) for Mp2_r
(declare-fun y_sp_Mp2_r_4 () Real)
; Transistor channel current (Mp2)
(declare-fun i_Mp2 () Real)
; Node voltage v(e0) [V]
(declare-fun v_e0 () Real)
(assert (and (>= v_e0 (- 0.1)) (<= v_e0 3.6)))
; Monotone Kirk high-injection collector roll-off factor (Q1)
(declare-fun skirk_Q1 () Real)
; BJT/HBT collector current (Q1)
(declare-fun ic_Q1 () Real)
; BJT/HBT base current (Q1)
(declare-fun ib_Q1 () Real)
; Node voltage v(ve2) [V]
(declare-fun v_ve2 () Real)
(assert (and (>= v_ve2 (- 0.1)) (<= v_ve2 3.6)))
; Monotone Kirk high-injection collector roll-off factor (Q2)
(declare-fun skirk_Q2 () Real)
; BJT/HBT collector current (Q2)
(declare-fun ic_Q2 () Real)
; BJT/HBT base current (Q2)
(declare-fun ib_Q2 () Real)

; --- Constitutive & Conservation Laws (MNA / PCB EM / TCAD) ---
; Voltage source constitutive equation (Vsup)
(assert (= v_vdd vdd))
; Positive device temperature
(assert (> temp_k 0.0))
; Positive thermal voltage
(assert (> (* 0.00008617333262 temp_k) 0.0))
; Softplus domain
(assert (>= y_sp_Mp1_f_1 0.0))
; Pure-exp softplus link exp(y) = 1 + exp(z) (Mp1_f)
(assert (= (exp y_sp_Mp1_f_1) (+ 1.0 (exp (/ (- (* 0.74 (- (- v_vdd v_vc1) (+ 0.43 (* (- 0.00085) (- temp_k 300.0))))) (- v_vdd v_vdd)) (* 2.0 (* 0.00008617333262 temp_k)))))))
; Softplus domain
(assert (>= y_sp_Mp1_r_2 0.0))
; Pure-exp softplus link exp(y) = 1 + exp(z) (Mp1_r)
(assert (= (exp y_sp_Mp1_r_2) (+ 1.0 (exp (/ (- (* 0.74 (- (- v_vdd v_vc1) (+ 0.43 (* (- 0.00085) (- temp_k 300.0))))) (- v_vdd v_ref)) (* 2.0 (* 0.00008617333262 temp_k)))))))
; Transistor constitutive current (Mp1, model SG13_PMOS)
(assert (= i_Mp1 (- (* 0.00000408 (- (* y_sp_Mp1_f_1 y_sp_Mp1_f_1) (* y_sp_Mp1_r_2 y_sp_Mp1_r_2))))))
; Positive device temperature
(assert (> temp_k 0.0))
; Positive thermal voltage
(assert (> (* 0.00008617333262 temp_k) 0.0))
; Softplus domain
(assert (>= y_sp_Mp2_f_3 0.0))
; Pure-exp softplus link exp(y) = 1 + exp(z) (Mp2_f)
(assert (= (exp y_sp_Mp2_f_3) (+ 1.0 (exp (/ (- (* 0.74 (- (- v_vdd v_vc1) (+ 0.43 (* (- 0.00085) (- temp_k 300.0))))) (- v_vdd v_vdd)) (* 2.0 (* 0.00008617333262 temp_k)))))))
; Softplus domain
(assert (>= y_sp_Mp2_r_4 0.0))
; Pure-exp softplus link exp(y) = 1 + exp(z) (Mp2_r)
(assert (= (exp y_sp_Mp2_r_4) (+ 1.0 (exp (/ (- (* 0.74 (- (- v_vdd v_vc1) (+ 0.43 (* (- 0.00085) (- temp_k 300.0))))) (- v_vdd v_vc1)) (* 2.0 (* 0.00008617333262 temp_k)))))))
; Transistor constitutive current (Mp2, model SG13_PMOS)
(assert (= i_Mp2 (- (* 0.00000408 (- (* y_sp_Mp2_f_3 y_sp_Mp2_f_3) (* y_sp_Mp2_r_4 y_sp_Mp2_r_4))))))
; Nonnegative square root
(assert (>= skirk_Q1 0.0))
; Algebraic sqrt constraint skirk_Q1^2 = radicand (Monotone Kirk high-injection collector roll-off factor (Q1))
(assert (= (* skirk_Q1 skirk_Q1) (+ 1.0 (/ (* (* (* 0.0000000000000000032 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ (- 1.12 deg_ge) (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_ref v_e0) (* 0.00008617333262 temp_k))) 1.0)) (* (* 0.0000000000000000032 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ (- 1.12 deg_ge) (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_ref v_e0) (* 0.00008617333262 temp_k))) 1.0))) 0.000144))))
; BJT/SiGe-HBT collector transport current (Q1)
(assert (= ic_Q1 (- (- (* (/ (* (* 0.0000000000000000032 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ (- 1.12 deg_ge) (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_ref v_e0) (* 0.00008617333262 temp_k))) 1.0)) skirk_Q1) (+ 1.0 (/ (- v_ref v_e0) 45.0))) (* (* 0.0000000000000000032 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ (- 1.12 deg_ge) (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_ref v_ref) (* 0.00008617333262 temp_k))) 1.0))) (/ (* (* 0.0000000000000000032 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ (- 1.12 deg_ge) (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_ref v_ref) (* 0.00008617333262 temp_k))) 1.0)) 8.0))))
; BJT/SiGe-HBT base recombination current (Q1)
(assert (= ib_Q1 (+ (/ (* (* 0.0000000000000000032 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ (- 1.12 deg_ge) (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_ref v_e0) (* 0.00008617333262 temp_k))) 1.0)) 380.0) (/ (* (* 0.0000000000000000032 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ (- 1.12 deg_ge) (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_ref v_ref) (* 0.00008617333262 temp_k))) 1.0)) 8.0))))
; Nonnegative square root
(assert (>= skirk_Q2 0.0))
; Algebraic sqrt constraint skirk_Q2^2 = radicand (Monotone Kirk high-injection collector roll-off factor (Q2))
(assert (= (* skirk_Q2 skirk_Q2) (+ 1.0 (/ (* (* (* 0.0000000000000000256 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ (- 1.12 deg_ge) (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_ref v_ve2) (* 0.00008617333262 temp_k))) 1.0)) (* (* 0.0000000000000000256 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ (- 1.12 deg_ge) (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_ref v_ve2) (* 0.00008617333262 temp_k))) 1.0))) 0.009216))))
; BJT/SiGe-HBT collector transport current (Q2)
(assert (= ic_Q2 (- (- (* (/ (* (* 0.0000000000000000256 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ (- 1.12 deg_ge) (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_ref v_ve2) (* 0.00008617333262 temp_k))) 1.0)) skirk_Q2) (+ 1.0 (/ (- v_vc1 v_ve2) 45.0))) (* (* 0.0000000000000000256 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ (- 1.12 deg_ge) (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_ref v_vc1) (* 0.00008617333262 temp_k))) 1.0))) (/ (* (* 0.0000000000000000256 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ (- 1.12 deg_ge) (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_ref v_vc1) (* 0.00008617333262 temp_k))) 1.0)) 8.0))))
; BJT/SiGe-HBT base recombination current (Q2)
(assert (= ib_Q2 (+ (/ (* (* 0.0000000000000000256 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ (- 1.12 deg_ge) (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_ref v_ve2) (* 0.00008617333262 temp_k))) 1.0)) 380.0) (/ (* (* 0.0000000000000000256 (* (* (* (/ temp_k 300.0) (/ temp_k 300.0)) (/ temp_k 300.0)) (exp (- 43.32353432118352 (/ (- 1.12 deg_ge) (* 0.00008617333262 temp_k)))))) (- (exp (/ (- v_ref v_vc1) (* 0.00008617333262 temp_k))) 1.0)) 8.0))))
; MNA Kirchhoff Current Law at node `e0`
(assert (= (+ (- (- (- ic_Q1) ib_Q1) (/ (- v_ve2 v_e0) 2200.0)) (/ v_e0 10400.0)) 0.0))
; MNA Kirchhoff Current Law at node `ref`
(assert (= (+ (+ (+ (+ i_Mp1 ic_Q1) ib_Q1) ib_Q2) (/ v_ref 10000000.0)) 0.0))
; MNA Kirchhoff Current Law at node `vc1`
(assert (= (+ i_Mp2 ic_Q2) 0.0))
; MNA Kirchhoff Current Law at node `vdd`
(assert (= (- (- i_Vsup i_Mp1) i_Mp2) 0.0))
; MNA Kirchhoff Current Law at node `ve2`
(assert (= (+ (- (- ic_Q2) ib_Q2) (/ (- v_ve2 v_e0) 2200.0)) 0.0))

(assert (=> (>= (- 43.32353432118352 (/ (- 1.12 deg_ge) (* 0.00008617333262 temp_k))) 25.0) (>= (exp (- 43.32353432118352 (/ (- 1.12 deg_ge) (* 0.00008617333262 temp_k)))) 8000000000.0)))
(assert (=> (>= (/ (- (* 0.74 (- (- v_vdd v_vc1) (+ 0.43 (* (- 0.00085) (- temp_k 300.0))))) (- v_vdd v_ref)) (* 2.0 (* 0.00008617333262 temp_k))) 25.0) (>= (exp (/ (- (* 0.74 (- (- v_vdd v_vc1) (+ 0.43 (* (- 0.00085) (- temp_k 300.0))))) (- v_vdd v_ref)) (* 2.0 (* 0.00008617333262 temp_k)))) 8000000000.0)))
(assert (=> (>= (/ (- (* 0.74 (- (- v_vdd v_vc1) (+ 0.43 (* (- 0.00085) (- temp_k 300.0))))) (- v_vdd v_vc1)) (* 2.0 (* 0.00008617333262 temp_k))) 25.0) (>= (exp (/ (- (* 0.74 (- (- v_vdd v_vc1) (+ 0.43 (* (- 0.00085) (- temp_k 300.0))))) (- v_vdd v_vc1)) (* 2.0 (* 0.00008617333262 temp_k)))) 8000000000.0)))
(assert (=> (>= (/ (- (* 0.74 (- (- v_vdd v_vc1) (+ 0.43 (* (- 0.00085) (- temp_k 300.0))))) (- v_vdd v_vdd)) (* 2.0 (* 0.00008617333262 temp_k))) 25.0) (>= (exp (/ (- (* 0.74 (- (- v_vdd v_vc1) (+ 0.43 (* (- 0.00085) (- temp_k 300.0))))) (- v_vdd v_vdd)) (* 2.0 (* 0.00008617333262 temp_k)))) 8000000000.0)))
(assert (=> (>= (/ (- v_ref v_e0) (* 0.00008617333262 temp_k)) 25.0) (>= (exp (/ (- v_ref v_e0) (* 0.00008617333262 temp_k))) 8000000000.0)))
(assert (=> (>= (/ (- v_ref v_ref) (* 0.00008617333262 temp_k)) 25.0) (>= (exp (/ (- v_ref v_ref) (* 0.00008617333262 temp_k))) 8000000000.0)))
(assert (=> (>= (/ (- v_ref v_vc1) (* 0.00008617333262 temp_k)) 25.0) (>= (exp (/ (- v_ref v_vc1) (* 0.00008617333262 temp_k))) 8000000000.0)))
(assert (=> (>= (/ (- v_ref v_ve2) (* 0.00008617333262 temp_k)) 25.0) (>= (exp (/ (- v_ref v_ve2) (* 0.00008617333262 temp_k))) 8000000000.0)))
(assert (=> (>= y_sp_Mp1_f_1 25.0) (>= (exp y_sp_Mp1_f_1) 8000000000.0)))
(assert (=> (>= y_sp_Mp1_r_2 25.0) (>= (exp y_sp_Mp1_r_2) 8000000000.0)))
(assert (=> (>= y_sp_Mp2_f_3 25.0) (>= (exp y_sp_Mp2_f_3) 8000000000.0)))
(assert (=> (>= y_sp_Mp2_r_4 25.0) (>= (exp y_sp_Mp2_r_4) 8000000000.0)))
; --- Negated Safety Specification (.unsafe) ---
(assert (< v_ref 0.15))

(check-sat)
(exit)
