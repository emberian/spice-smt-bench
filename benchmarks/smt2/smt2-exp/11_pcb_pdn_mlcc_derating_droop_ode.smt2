; ============================================================================
; Benchmark : Suite C-11: Core PDN With BGA Cold-Solder Void & Voltage-Derated Class-II MLCC Under Load Step (ODE)
; Dialect   : smt2-exp (QF_NRA + transcendental exp)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)

; --- Continuous Parameter / Defect / Litho Uncertainty Box ---
(declare-fun r_void () Real)
(assert (and (>= r_void 0.001) (<= r_void 0.028)))
(declare-fun v_sat () Real)
(assert (and (>= v_sat 0.55) (<= v_sat 0.8)))
(declare-fun di_step () Real)
(assert (and (>= di_step 0.4) (<= di_step 1.1)))

; --- Implicit Backward-Euler Trajectory Unrolling (6 steps, dt = 2.5000e-10 s) ---
(declare-fun v_bga_s0 () Real)
(assert (and (>= v_bga_s0 0.7) (<= v_bga_s0 1.0)))
(declare-fun v_vcore_s0 () Real)
(assert (and (>= v_vcore_s0 0.75) (<= v_vcore_s0 1.0)))
(declare-fun i_Lplane_s0 () Real)
(assert (and (>= i_Lplane_s0 (- 0.5)) (<= i_Lplane_s0 4.0)))
(declare-fun i_C_MLCC1_s0 () Real)
(assert (and (>= i_C_MLCC1_s0 (- 3.0)) (<= i_C_MLCC1_s0 3.0)))
(declare-fun vc_C_MLCC1_s0 () Real)
(assert (and (>= vc_C_MLCC1_s0 0.7) (<= vc_C_MLCC1_s0 1.0)))
(declare-fun v_bga_s1 () Real)
(assert (and (>= v_bga_s1 0.7) (<= v_bga_s1 1.0)))
(declare-fun v_vcore_s1 () Real)
(assert (and (>= v_vcore_s1 0.75) (<= v_vcore_s1 1.0)))
(declare-fun i_Lplane_s1 () Real)
(assert (and (>= i_Lplane_s1 (- 0.5)) (<= i_Lplane_s1 4.0)))
(declare-fun i_C_MLCC1_s1 () Real)
(assert (and (>= i_C_MLCC1_s1 (- 3.0)) (<= i_C_MLCC1_s1 3.0)))
(declare-fun vc_C_MLCC1_s1 () Real)
(assert (and (>= vc_C_MLCC1_s1 0.7) (<= vc_C_MLCC1_s1 1.0)))
(declare-fun v_bga_s2 () Real)
(assert (and (>= v_bga_s2 0.7) (<= v_bga_s2 1.0)))
(declare-fun v_vcore_s2 () Real)
(assert (and (>= v_vcore_s2 0.75) (<= v_vcore_s2 1.0)))
(declare-fun i_Lplane_s2 () Real)
(assert (and (>= i_Lplane_s2 (- 0.5)) (<= i_Lplane_s2 4.0)))
(declare-fun i_C_MLCC1_s2 () Real)
(assert (and (>= i_C_MLCC1_s2 (- 3.0)) (<= i_C_MLCC1_s2 3.0)))
(declare-fun vc_C_MLCC1_s2 () Real)
(assert (and (>= vc_C_MLCC1_s2 0.7) (<= vc_C_MLCC1_s2 1.0)))
(declare-fun v_bga_s3 () Real)
(assert (and (>= v_bga_s3 0.7) (<= v_bga_s3 1.0)))
(declare-fun v_vcore_s3 () Real)
(assert (and (>= v_vcore_s3 0.75) (<= v_vcore_s3 1.0)))
(declare-fun i_Lplane_s3 () Real)
(assert (and (>= i_Lplane_s3 (- 0.5)) (<= i_Lplane_s3 4.0)))
(declare-fun i_C_MLCC1_s3 () Real)
(assert (and (>= i_C_MLCC1_s3 (- 3.0)) (<= i_C_MLCC1_s3 3.0)))
(declare-fun vc_C_MLCC1_s3 () Real)
(assert (and (>= vc_C_MLCC1_s3 0.7) (<= vc_C_MLCC1_s3 1.0)))
(declare-fun v_bga_s4 () Real)
(assert (and (>= v_bga_s4 0.7) (<= v_bga_s4 1.0)))
(declare-fun v_vcore_s4 () Real)
(assert (and (>= v_vcore_s4 0.75) (<= v_vcore_s4 1.0)))
(declare-fun i_Lplane_s4 () Real)
(assert (and (>= i_Lplane_s4 (- 0.5)) (<= i_Lplane_s4 4.0)))
(declare-fun i_C_MLCC1_s4 () Real)
(assert (and (>= i_C_MLCC1_s4 (- 3.0)) (<= i_C_MLCC1_s4 3.0)))
(declare-fun vc_C_MLCC1_s4 () Real)
(assert (and (>= vc_C_MLCC1_s4 0.7) (<= vc_C_MLCC1_s4 1.0)))
(declare-fun v_bga_s5 () Real)
(assert (and (>= v_bga_s5 0.7) (<= v_bga_s5 1.0)))
(declare-fun v_vcore_s5 () Real)
(assert (and (>= v_vcore_s5 0.75) (<= v_vcore_s5 1.0)))
(declare-fun i_Lplane_s5 () Real)
(assert (and (>= i_Lplane_s5 (- 0.5)) (<= i_Lplane_s5 4.0)))
(declare-fun i_C_MLCC1_s5 () Real)
(assert (and (>= i_C_MLCC1_s5 (- 3.0)) (<= i_C_MLCC1_s5 3.0)))
(declare-fun vc_C_MLCC1_s5 () Real)
(assert (and (>= vc_C_MLCC1_s5 0.7) (<= vc_C_MLCC1_s5 1.0)))
(declare-fun v_bga_s6 () Real)
(assert (and (>= v_bga_s6 0.7) (<= v_bga_s6 1.0)))
(declare-fun v_vcore_s6 () Real)
(assert (and (>= v_vcore_s6 0.75) (<= v_vcore_s6 1.0)))
(declare-fun i_Lplane_s6 () Real)
(assert (and (>= i_Lplane_s6 (- 0.5)) (<= i_Lplane_s6 4.0)))
(declare-fun i_C_MLCC1_s6 () Real)
(assert (and (>= i_C_MLCC1_s6 (- 3.0)) (<= i_C_MLCC1_s6 3.0)))
(declare-fun vc_C_MLCC1_s6 () Real)
(assert (and (>= vc_C_MLCC1_s6 0.7) (<= vc_C_MLCC1_s6 1.0)))

; --- Initial State Set X_0 ---
(assert (= v_bga_s0 0.9))
(assert (= v_vcore_s0 0.9))
(assert (= i_Lplane_s0 0.1))
(assert (= i_C_MLCC1_s0 0.0))
(assert (= vc_C_MLCC1_s0 0.9))

; --- Discrete-Time Nonlinear DAE / ODE Step Equations ---
; Step 1: v_bga
(assert (= v_bga_s1 (+ v_bga_s0 (* (/ 2.5 10000000000.0) (/ (- i_Lplane_s1 (/ (- v_bga_s1 v_vcore_s1) r_void)) (/ 8.0 100000000.0))))))
; Step 1: v_vcore
(assert (= v_vcore_s1 (+ v_vcore_s0 (* (/ 2.5 10000000000.0) (/ (- (- (/ (- v_bga_s1 v_vcore_s1) r_void) i_C_MLCC1_s1) (+ 0.1 (/ di_step (+ 1.0 (exp 1.0))))) (/ 1.5 100000000.0))))))
; Step 1: i_Lplane
(assert (= i_Lplane_s1 (+ i_Lplane_s0 (* (/ 2.5 10000000000.0) (/ (- (- 0.9 v_bga_s1) (* 0.002 i_Lplane_s1)) (/ 2.2 10000000000.0))))))
; Step 1: i_C_MLCC1
(assert (= i_C_MLCC1_s1 (+ i_C_MLCC1_s0 (* (/ 2.5 10000000000.0) (/ (- (- v_vcore_s1 vc_C_MLCC1_s1) (* 0.003 i_C_MLCC1_s1)) (/ 1.4 10000000000.0))))))
; Step 1: vc_C_MLCC1
(assert (= vc_C_MLCC1_s1 (+ vc_C_MLCC1_s0 (* (/ 2.5 10000000000.0) (/ i_C_MLCC1_s1 (+ (/ 1.5 1000000.0) (/ (/ 2.2 100000.0) (+ 1.0 (* (/ vc_C_MLCC1_s1 v_sat) (/ vc_C_MLCC1_s1 v_sat))))))))))
; Step 2: v_bga
(assert (= v_bga_s2 (+ v_bga_s1 (* (/ 2.5 10000000000.0) (/ (- i_Lplane_s2 (/ (- v_bga_s2 v_vcore_s2) r_void)) (/ 8.0 100000000.0))))))
; Step 2: v_vcore
(assert (= v_vcore_s2 (+ v_vcore_s1 (* (/ 2.5 10000000000.0) (/ (- (- (/ (- v_bga_s2 v_vcore_s2) r_void) i_C_MLCC1_s2) (+ 0.1 (/ di_step (+ 1.0 (exp (- 0.666666666667)))))) (/ 1.5 100000000.0))))))
; Step 2: i_Lplane
(assert (= i_Lplane_s2 (+ i_Lplane_s1 (* (/ 2.5 10000000000.0) (/ (- (- 0.9 v_bga_s2) (* 0.002 i_Lplane_s2)) (/ 2.2 10000000000.0))))))
; Step 2: i_C_MLCC1
(assert (= i_C_MLCC1_s2 (+ i_C_MLCC1_s1 (* (/ 2.5 10000000000.0) (/ (- (- v_vcore_s2 vc_C_MLCC1_s2) (* 0.003 i_C_MLCC1_s2)) (/ 1.4 10000000000.0))))))
; Step 2: vc_C_MLCC1
(assert (= vc_C_MLCC1_s2 (+ vc_C_MLCC1_s1 (* (/ 2.5 10000000000.0) (/ i_C_MLCC1_s2 (+ (/ 1.5 1000000.0) (/ (/ 2.2 100000.0) (+ 1.0 (* (/ vc_C_MLCC1_s2 v_sat) (/ vc_C_MLCC1_s2 v_sat))))))))))
; Step 3: v_bga
(assert (= v_bga_s3 (+ v_bga_s2 (* (/ 2.5 10000000000.0) (/ (- i_Lplane_s3 (/ (- v_bga_s3 v_vcore_s3) r_void)) (/ 8.0 100000000.0))))))
; Step 3: v_vcore
(assert (= v_vcore_s3 (+ v_vcore_s2 (* (/ 2.5 10000000000.0) (/ (- (- (/ (- v_bga_s3 v_vcore_s3) r_void) i_C_MLCC1_s3) (+ 0.1 (/ di_step (+ 1.0 (exp (- 2.333333333333)))))) (/ 1.5 100000000.0))))))
; Step 3: i_Lplane
(assert (= i_Lplane_s3 (+ i_Lplane_s2 (* (/ 2.5 10000000000.0) (/ (- (- 0.9 v_bga_s3) (* 0.002 i_Lplane_s3)) (/ 2.2 10000000000.0))))))
; Step 3: i_C_MLCC1
(assert (= i_C_MLCC1_s3 (+ i_C_MLCC1_s2 (* (/ 2.5 10000000000.0) (/ (- (- v_vcore_s3 vc_C_MLCC1_s3) (* 0.003 i_C_MLCC1_s3)) (/ 1.4 10000000000.0))))))
; Step 3: vc_C_MLCC1
(assert (= vc_C_MLCC1_s3 (+ vc_C_MLCC1_s2 (* (/ 2.5 10000000000.0) (/ i_C_MLCC1_s3 (+ (/ 1.5 1000000.0) (/ (/ 2.2 100000.0) (+ 1.0 (* (/ vc_C_MLCC1_s3 v_sat) (/ vc_C_MLCC1_s3 v_sat))))))))))
; Step 4: v_bga
(assert (= v_bga_s4 (+ v_bga_s3 (* (/ 2.5 10000000000.0) (/ (- i_Lplane_s4 (/ (- v_bga_s4 v_vcore_s4) r_void)) (/ 8.0 100000000.0))))))
; Step 4: v_vcore
(assert (= v_vcore_s4 (+ v_vcore_s3 (* (/ 2.5 10000000000.0) (/ (- (- (/ (- v_bga_s4 v_vcore_s4) r_void) i_C_MLCC1_s4) (+ 0.1 (/ di_step (+ 1.0 (exp (- 4.0)))))) (/ 1.5 100000000.0))))))
; Step 4: i_Lplane
(assert (= i_Lplane_s4 (+ i_Lplane_s3 (* (/ 2.5 10000000000.0) (/ (- (- 0.9 v_bga_s4) (* 0.002 i_Lplane_s4)) (/ 2.2 10000000000.0))))))
; Step 4: i_C_MLCC1
(assert (= i_C_MLCC1_s4 (+ i_C_MLCC1_s3 (* (/ 2.5 10000000000.0) (/ (- (- v_vcore_s4 vc_C_MLCC1_s4) (* 0.003 i_C_MLCC1_s4)) (/ 1.4 10000000000.0))))))
; Step 4: vc_C_MLCC1
(assert (= vc_C_MLCC1_s4 (+ vc_C_MLCC1_s3 (* (/ 2.5 10000000000.0) (/ i_C_MLCC1_s4 (+ (/ 1.5 1000000.0) (/ (/ 2.2 100000.0) (+ 1.0 (* (/ vc_C_MLCC1_s4 v_sat) (/ vc_C_MLCC1_s4 v_sat))))))))))
; Step 5: v_bga
(assert (= v_bga_s5 (+ v_bga_s4 (* (/ 2.5 10000000000.0) (/ (- i_Lplane_s5 (/ (- v_bga_s5 v_vcore_s5) r_void)) (/ 8.0 100000000.0))))))
; Step 5: v_vcore
(assert (= v_vcore_s5 (+ v_vcore_s4 (* (/ 2.5 10000000000.0) (/ (- (- (/ (- v_bga_s5 v_vcore_s5) r_void) i_C_MLCC1_s5) (+ 0.1 (/ di_step (+ 1.0 (exp (- 5.666666666667)))))) (/ 1.5 100000000.0))))))
; Step 5: i_Lplane
(assert (= i_Lplane_s5 (+ i_Lplane_s4 (* (/ 2.5 10000000000.0) (/ (- (- 0.9 v_bga_s5) (* 0.002 i_Lplane_s5)) (/ 2.2 10000000000.0))))))
; Step 5: i_C_MLCC1
(assert (= i_C_MLCC1_s5 (+ i_C_MLCC1_s4 (* (/ 2.5 10000000000.0) (/ (- (- v_vcore_s5 vc_C_MLCC1_s5) (* 0.003 i_C_MLCC1_s5)) (/ 1.4 10000000000.0))))))
; Step 5: vc_C_MLCC1
(assert (= vc_C_MLCC1_s5 (+ vc_C_MLCC1_s4 (* (/ 2.5 10000000000.0) (/ i_C_MLCC1_s5 (+ (/ 1.5 1000000.0) (/ (/ 2.2 100000.0) (+ 1.0 (* (/ vc_C_MLCC1_s5 v_sat) (/ vc_C_MLCC1_s5 v_sat))))))))))
; Step 6: v_bga
(assert (= v_bga_s6 (+ v_bga_s5 (* (/ 2.5 10000000000.0) (/ (- i_Lplane_s6 (/ (- v_bga_s6 v_vcore_s6) r_void)) (/ 8.0 100000000.0))))))
; Step 6: v_vcore
(assert (= v_vcore_s6 (+ v_vcore_s5 (* (/ 2.5 10000000000.0) (/ (- (- (/ (- v_bga_s6 v_vcore_s6) r_void) i_C_MLCC1_s6) (+ 0.1 (/ di_step (+ 1.0 (exp (- 7.333333333333)))))) (/ 1.5 100000000.0))))))
; Step 6: i_Lplane
(assert (= i_Lplane_s6 (+ i_Lplane_s5 (* (/ 2.5 10000000000.0) (/ (- (- 0.9 v_bga_s6) (* 0.002 i_Lplane_s6)) (/ 2.2 10000000000.0))))))
; Step 6: i_C_MLCC1
(assert (= i_C_MLCC1_s6 (+ i_C_MLCC1_s5 (* (/ 2.5 10000000000.0) (/ (- (- v_vcore_s6 vc_C_MLCC1_s6) (* 0.003 i_C_MLCC1_s6)) (/ 1.4 10000000000.0))))))
; Step 6: vc_C_MLCC1
(assert (= vc_C_MLCC1_s6 (+ vc_C_MLCC1_s5 (* (/ 2.5 10000000000.0) (/ i_C_MLCC1_s6 (+ (/ 1.5 1000000.0) (/ (/ 2.2 100000.0) (+ 1.0 (* (/ vc_C_MLCC1_s6 v_sat) (/ vc_C_MLCC1_s6 v_sat))))))))))

; --- Existential Unsafe Trajectory Violation Across Steps 1..=6 ---
(assert (or (< v_vcore_s1 0.8) (< v_vcore_s2 0.8) (< v_vcore_s3 0.8) (< v_vcore_s4 0.8) (< v_vcore_s5 0.8) (< v_vcore_s6 0.8)))

(check-sat)
(exit)
