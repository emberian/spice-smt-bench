; ============================================================================
; Benchmark : Suite B-06: Nonlinear RC + Shockley Clamp Glitch Filter Rejecting Laser/EMI Fault Pulse (ODE)
; PDK       : gf180mcu (Open 180nm Planar Bulk CMOS (GF180MCU class: 3.3V/5V I/O + ESD diodes + parasitic well/substrate SCR))
; Dialect   : smt2-exp (QF_NRA + transcendental exp)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic ALL)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)

; --- Continuous Parameter / Defect / Litho Uncertainty Box ---
(declare-fun i_peak () Real)
(assert (and (>= i_peak 0.0) (<= i_peak 0.035)))
(declare-fun vt () Real)
(assert (and (>= vt 0.024) (<= vt 0.031)))

; --- Implicit Backward-Euler Trajectory Unrolling (6 steps, dt = 1.0000e-10 s) ---
(declare-fun v_comp_s0 () Real) (assert (and (>= v_comp_s0 (- 0.2)) (<= v_comp_s0 2.0)))
(declare-fun v_comp_s1 () Real) (assert (and (>= v_comp_s1 (- 0.2)) (<= v_comp_s1 2.0)))
(declare-fun v_comp_s2 () Real) (assert (and (>= v_comp_s2 (- 0.2)) (<= v_comp_s2 2.0)))
(declare-fun v_comp_s3 () Real) (assert (and (>= v_comp_s3 (- 0.2)) (<= v_comp_s3 2.0)))
(declare-fun v_comp_s4 () Real) (assert (and (>= v_comp_s4 (- 0.2)) (<= v_comp_s4 2.0)))
(declare-fun v_comp_s5 () Real) (assert (and (>= v_comp_s5 (- 0.2)) (<= v_comp_s5 2.0)))
(declare-fun v_comp_s6 () Real) (assert (and (>= v_comp_s6 (- 0.2)) (<= v_comp_s6 2.0)))

; --- Initial State Set X_0 ---
(assert (and (>= v_comp_s0 0.0) (<= v_comp_s0 0.05)))

; --- Step-Local Transcendental Softplus Auxiliaries ---
(declare-fun dx_0_s1 () Real) (assert (= dx_0_s1 (/ (- (- (* i_peak (exp (- 0.6944444444444445))) (/ v_comp_s1 2500.0)) (* 0.0000000000012 (- (exp (/ v_comp_s1 (* 1.05 vt))) 1.0))) 0.000000000008)))
(declare-fun dx_0_s2 () Real) (assert (= dx_0_s2 (/ (- (- (* i_peak (exp (- 0.07716049382716053))) (/ v_comp_s2 2500.0)) (* 0.0000000000012 (- (exp (/ v_comp_s2 (* 1.05 vt))) 1.0))) 0.000000000008)))
(declare-fun dx_0_s3 () Real) (assert (= dx_0_s3 (/ (- (- (* i_peak (exp (- 0.07716049382716043))) (/ v_comp_s3 2500.0)) (* 0.0000000000012 (- (exp (/ v_comp_s3 (* 1.05 vt))) 1.0))) 0.000000000008)))
(declare-fun dx_0_s4 () Real) (assert (= dx_0_s4 (/ (- (- (* i_peak (exp (- 0.6944444444444445))) (/ v_comp_s4 2500.0)) (* 0.0000000000012 (- (exp (/ v_comp_s4 (* 1.05 vt))) 1.0))) 0.000000000008)))
(declare-fun dx_0_s5 () Real) (assert (= dx_0_s5 (/ (- (- (* i_peak (exp (- 1.929012345679013))) (/ v_comp_s5 2500.0)) (* 0.0000000000012 (- (exp (/ v_comp_s5 (* 1.05 vt))) 1.0))) 0.000000000008)))
(declare-fun dx_0_s6 () Real) (assert (= dx_0_s6 (/ (- (- (* i_peak (exp (- 3.780864197530864))) (/ v_comp_s6 2500.0)) (* 0.0000000000012 (- (exp (/ v_comp_s6 (* 1.05 vt))) 1.0))) 0.000000000008)))

; --- Discrete-Time Nonlinear DAE / ODE Step Equations ---
(assert (= v_comp_s1 (+ v_comp_s0 (* 0.0000000001 dx_0_s1))))
(assert (= v_comp_s2 (+ v_comp_s1 (* 0.0000000001 dx_0_s2))))
(assert (= v_comp_s3 (+ v_comp_s2 (* 0.0000000001 dx_0_s3))))
(assert (= v_comp_s4 (+ v_comp_s3 (* 0.0000000001 dx_0_s4))))
(assert (= v_comp_s5 (+ v_comp_s4 (* 0.0000000001 dx_0_s5))))
(assert (= v_comp_s6 (+ v_comp_s5 (* 0.0000000001 dx_0_s6))))

; --- Existential Unsafe Trajectory Violation Across Steps 0..=6 ---
(assert (or (>= v_comp_s0 1.1) (>= v_comp_s1 1.1) (>= v_comp_s2 1.1) (>= v_comp_s3 1.1) (>= v_comp_s4 1.1) (>= v_comp_s5 1.1) (>= v_comp_s6 1.1)))

(check-sat)
(exit)
