; ============================================================================
; Benchmark : Suite B-06: Nonlinear RC + Shockley Clamp Glitch Filter Rejecting Laser/EMI Fault Pulse (ODE)
; PDK       : gf180mcu (Open 180nm Planar Bulk CMOS (GF180MCU class: 3.3V/5V I/O + ESD diodes + parasitic well/substrate SCR))
; Dialect   : dreal-ode (QF_NRA + exp + continuous define-ode)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)

; --- Continuous Parameter / Defect / Litho Uncertainty Box ---
(declare-fun i_peak () Real)
(assert (and (>= i_peak 0.0) (<= i_peak 0.035)))
(declare-fun vt () Real)
(assert (and (>= vt 0.024) (<= vt 0.031)))

; --- Continuous ODE Flow Variables & Initial/Final Endpoints ---
(declare-fun t () Real)
(declare-fun t_0 () Real)
(declare-fun t_t () Real)
(declare-fun tau_hit () Real)
(assert (and (= t_0 0.0) (>= tau_hit 0.0) (<= tau_hit (/ 6.0 10000000000.0)) (= t_t tau_hit)))
; Dynamic node voltage v(comp) [V]
(declare-fun v_comp () Real)
(declare-fun v_comp_0 () Real)
(declare-fun v_comp_t () Real)
(assert (and (>= v_comp_0 (- 0.2)) (<= v_comp_0 2.0)))
(assert (and (>= v_comp_t (- 0.2)) (<= v_comp_t 2.0)))

; --- Initial Condition X_0 ---
(assert (and (>= v_comp_0 0.0) (<= v_comp_0 0.05)))

; --- Continuous Nonlinear Circuit ODE Flow ---
(define-ode flow_1 (
  (= d/dt[t] 1.0)
  (= d/dt[v_comp] (/ (- (- (* i_peak (exp (- (* (/ (- t (/ 2.5 10000000000.0)) (/ 1.8 10000000000.0)) (/ (- t (/ 2.5 10000000000.0)) (/ 1.8 10000000000.0)))))) (/ v_comp 2500.0)) (* (/ 1.2 1000000000000.0) (- (exp (/ v_comp (* 1.05 vt))) 1.0))) (/ 8.0 1000000000000.0)))
))

(assert (= [t_t v_comp_t] (integral 0.0 tau_hit [t_0 v_comp_0] flow_1)))
(assert (forall_t 1 [0.0 tau_hit] (and (>= v_comp_t (- 0.2)) (<= v_comp_t 2.0))))

; --- Existential Unsafe Reachability at Hit Time tau_hit in [0, (/ 6.0 10000000000.0)] ---
(assert (>= v_comp_t 1.1))

(check-sat)
(exit)
