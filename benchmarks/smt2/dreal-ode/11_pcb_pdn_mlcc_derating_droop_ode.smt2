; ============================================================================
; Benchmark : Suite C-11: Core PDN With BGA Cold-Solder Void & Voltage-Derated Class-II MLCC Under Load Step (ODE)
; Dialect   : dreal-ode (QF_NRA + exp + continuous define-ode)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic QF_NRA_ODE)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)

; --- Continuous Parameter / Defect / Litho Uncertainty Box ---
(declare-fun r_void () Real)
(assert (and (>= r_void 0.001) (<= r_void 0.028)))
(declare-fun v_sat () Real)
(assert (and (>= v_sat 0.55) (<= v_sat 0.8)))
(declare-fun di_step () Real)
(assert (and (>= di_step 0.4) (<= di_step 1.1)))

; --- Continuous ODE Flow Variables & Initial/Final Endpoints ---
(declare-fun t () Real)
(declare-fun t_0 () Real)
(declare-fun t_t () Real)
(declare-fun tau_hit () Real)
(assert (and (= t_0 0.0) (>= tau_hit 0.0) (<= tau_hit 0.000000004) (= t_t tau_hit)))
; Dynamic node voltage v(bga) [V]
(declare-fun v_bga () Real)
(declare-fun v_bga_0 () Real)
(declare-fun v_bga_t () Real)
(assert (and (>= v_bga_0 0.7) (<= v_bga_0 1.0)))
(assert (and (>= v_bga_t 0.7) (<= v_bga_t 1.0)))
; Dynamic node voltage v(vcore) [V]
(declare-fun v_vcore () Real)
(declare-fun v_vcore_0 () Real)
(declare-fun v_vcore_t () Real)
(assert (and (>= v_vcore_0 0.4) (<= v_vcore_0 1.1)))
(assert (and (>= v_vcore_t 0.4) (<= v_vcore_t 1.1)))
; Inductor / interconnect branch current (Lplane) [A]
(declare-fun i_Lplane () Real)
(declare-fun i_Lplane_0 () Real)
(declare-fun i_Lplane_t () Real)
(assert (and (>= i_Lplane_0 (- 0.5)) (<= i_Lplane_0 4.0)))
(assert (and (>= i_Lplane_t (- 0.5)) (<= i_Lplane_t 4.0)))
; Inductor / interconnect branch current (C_MLCC1) [A]
(declare-fun i_C_MLCC1 () Real)
(declare-fun i_C_MLCC1_0 () Real)
(declare-fun i_C_MLCC1_t () Real)
(assert (and (>= i_C_MLCC1_0 (- 3.0)) (<= i_C_MLCC1_0 3.0)))
(assert (and (>= i_C_MLCC1_t (- 3.0)) (<= i_C_MLCC1_t 3.0)))
; Nonlinear voltage-derated MLCC internal voltage [V] (C_MLCC1)
(declare-fun vc_C_MLCC1 () Real)
(declare-fun vc_C_MLCC1_0 () Real)
(declare-fun vc_C_MLCC1_t () Real)
(assert (and (>= vc_C_MLCC1_0 0.7) (<= vc_C_MLCC1_0 1.0)))
(assert (and (>= vc_C_MLCC1_t 0.7) (<= vc_C_MLCC1_t 1.0)))

; --- Initial Condition X_0 ---
(assert (= v_bga_0 0.9))
(assert (= v_vcore_0 0.9))
(assert (= i_Lplane_0 0.1))
(assert (= i_C_MLCC1_0 0.0))
(assert (= vc_C_MLCC1_0 0.9))

; --- Continuous Nonlinear Circuit ODE Flow ---
(define-ode flow_1 (
  (= d/dt[t] 1.0)
  (= d/dt[v_bga] (/ (- i_Lplane (/ (- v_bga v_vcore) r_void)) 0.000000008))
  (= d/dt[v_vcore] (/ (- (- (/ (- v_bga v_vcore) r_void) i_C_MLCC1) (+ 0.1 (* di_step (/ (- (/ 1.0 (+ 1.0 (exp (- (/ (- t 0.0000000004) 0.00000000015))))) (/ 1.0 (+ 1.0 (exp 2.666666666666667)))) (- 1.0 (/ 1.0 (+ 1.0 (exp 2.666666666666667)))))))) 0.000000003))
  (= d/dt[i_Lplane] (/ (- (- 0.9 v_bga) (* 0.002 i_Lplane)) 0.00000000022))
  (= d/dt[i_C_MLCC1] (/ (- (- v_vcore vc_C_MLCC1) (* 0.003 i_C_MLCC1)) 0.00000000014))
  (= d/dt[vc_C_MLCC1] (/ i_C_MLCC1 (+ 0.0000015 (/ 0.000022 (+ 1.0 (* (/ vc_C_MLCC1 v_sat) (/ vc_C_MLCC1 v_sat)))))))
))

(assert (= [t_t v_bga_t v_vcore_t i_Lplane_t i_C_MLCC1_t vc_C_MLCC1_t] (integral 0.0 tau_hit [t_0 v_bga_0 v_vcore_0 i_Lplane_0 i_C_MLCC1_0 vc_C_MLCC1_0] flow_1)))
(assert (forall_t 1 [0.0 tau_hit] (and (>= v_bga_t 0.7) (<= v_bga_t 1.0))))
(assert (forall_t 1 [0.0 tau_hit] (and (>= v_vcore_t 0.4) (<= v_vcore_t 1.1))))
(assert (forall_t 1 [0.0 tau_hit] (and (>= i_Lplane_t (- 0.5)) (<= i_Lplane_t 4.0))))
(assert (forall_t 1 [0.0 tau_hit] (and (>= i_C_MLCC1_t (- 3.0)) (<= i_C_MLCC1_t 3.0))))
(assert (forall_t 1 [0.0 tau_hit] (and (>= vc_C_MLCC1_t 0.7) (<= vc_C_MLCC1_t 1.0))))

; --- Existential Unsafe Reachability at Hit Time tau_hit in [0, 0.000000004] ---
(assert (< v_vcore_t 0.8))

(check-sat)
(exit)
