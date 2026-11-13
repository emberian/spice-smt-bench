; ============================================================================
; Benchmark : Suite B-07: GaN-on-SiC 48V Half-Bridge High-dv/dt Miller Bounce & Shoot-Through Immunity (ODE)
; PDK       : gan_sic (Wide-Bandgap AlGaN/GaN-on-SiC Power & RF HEMT (ASM-HEMT 2DEG polarization channel + voltage-dependent depletion Miller Cgd))
; Dialect   : dreal-ode (QF_NRA + exp + continuous define-ode)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)

; --- Continuous Parameter / Defect / Litho Uncertainty Box ---
(declare-fun cgd0 () Real)
(assert (and (>= cgd0 (/ 3.5 100000000000.0)) (<= cgd0 (/ 4.8 100000000000.0))))
(declare-fun r_pd () Real)
(assert (and (>= r_pd 0.8) (<= r_pd 1.5)))
(declare-fun vt () Real)
(assert (and (>= vt 0.025) (<= vt 0.034)))

; --- Continuous ODE Flow Variables & Initial/Final Endpoints ---
(declare-fun t () Real)
(declare-fun t_0 () Real)
(declare-fun t_t () Real)
(declare-fun tau_hit () Real)
(assert (and (= t_0 0.0) (>= tau_hit 0.0) (<= tau_hit (/ 1.5 1000000000.0)) (= t_t tau_hit)))
; Dynamic node voltage v(d_ls) [V]
(declare-fun v_d_ls () Real)
(declare-fun v_d_ls_0 () Real)
(declare-fun v_d_ls_t () Real)
(assert (and (>= v_d_ls_0 (- 0.5)) (<= v_d_ls_0 52.0)))
(assert (and (>= v_d_ls_t (- 0.5)) (<= v_d_ls_t 52.0)))
; Dynamic node voltage v(g_ls) [V]
(declare-fun v_g_ls () Real)
(declare-fun v_g_ls_0 () Real)
(declare-fun v_g_ls_t () Real)
(assert (and (>= v_g_ls_0 (- 0.3)) (<= v_g_ls_0 3.0)))
(assert (and (>= v_g_ls_t (- 0.3)) (<= v_g_ls_t 3.0)))

; --- Initial Condition X_0 ---
(assert (= v_d_ls_0 48.0))
(assert (and (>= v_g_ls_0 0.0) (<= v_g_ls_0 0.05)))

; --- Continuous Nonlinear Circuit ODE Flow ---
(define-ode flow_1 (
  (= d/dt[t] 1.0)
  (= d/dt[v_d_ls] (/ (- (/ (- 48.0 v_d_ls) 2.0) (* (/ 72.0 (+ 1.0 (* 0.12 (log (+ 1.0 (exp (/ (- v_g_ls 1.45) (* 2.0 (* 0.82 vt))))))))) (- (* (log (+ 1.0 (exp (/ (- v_g_ls 1.45) (* 2.0 (* 0.82 vt)))))) (log (+ 1.0 (exp (/ (- v_g_ls 1.45) (* 2.0 (* 0.82 vt))))))) (* (log (+ 1.0 (exp (/ (- (- v_g_ls 1.45) (* 0.82 v_d_ls)) (* 2.0 (* 0.82 vt)))))) (log (+ 1.0 (exp (/ (- (- v_g_ls 1.45) (* 0.82 v_d_ls)) (* 2.0 (* 0.82 vt)))))))))) (/ 1.2 10000000000.0)))
  (= d/dt[v_g_ls] (/ (- (* (+ (/ 3.5 1000000000000.0) (/ cgd0 (+ 1.0 (* (/ (- (/ 48.0 (+ 1.0 (exp (- (/ (- t (/ 6.0 10000000000.0)) (/ 3.5 10000000000.0)))))) v_g_ls) 8.0) (/ (- (/ 48.0 (+ 1.0 (exp (- (/ (- t (/ 6.0 10000000000.0)) (/ 3.5 10000000000.0)))))) v_g_ls) 8.0))))) (/ (- (* 48.0 (* (exp (- (/ (- t (/ 6.0 10000000000.0)) (/ 3.5 10000000000.0)))) (- (* 2.85714285714286 1000000000.0))))) (* (+ 1.0 (exp (- (/ (- t (/ 6.0 10000000000.0)) (/ 3.5 10000000000.0))))) (+ 1.0 (exp (- (/ (- t (/ 6.0 10000000000.0)) (/ 3.5 10000000000.0)))))))) (/ v_g_ls r_pd)) (+ (+ (/ 3.5 1000000000000.0) (/ cgd0 (+ 1.0 (* (/ (- (/ 48.0 (+ 1.0 (exp (- (/ (- t (/ 6.0 10000000000.0)) (/ 3.5 10000000000.0)))))) v_g_ls) 8.0) (/ (- (/ 48.0 (+ 1.0 (exp (- (/ (- t (/ 6.0 10000000000.0)) (/ 3.5 10000000000.0)))))) v_g_ls) 8.0))))) (/ 6.8 10000000000.0))))
))

(assert (= [t_t v_d_ls_t v_g_ls_t] (integral 0.0 tau_hit [t_0 v_d_ls_0 v_g_ls_0] flow_1)))
(assert (forall_t 1 [0.0 tau_hit] (and (>= v_d_ls_t (- 0.5)) (<= v_d_ls_t 52.0))))
(assert (forall_t 1 [0.0 tau_hit] (and (>= v_g_ls_t (- 0.3)) (<= v_g_ls_t 3.0))))

; --- Existential Unsafe Reachability at Hit Time tau_hit in [0, (/ 1.5 1000000000.0)] ---
(assert (> v_g_ls_t 1.2))

(check-sat)
(exit)
