; ============================================================================
; Benchmark : Suite B-07: GaN-on-SiC 48V Half-Bridge High-dv/dt Miller Bounce & Shoot-Through Immunity (ODE)
; PDK       : gan_sic (Wide-Bandgap AlGaN/GaN-on-SiC Power & RF HEMT (ASM-HEMT 2DEG polarization channel + voltage-dependent depletion Miller Cgd))
; Dialect   : dreal-ode (QF_NRA + exp + continuous define-ode)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic QF_NRA_ODE)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)

; --- Continuous Parameter / Defect / Litho Uncertainty Box ---
(declare-fun cgd0 () Real)
(assert (and (>= cgd0 0.000000000035) (<= cgd0 0.000000000048)))
(declare-fun r_pd () Real)
(assert (and (>= r_pd 0.8) (<= r_pd 1.5)))
(declare-fun vt () Real)
(assert (and (>= vt 0.025) (<= vt 0.034)))

; --- Continuous ODE Flow Variables & Initial/Final Endpoints ---
(declare-fun t () Real)
(declare-fun t_0 () Real)
(declare-fun t_t () Real)
(declare-fun tau_hit () Real)
(assert (and (= t_0 0.0) (>= tau_hit 0.0) (<= tau_hit 0.0000000015000000000000002) (= t_t tau_hit)))
; Dynamic node voltage v(g_ls) [V]
(declare-fun v_g_ls () Real)
(declare-fun v_g_ls_0 () Real)
(declare-fun v_g_ls_t () Real)
(assert (and (>= v_g_ls_0 (- 0.3)) (<= v_g_ls_0 3.0)))
(assert (and (>= v_g_ls_t (- 0.3)) (<= v_g_ls_t 3.0)))
; Dynamic node voltage v(sw) [V]
(declare-fun v_sw () Real)
(declare-fun v_sw_0 () Real)
(declare-fun v_sw_t () Real)
(assert (and (>= v_sw_0 (- 1.0)) (<= v_sw_0 55.0)))
(assert (and (>= v_sw_t (- 1.0)) (<= v_sw_t 55.0)))

; --- Initial Condition X_0 ---
(assert (and (>= v_g_ls_0 0.0) (<= v_g_ls_0 0.05)))
(assert (= v_sw_0 0.0))

; --- Continuous Nonlinear Circuit ODE Flow ---
(define-ode flow_1 (
  (= d/dt[t] 1.0)
  (= d/dt[v_g_ls] (/ (+ (* (+ 0.00000000012 (+ 0.0000000000035 (/ cgd0 (sqrt (+ 1.0 (* (/ (- v_sw v_g_ls) 8.0) (/ (- v_sw v_g_ls) 8.0))))))) (- (/ v_g_ls r_pd))) (* (+ 0.0000000000035 (/ cgd0 (sqrt (+ 1.0 (* (/ (- v_sw v_g_ls) 8.0) (/ (- v_sw v_g_ls) 8.0)))))) (- (/ (- (* 48.0 (/ (- (/ 1.0 (+ 1.0 (exp (- (/ (- t 0.0000000006) 0.00000000035))))) (/ 1.0 (+ 1.0 (exp 1.7142857142857144)))) (- 1.0 (/ 1.0 (+ 1.0 (exp 1.7142857142857144)))))) v_sw) 0.5) (* (/ 0.004 (+ 1.0 (* 0.12 (log (+ 1.0 (exp (/ (* 0.82 (- v_g_ls 1.45)) (* 2.0 vt)))))))) (- (* (log (+ 1.0 (exp (/ (* 0.82 (- v_g_ls 1.45)) (* 2.0 vt))))) (log (+ 1.0 (exp (/ (* 0.82 (- v_g_ls 1.45)) (* 2.0 vt)))))) (* (log (+ 1.0 (exp (/ (- (* 0.82 (- v_g_ls 1.45)) v_sw) (* 2.0 vt))))) (log (+ 1.0 (exp (/ (- (* 0.82 (- v_g_ls 1.45)) v_sw) (* 2.0 vt))))))))))) (+ 0.0000000000000000000816 (* (+ 0.0000000000035 (/ cgd0 (sqrt (+ 1.0 (* (/ (- v_sw v_g_ls) 8.0) (/ (- v_sw v_g_ls) 8.0)))))) 0.0000000008))))
  (= d/dt[v_sw] (/ (+ (* (+ 0.00000000068 (+ 0.0000000000035 (/ cgd0 (sqrt (+ 1.0 (* (/ (- v_sw v_g_ls) 8.0) (/ (- v_sw v_g_ls) 8.0))))))) (- (/ (- (* 48.0 (/ (- (/ 1.0 (+ 1.0 (exp (- (/ (- t 0.0000000006) 0.00000000035))))) (/ 1.0 (+ 1.0 (exp 1.7142857142857144)))) (- 1.0 (/ 1.0 (+ 1.0 (exp 1.7142857142857144)))))) v_sw) 0.5) (* (/ 0.004 (+ 1.0 (* 0.12 (log (+ 1.0 (exp (/ (* 0.82 (- v_g_ls 1.45)) (* 2.0 vt)))))))) (- (* (log (+ 1.0 (exp (/ (* 0.82 (- v_g_ls 1.45)) (* 2.0 vt))))) (log (+ 1.0 (exp (/ (* 0.82 (- v_g_ls 1.45)) (* 2.0 vt)))))) (* (log (+ 1.0 (exp (/ (- (* 0.82 (- v_g_ls 1.45)) v_sw) (* 2.0 vt))))) (log (+ 1.0 (exp (/ (- (* 0.82 (- v_g_ls 1.45)) v_sw) (* 2.0 vt)))))))))) (* (+ 0.0000000000035 (/ cgd0 (sqrt (+ 1.0 (* (/ (- v_sw v_g_ls) 8.0) (/ (- v_sw v_g_ls) 8.0)))))) (- (/ v_g_ls r_pd)))) (+ 0.0000000000000000000816 (* (+ 0.0000000000035 (/ cgd0 (sqrt (+ 1.0 (* (/ (- v_sw v_g_ls) 8.0) (/ (- v_sw v_g_ls) 8.0)))))) 0.0000000008))))
))

(assert (= [t_t v_g_ls_t v_sw_t] (integral 0.0 tau_hit [t_0 v_g_ls_0 v_sw_0] flow_1)))
(assert (forall_t 1 [0.0 tau_hit] (and (>= v_g_ls_t (- 0.3)) (<= v_g_ls_t 3.0))))
(assert (forall_t 1 [0.0 tau_hit] (and (>= v_sw_t (- 1.0)) (<= v_sw_t 55.0))))

; --- Existential Unsafe Reachability at Hit Time tau_hit in [0, 0.0000000015000000000000002] ---
(assert (or (> v_g_ls_t 1.2) (> (* (/ 0.004 (+ 1.0 (* 0.12 (log (+ 1.0 (exp (/ (* 0.82 (- v_g_ls_t 1.45)) (* 2.0 vt)))))))) (- (* (log (+ 1.0 (exp (/ (* 0.82 (- v_g_ls_t 1.45)) (* 2.0 vt))))) (log (+ 1.0 (exp (/ (* 0.82 (- v_g_ls_t 1.45)) (* 2.0 vt)))))) (* (log (+ 1.0 (exp (/ (- (* 0.82 (- v_g_ls_t 1.45)) v_sw_t) (* 2.0 vt))))) (log (+ 1.0 (exp (/ (- (* 0.82 (- v_g_ls_t 1.45)) v_sw_t) (* 2.0 vt)))))))) 0.5) (> (* (* (/ 0.004 (+ 1.0 (* 0.12 (log (+ 1.0 (exp (/ (* 0.82 (- v_g_ls_t 1.45)) (* 2.0 vt)))))))) (- (* (log (+ 1.0 (exp (/ (* 0.82 (- v_g_ls_t 1.45)) (* 2.0 vt))))) (log (+ 1.0 (exp (/ (* 0.82 (- v_g_ls_t 1.45)) (* 2.0 vt)))))) (* (log (+ 1.0 (exp (/ (- (* 0.82 (- v_g_ls_t 1.45)) v_sw_t) (* 2.0 vt))))) (log (+ 1.0 (exp (/ (- (* 0.82 (- v_g_ls_t 1.45)) v_sw_t) (* 2.0 vt)))))))) v_sw_t) 20.0)))

(check-sat)
(exit)
