; ============================================================================
; Benchmark : Suite B-08: 2nm Gate-All-Around (gt2n) 3-Stacked Nanosheet 3-Stage Ring Oscillator Envelope (ODE)
; PDK       : gt2n (2nm Gate-All-Around Stacked Nanosheet (gt2n: Nsheet=3, Lg=12nm, Wns=18nm, Tns=5.0nm, EOT=0.85nm, inner-spacer Cisp + electro-thermal Rth))
; Dialect   : dreal-ode (QF_NRA + exp + continuous define-ode)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)

; --- Continuous Parameter / Defect / Litho Uncertainty Box ---
(declare-fun vdd () Real)
(assert (and (>= vdd 0.62) (<= vdd 0.68)))
(declare-fun dtns_nm () Real)
(assert (and (>= dtns_nm (- 0.3)) (<= dtns_nm 0.3)))
(declare-fun dlisp_nm () Real)
(assert (and (>= dlisp_nm (- 0.6)) (<= dlisp_nm 0.6)))

; --- Time-Invariant Geometry & Interconnect Variables ---
; Multi-gate natural scaling length lambda [nm] (Mp1)
(declare-fun lam_Mp1 () Real)
(assert (and (>= lam_Mp1 0.5) (<= lam_Mp1 15.0)))
; Multi-gate natural scaling length lambda [nm] (Mn1)
(declare-fun lam_Mn1 () Real)
(assert (and (>= lam_Mn1 0.5) (<= lam_Mn1 15.0)))
; Multi-gate natural scaling length lambda [nm] (Mp2)
(declare-fun lam_Mp2 () Real)
(assert (and (>= lam_Mp2 0.5) (<= lam_Mp2 15.0)))
; Multi-gate natural scaling length lambda [nm] (Mn2)
(declare-fun lam_Mn2 () Real)
(assert (and (>= lam_Mn2 0.5) (<= lam_Mn2 15.0)))
; Multi-gate natural scaling length lambda [nm] (Mp3)
(declare-fun lam_Mp3 () Real)
(assert (and (>= lam_Mp3 0.5) (<= lam_Mp3 15.0)))
; Multi-gate natural scaling length lambda [nm] (Mn3)
(declare-fun lam_Mn3 () Real)
(assert (and (>= lam_Mn3 0.5) (<= lam_Mn3 15.0)))
; Algebraic sqrt constraint lam_Mp1^2 = radicand (Multi-gate natural scaling length lambda [nm] (Mp1))
(assert (= (* lam_Mp1 lam_Mp1) (* 0.75 (* (+ 5.0 dtns_nm) 0.85))))
; Algebraic sqrt constraint lam_Mn1^2 = radicand (Multi-gate natural scaling length lambda [nm] (Mn1))
(assert (= (* lam_Mn1 lam_Mn1) (* 0.75 (* (+ 5.0 dtns_nm) 0.85))))
; Algebraic sqrt constraint lam_Mp2^2 = radicand (Multi-gate natural scaling length lambda [nm] (Mp2))
(assert (= (* lam_Mp2 lam_Mp2) (* 0.75 (* (+ 5.0 dtns_nm) 0.85))))
; Algebraic sqrt constraint lam_Mn2^2 = radicand (Multi-gate natural scaling length lambda [nm] (Mn2))
(assert (= (* lam_Mn2 lam_Mn2) (* 0.75 (* (+ 5.0 dtns_nm) 0.85))))
; Algebraic sqrt constraint lam_Mp3^2 = radicand (Multi-gate natural scaling length lambda [nm] (Mp3))
(assert (= (* lam_Mp3 lam_Mp3) (* 0.75 (* (+ 5.0 dtns_nm) 0.85))))
; Algebraic sqrt constraint lam_Mn3^2 = radicand (Multi-gate natural scaling length lambda [nm] (Mn3))
(assert (= (* lam_Mn3 lam_Mn3) (* 0.75 (* (+ 5.0 dtns_nm) 0.85))))

; --- Continuous ODE Flow Variables & Initial/Final Endpoints ---
(declare-fun t () Real)
(declare-fun t_0 () Real)
(declare-fun t_t () Real)
(declare-fun tau_hit () Real)
(assert (and (= t_0 0.0) (>= tau_hit 0.0) (<= tau_hit (/ 1.0 100000000000.0)) (= t_t tau_hit)))
; Dynamic node voltage v(n1) [V]
(declare-fun v_n1 () Real)
(declare-fun v_n1_0 () Real)
(declare-fun v_n1_t () Real)
(assert (and (>= v_n1_0 (- 0.2)) (<= v_n1_0 0.9)))
(assert (and (>= v_n1_t (- 0.2)) (<= v_n1_t 0.9)))
; Dynamic node voltage v(n2) [V]
(declare-fun v_n2 () Real)
(declare-fun v_n2_0 () Real)
(declare-fun v_n2_t () Real)
(assert (and (>= v_n2_0 (- 0.2)) (<= v_n2_0 0.9)))
(assert (and (>= v_n2_t (- 0.2)) (<= v_n2_t 0.9)))
; Dynamic node voltage v(n3) [V]
(declare-fun v_n3 () Real)
(declare-fun v_n3_0 () Real)
(declare-fun v_n3_t () Real)
(assert (and (>= v_n3_0 (- 0.2)) (<= v_n3_0 0.9)))
(assert (and (>= v_n3_t (- 0.2)) (<= v_n3_t 0.9)))

; --- Initial Condition X_0 ---
(assert (and (>= v_n1_0 0.55) (<= v_n1_0 0.62)))
(assert (and (>= v_n2_0 0.02) (<= v_n2_0 0.08)))
(assert (and (>= v_n3_0 0.28) (<= v_n3_0 0.35)))

; --- Continuous Nonlinear Circuit ODE Flow ---
(define-ode flow_1 (
  (= d/dt[t] 1.0)
  (= d/dt[v_n1] (/ (- (* (* (/ 2.25 1000000.0) (* 3.0 (/ (* 2.0 (+ 18.0 (+ 5.0 dtns_nm))) 12.0))) (- (* (log (+ 1.0 (exp (/ (- (- vdd v_n3) (- (+ 0.24 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.9 (exp (- (/ 12.0 (* 2.0 lam_Mp3))))) (- vdd v_n1)))) 0.0465336)))) (log (+ 1.0 (exp (/ (- (- vdd v_n3) (- (+ 0.24 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.9 (exp (- (/ 12.0 (* 2.0 lam_Mp3))))) (- vdd v_n1)))) 0.0465336))))) (* (log (+ 1.0 (exp (/ (- (- (- vdd v_n3) (- (+ 0.24 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.9 (exp (- (/ 12.0 (* 2.0 lam_Mp3))))) (- vdd v_n1)))) (* 0.9 (- vdd v_n1))) 0.0465336)))) (log (+ 1.0 (exp (/ (- (- (- vdd v_n3) (- (+ 0.24 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.9 (exp (- (/ 12.0 (* 2.0 lam_Mp3))))) (- vdd v_n1)))) (* 0.9 (- vdd v_n1))) 0.0465336))))))) (* (* (/ 2.6 1000000.0) (* 3.0 (/ (* 2.0 (+ 18.0 (+ 5.0 dtns_nm))) 12.0))) (- (* (log (+ 1.0 (exp (/ (- v_n3 (- (+ 0.23 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.8 (exp (- (/ 12.0 (* 2.0 lam_Mn3))))) v_n1))) 0.04705064)))) (log (+ 1.0 (exp (/ (- v_n3 (- (+ 0.23 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.8 (exp (- (/ 12.0 (* 2.0 lam_Mn3))))) v_n1))) 0.04705064))))) (* (log (+ 1.0 (exp (/ (- (- v_n3 (- (+ 0.23 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.8 (exp (- (/ 12.0 (* 2.0 lam_Mn3))))) v_n1))) (* 0.91 v_n1)) 0.04705064)))) (log (+ 1.0 (exp (/ (- (- v_n3 (- (+ 0.23 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.8 (exp (- (/ 12.0 (* 2.0 lam_Mn3))))) v_n1))) (* 0.91 v_n1)) 0.04705064)))))))) (+ (+ (+ (+ (* 2.0 (/ (/ 5.4 10000000000000000.0) (+ 5.5 dlisp_nm))) (* 2.0 (/ (/ 5.4 10000000000000000.0) (+ 5.5 dlisp_nm)))) (/ (/ 5.4 10000000000000000.0) (+ 5.5 dlisp_nm))) (/ (/ 5.4 10000000000000000.0) (+ 5.5 dlisp_nm))) (/ 1.8 1000000000000000.0))))
  (= d/dt[v_n2] (/ (- (* (* (/ 2.25 1000000.0) (* 3.0 (/ (* 2.0 (+ 18.0 (+ 5.0 dtns_nm))) 12.0))) (- (* (log (+ 1.0 (exp (/ (- (- vdd v_n1) (- (+ 0.24 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.9 (exp (- (/ 12.0 (* 2.0 lam_Mp1))))) (- vdd v_n2)))) 0.0465336)))) (log (+ 1.0 (exp (/ (- (- vdd v_n1) (- (+ 0.24 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.9 (exp (- (/ 12.0 (* 2.0 lam_Mp1))))) (- vdd v_n2)))) 0.0465336))))) (* (log (+ 1.0 (exp (/ (- (- (- vdd v_n1) (- (+ 0.24 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.9 (exp (- (/ 12.0 (* 2.0 lam_Mp1))))) (- vdd v_n2)))) (* 0.9 (- vdd v_n2))) 0.0465336)))) (log (+ 1.0 (exp (/ (- (- (- vdd v_n1) (- (+ 0.24 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.9 (exp (- (/ 12.0 (* 2.0 lam_Mp1))))) (- vdd v_n2)))) (* 0.9 (- vdd v_n2))) 0.0465336))))))) (* (* (/ 2.6 1000000.0) (* 3.0 (/ (* 2.0 (+ 18.0 (+ 5.0 dtns_nm))) 12.0))) (- (* (log (+ 1.0 (exp (/ (- v_n1 (- (+ 0.23 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.8 (exp (- (/ 12.0 (* 2.0 lam_Mn1))))) v_n2))) 0.04705064)))) (log (+ 1.0 (exp (/ (- v_n1 (- (+ 0.23 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.8 (exp (- (/ 12.0 (* 2.0 lam_Mn1))))) v_n2))) 0.04705064))))) (* (log (+ 1.0 (exp (/ (- (- v_n1 (- (+ 0.23 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.8 (exp (- (/ 12.0 (* 2.0 lam_Mn1))))) v_n2))) (* 0.91 v_n2)) 0.04705064)))) (log (+ 1.0 (exp (/ (- (- v_n1 (- (+ 0.23 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.8 (exp (- (/ 12.0 (* 2.0 lam_Mn1))))) v_n2))) (* 0.91 v_n2)) 0.04705064)))))))) (+ (+ (+ (+ (/ (/ 5.4 10000000000000000.0) (+ 5.5 dlisp_nm)) (/ (/ 5.4 10000000000000000.0) (+ 5.5 dlisp_nm))) (/ 1.8 1000000000000000.0)) (* 2.0 (/ (/ 5.4 10000000000000000.0) (+ 5.5 dlisp_nm)))) (* 2.0 (/ (/ 5.4 10000000000000000.0) (+ 5.5 dlisp_nm))))))
  (= d/dt[v_n3] (/ (- (* (* (/ 2.25 1000000.0) (* 3.0 (/ (* 2.0 (+ 18.0 (+ 5.0 dtns_nm))) 12.0))) (- (* (log (+ 1.0 (exp (/ (- (- vdd v_n2) (- (+ 0.24 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.9 (exp (- (/ 12.0 (* 2.0 lam_Mp2))))) (- vdd v_n3)))) 0.0465336)))) (log (+ 1.0 (exp (/ (- (- vdd v_n2) (- (+ 0.24 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.9 (exp (- (/ 12.0 (* 2.0 lam_Mp2))))) (- vdd v_n3)))) 0.0465336))))) (* (log (+ 1.0 (exp (/ (- (- (- vdd v_n2) (- (+ 0.24 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.9 (exp (- (/ 12.0 (* 2.0 lam_Mp2))))) (- vdd v_n3)))) (* 0.9 (- vdd v_n3))) 0.0465336)))) (log (+ 1.0 (exp (/ (- (- (- vdd v_n2) (- (+ 0.24 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.9 (exp (- (/ 12.0 (* 2.0 lam_Mp2))))) (- vdd v_n3)))) (* 0.9 (- vdd v_n3))) 0.0465336))))))) (* (* (/ 2.6 1000000.0) (* 3.0 (/ (* 2.0 (+ 18.0 (+ 5.0 dtns_nm))) 12.0))) (- (* (log (+ 1.0 (exp (/ (- v_n2 (- (+ 0.23 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.8 (exp (- (/ 12.0 (* 2.0 lam_Mn2))))) v_n3))) 0.04705064)))) (log (+ 1.0 (exp (/ (- v_n2 (- (+ 0.23 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.8 (exp (- (/ 12.0 (* 2.0 lam_Mn2))))) v_n3))) 0.04705064))))) (* (log (+ 1.0 (exp (/ (- (- v_n2 (- (+ 0.23 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.8 (exp (- (/ 12.0 (* 2.0 lam_Mn2))))) v_n3))) (* 0.91 v_n3)) 0.04705064)))) (log (+ 1.0 (exp (/ (- (- v_n2 (- (+ 0.23 (* 1.71 (- (/ 1.0 (* (+ 5.0 dtns_nm) (+ 5.0 dtns_nm))) 0.04))) (* (* 2.8 (exp (- (/ 12.0 (* 2.0 lam_Mn2))))) v_n3))) (* 0.91 v_n3)) 0.04705064)))))))) (+ (+ (+ (+ (/ (/ 5.4 10000000000000000.0) (+ 5.5 dlisp_nm)) (/ (/ 5.4 10000000000000000.0) (+ 5.5 dlisp_nm))) (/ 1.8 1000000000000000.0)) (* 2.0 (/ (/ 5.4 10000000000000000.0) (+ 5.5 dlisp_nm)))) (* 2.0 (/ (/ 5.4 10000000000000000.0) (+ 5.5 dlisp_nm))))))
))

(assert (= [t_t v_n1_t v_n2_t v_n3_t] (integral 0.0 tau_hit [t_0 v_n1_0 v_n2_0 v_n3_0] flow_1)))
(assert (forall_t 1 [0.0 tau_hit] (and (>= v_n1_t (- 0.2)) (<= v_n1_t 0.9))))
(assert (forall_t 1 [0.0 tau_hit] (and (>= v_n2_t (- 0.2)) (<= v_n2_t 0.9))))
(assert (forall_t 1 [0.0 tau_hit] (and (>= v_n3_t (- 0.2)) (<= v_n3_t 0.9))))

; --- Existential Unsafe Reachability at Hit Time tau_hit in [0, (/ 1.0 100000000000.0)] ---
(assert (or (> v_n1_t (+ vdd 0.12)) (< v_n1_t (- 0.12)) (> v_n2_t (+ vdd 0.12)) (< v_n2_t (- 0.12))))

(check-sat)
(exit)
