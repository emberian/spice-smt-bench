; ============================================================================
; Benchmark : Six-transistor FinFET SRAM read-disturb, stored 1; manufacturing-defect twin b
; PDK       : asap7 (7nm Multi-Gate FinFET (Clark et al. ASAP7 class: Lg=21nm, Tfin=6.5nm, Hfin=32nm, HfO2 EOT=1.0nm, quantum confinement + DIBL))
; Dialect   : dreal-ode (QF_NRA + exp + continuous define-ode)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic QF_NRA_ODE)
(set-info :smt-lib-version 2.6)
(set-info :status sat)

; --- Continuous Parameter / Defect / Litho Uncertainty Box ---
(declare-fun dtfin_nm () Real)
(assert (and (>= dtfin_nm (- 0.35)) (<= dtfin_nm 0.35)))
(declare-fun dt_fin_pdb () Real)
(assert (and (>= dt_fin_pdb (- 2.2)) (<= dt_fin_pdb (- 1.4))))
(declare-fun dphim () Real)
(assert (and (>= dphim 0.42) (<= dphim 0.48)))

; --- Time-Invariant Geometry & Interconnect Variables ---
; Multi-gate natural scaling length lambda [nm] (Mpu_a)
(declare-fun lam_Mpu_a () Real)
; Multi-gate natural scaling length lambda [nm] (Mpd_a)
(declare-fun lam_Mpd_a () Real)
; Multi-gate natural scaling length lambda [nm] (Mpg_a)
(declare-fun lam_Mpg_a () Real)
; Multi-gate natural scaling length lambda [nm] (Mpu_b)
(declare-fun lam_Mpu_b () Real)
; Multi-gate natural scaling length lambda [nm] (Mpd_b)
(declare-fun lam_Mpd_b () Real)
; Multi-gate natural scaling length lambda [nm] (Mpg_b)
(declare-fun lam_Mpg_b () Real)
; Positive thermal voltage
(assert (> 0.025852 0.0))
; Positive body thickness
(assert (> (+ 6.5 dtfin_nm) 0.0))
; Positive gate length
(assert (> 21.0 0.0))
; Nonnegative square root
(assert (>= lam_Mpu_a 0.0))
; Algebraic sqrt constraint lam_Mpu_a^2 = radicand (Multi-gate natural scaling length lambda [nm] (Mpu_a))
(assert (= (* lam_Mpu_a lam_Mpu_a) (+ 6.5 dtfin_nm)))
; Positive thermal voltage
(assert (> 0.025852 0.0))
; Positive body thickness
(assert (> (+ 6.5 dtfin_nm) 0.0))
; Positive gate length
(assert (> 21.0 0.0))
; Nonnegative square root
(assert (>= lam_Mpd_a 0.0))
; Algebraic sqrt constraint lam_Mpd_a^2 = radicand (Multi-gate natural scaling length lambda [nm] (Mpd_a))
(assert (= (* lam_Mpd_a lam_Mpd_a) (+ 6.5 dtfin_nm)))
; Positive thermal voltage
(assert (> 0.025852 0.0))
; Positive body thickness
(assert (> 6.5 0.0))
; Positive gate length
(assert (> 21.0 0.0))
; Nonnegative square root
(assert (>= lam_Mpg_a 0.0))
; Algebraic sqrt constraint lam_Mpg_a^2 = radicand (Multi-gate natural scaling length lambda [nm] (Mpg_a))
(assert (= (* lam_Mpg_a lam_Mpg_a) 6.5))
; Positive thermal voltage
(assert (> 0.025852 0.0))
; Positive body thickness
(assert (> (+ 6.5 dtfin_nm) 0.0))
; Positive gate length
(assert (> 21.0 0.0))
; Nonnegative square root
(assert (>= lam_Mpu_b 0.0))
; Algebraic sqrt constraint lam_Mpu_b^2 = radicand (Multi-gate natural scaling length lambda [nm] (Mpu_b))
(assert (= (* lam_Mpu_b lam_Mpu_b) (+ 6.5 dtfin_nm)))
; Positive thermal voltage
(assert (> 0.025852 0.0))
; Positive body thickness
(assert (> (+ 6.5 dt_fin_pdb) 0.0))
; Positive gate length
(assert (> 21.0 0.0))
; Nonnegative square root
(assert (>= lam_Mpd_b 0.0))
; Algebraic sqrt constraint lam_Mpd_b^2 = radicand (Multi-gate natural scaling length lambda [nm] (Mpd_b))
(assert (= (* lam_Mpd_b lam_Mpd_b) (+ 6.5 dt_fin_pdb)))
; Positive thermal voltage
(assert (> 0.025852 0.0))
; Positive body thickness
(assert (> 6.5 0.0))
; Positive gate length
(assert (> 21.0 0.0))
; Nonnegative square root
(assert (>= lam_Mpg_b 0.0))
; Algebraic sqrt constraint lam_Mpg_b^2 = radicand (Multi-gate natural scaling length lambda [nm] (Mpg_b))
(assert (= (* lam_Mpg_b lam_Mpg_b) 6.5))

; --- Continuous ODE Flow Variables & Initial/Final Endpoints ---
(declare-fun t () Real)
(declare-fun t_0 () Real)
(declare-fun t_t () Real)
(declare-fun tau_hit () Real)
(assert (and (= t_0 0.0) (>= tau_hit 0.0) (<= tau_hit 0.00000000019999999999999998) (= t_t tau_hit)))
; Dynamic node voltage v(q) [V]
(declare-fun v_q () Real)
(declare-fun v_q_0 () Real)
(declare-fun v_q_t () Real)
(assert (and (>= v_q_0 (- 0.05)) (<= v_q_0 0.8)))
(assert (and (>= v_q_t (- 0.05)) (<= v_q_t 0.8)))
; Dynamic node voltage v(qb) [V]
(declare-fun v_qb () Real)
(declare-fun v_qb_0 () Real)
(declare-fun v_qb_t () Real)
(assert (and (>= v_qb_0 (- 0.05)) (<= v_qb_0 0.8)))
(assert (and (>= v_qb_t (- 0.05)) (<= v_qb_t 0.8)))

; --- Initial Condition X_0 ---
(assert (= v_q_0 0.7))
(assert (= v_qb_0 0.0))

; --- Continuous Nonlinear Circuit ODE Flow ---
(define-ode flow_1 (
  (= d/dt[t] 1.0)
  (= d/dt[v_q] (/ (+ (- (/ (* (* 0.00000026 (/ (+ 64.0 (+ 6.5 dtfin_nm)) 21.0)) (- (* (log (+ 1.0 (exp (/ (* 0.84 (- (- 0.7 v_qb) (- (+ 0.33 (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.2 (exp (- (/ 21.0 (* 2.0 lam_Mpu_a))))) (- 0.7 v_q))))) 0.051704)))) (log (+ 1.0 (exp (/ (* 0.84 (- (- 0.7 v_qb) (- (+ 0.33 (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.2 (exp (- (/ 21.0 (* 2.0 lam_Mpu_a))))) (- 0.7 v_q))))) 0.051704))))) (* (log (+ 1.0 (exp (/ (- (* 0.84 (- (- 0.7 v_qb) (- (+ 0.33 (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.2 (exp (- (/ 21.0 (* 2.0 lam_Mpu_a))))) (- 0.7 v_q))))) (- 0.7 v_q)) 0.051704)))) (log (+ 1.0 (exp (/ (- (* 0.84 (- (- 0.7 v_qb) (- (+ 0.33 (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.2 (exp (- (/ 21.0 (* 2.0 lam_Mpu_a))))) (- 0.7 v_q))))) (- 0.7 v_q)) 0.051704))))))) (+ 1.0 (* 0.1 (log (+ 1.0 (exp (/ (* 0.84 (- (- 0.7 v_qb) (- (+ 0.33 (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.2 (exp (- (/ 21.0 (* 2.0 lam_Mpu_a))))) (- 0.7 v_q))))) 0.051704))))))) (/ (* (* 0.0000003 (* 2.0 (/ (+ 64.0 (+ 6.5 dtfin_nm)) 21.0))) (- (* (log (+ 1.0 (exp (/ (* 0.85 (- v_qb (- (+ 0.32 (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpd_a))))) v_q)))) 0.051704)))) (log (+ 1.0 (exp (/ (* 0.85 (- v_qb (- (+ 0.32 (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpd_a))))) v_q)))) 0.051704))))) (* (log (+ 1.0 (exp (/ (- (* 0.85 (- v_qb (- (+ 0.32 (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpd_a))))) v_q)))) v_q) 0.051704)))) (log (+ 1.0 (exp (/ (- (* 0.85 (- v_qb (- (+ 0.32 (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpd_a))))) v_q)))) v_q) 0.051704))))))) (+ 1.0 (* 0.1 (log (+ 1.0 (exp (/ (* 0.85 (- v_qb (- (+ 0.32 (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpd_a))))) v_q)))) 0.051704)))))))) (/ (* 0.0000010071428571428572 (- (* (log (+ 1.0 (exp (/ (* 0.85 (- (- 0.7 v_q) (- 0.32 (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpg_a))))) (- 0.7 v_q))))) 0.051704)))) (log (+ 1.0 (exp (/ (* 0.85 (- (- 0.7 v_q) (- 0.32 (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpg_a))))) (- 0.7 v_q))))) 0.051704))))) (* (log (+ 1.0 (exp (/ (- (* 0.85 (- (- 0.7 v_q) (- 0.32 (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpg_a))))) (- 0.7 v_q))))) (- 0.7 v_q)) 0.051704)))) (log (+ 1.0 (exp (/ (- (* 0.85 (- (- 0.7 v_q) (- 0.32 (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpg_a))))) (- 0.7 v_q))))) (- 0.7 v_q)) 0.051704))))))) (+ 1.0 (* 0.1 (log (+ 1.0 (exp (/ (* 0.85 (- (- 0.7 v_q) (- 0.32 (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpg_a))))) (- 0.7 v_q))))) 0.051704)))))))) 0.000000000000001))
  (= d/dt[v_qb] (/ (+ (- (/ (* (* 0.00000026 (/ (+ 64.0 (+ 6.5 dtfin_nm)) 21.0)) (- (* (log (+ 1.0 (exp (/ (* 0.84 (- (- 0.7 v_q) (- (+ 0.33 (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.2 (exp (- (/ 21.0 (* 2.0 lam_Mpu_b))))) (- 0.7 v_qb))))) 0.051704)))) (log (+ 1.0 (exp (/ (* 0.84 (- (- 0.7 v_q) (- (+ 0.33 (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.2 (exp (- (/ 21.0 (* 2.0 lam_Mpu_b))))) (- 0.7 v_qb))))) 0.051704))))) (* (log (+ 1.0 (exp (/ (- (* 0.84 (- (- 0.7 v_q) (- (+ 0.33 (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.2 (exp (- (/ 21.0 (* 2.0 lam_Mpu_b))))) (- 0.7 v_qb))))) (- 0.7 v_qb)) 0.051704)))) (log (+ 1.0 (exp (/ (- (* 0.84 (- (- 0.7 v_q) (- (+ 0.33 (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.2 (exp (- (/ 21.0 (* 2.0 lam_Mpu_b))))) (- 0.7 v_qb))))) (- 0.7 v_qb)) 0.051704))))))) (+ 1.0 (* 0.1 (log (+ 1.0 (exp (/ (* 0.84 (- (- 0.7 v_q) (- (+ 0.33 (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.2 (exp (- (/ 21.0 (* 2.0 lam_Mpu_b))))) (- 0.7 v_qb))))) 0.051704))))))) (/ (* (* 0.0000003 (* 2.0 (/ (+ 64.0 (+ 6.5 dt_fin_pdb)) 21.0))) (- (* (log (+ 1.0 (exp (/ (* 0.85 (- v_q (- (+ (+ 0.32 dphim) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dt_fin_pdb) (+ 6.5 dt_fin_pdb))) 0.023668639053254437))) (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpd_b))))) v_qb)))) 0.051704)))) (log (+ 1.0 (exp (/ (* 0.85 (- v_q (- (+ (+ 0.32 dphim) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dt_fin_pdb) (+ 6.5 dt_fin_pdb))) 0.023668639053254437))) (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpd_b))))) v_qb)))) 0.051704))))) (* (log (+ 1.0 (exp (/ (- (* 0.85 (- v_q (- (+ (+ 0.32 dphim) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dt_fin_pdb) (+ 6.5 dt_fin_pdb))) 0.023668639053254437))) (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpd_b))))) v_qb)))) v_qb) 0.051704)))) (log (+ 1.0 (exp (/ (- (* 0.85 (- v_q (- (+ (+ 0.32 dphim) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dt_fin_pdb) (+ 6.5 dt_fin_pdb))) 0.023668639053254437))) (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpd_b))))) v_qb)))) v_qb) 0.051704))))))) (+ 1.0 (* 0.1 (log (+ 1.0 (exp (/ (* 0.85 (- v_q (- (+ (+ 0.32 dphim) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dt_fin_pdb) (+ 6.5 dt_fin_pdb))) 0.023668639053254437))) (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpd_b))))) v_qb)))) 0.051704)))))))) (/ (* 0.0000010071428571428572 (- (* (log (+ 1.0 (exp (/ (* 0.85 (- (- 0.7 v_qb) (- 0.32 (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpg_b))))) (- 0.7 v_qb))))) 0.051704)))) (log (+ 1.0 (exp (/ (* 0.85 (- (- 0.7 v_qb) (- 0.32 (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpg_b))))) (- 0.7 v_qb))))) 0.051704))))) (* (log (+ 1.0 (exp (/ (- (* 0.85 (- (- 0.7 v_qb) (- 0.32 (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpg_b))))) (- 0.7 v_qb))))) (- 0.7 v_qb)) 0.051704)))) (log (+ 1.0 (exp (/ (- (* 0.85 (- (- 0.7 v_qb) (- 0.32 (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpg_b))))) (- 0.7 v_qb))))) (- 0.7 v_qb)) 0.051704))))))) (+ 1.0 (* 0.1 (log (+ 1.0 (exp (/ (* 0.85 (- (- 0.7 v_qb) (- 0.32 (* (* 3.0 (exp (- (/ 21.0 (* 2.0 lam_Mpg_b))))) (- 0.7 v_qb))))) 0.051704)))))))) 0.000000000000001))
))

(assert (= [t_t v_q_t v_qb_t] (integral 0.0 tau_hit [t_0 v_q_0 v_qb_0] flow_1)))
(assert (forall_t 1 [0.0 tau_hit] (and (>= v_q_t (- 0.05)) (<= v_q_t 0.8))))
(assert (forall_t 1 [0.0 tau_hit] (and (>= v_qb_t (- 0.05)) (<= v_qb_t 0.8))))

; --- Existential Unsafe Reachability at Hit Time tau_hit in [0, 0.00000000019999999999999998] ---
(assert (< (- v_q_t v_qb_t) 0.12))

(check-sat)
(exit)
