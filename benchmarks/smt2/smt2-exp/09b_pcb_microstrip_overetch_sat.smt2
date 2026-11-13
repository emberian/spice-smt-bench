; ============================================================================
; Benchmark : Suite C-09b: Uncontrolled PCB Fab Over-Etch + Resin-Rich Prepreg Corner Violating Z0 Tolerance (SAT)
; Dialect   : smt2-exp (QF_NRA + transcendental exp)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic ALL)
(set-info :smt-lib-version 2.6)
(set-info :status sat)

; --- Continuous Parameter / Defect / Litho Uncertainty Box ---
(declare-fun dw_etch () Real)
(assert (and (>= dw_etch (- 0.000042)) (<= dw_etch 0.000005)))
(declare-fun dh_lam () Real)
(assert (and (>= dh_lam (- 0.000012)) (<= dh_lam 0.000018)))
(declare-fun t_cu () Real)
(assert (and (>= t_cu 0.000028) (<= t_cu 0.000038)))
(declare-fun er_lam () Real)
(assert (and (>= er_lam 3.85) (<= er_lam 4.5)))

; --- State & Auxiliary Variables ---
; Node voltage v(tx) [V]
(declare-fun v_tx () Real)
(assert (and (>= v_tx (- 0.5)) (<= v_tx 5.0)))
; Voltage source branch current (Vdrv)
(declare-fun i_Vdrv () Real)
; Node voltage v(rx) [V]
(declare-fun v_rx () Real)
(assert (and (>= v_rx (- 0.5)) (<= v_rx 5.0)))
; Bahl-Garg thickness correction
(declare-fun thickness_log_tl50 () Real)
; Hammerstad-Jensen sqrt(1 + 12/u) for tl50
(declare-fun su_tl50 () Real)
; Effective microstrip permittivity e_eff (tl50)
(declare-fun eeff_tl50 () Real)
; sqrt(e_eff) for tl50
(declare-fun seeff_tl50 () Real)
; Wheeler-Hammerstad log geometry factor (tl50)
(declare-fun lnz_tl50 () Real)
; Characteristic impedance Z0 [Ohm] (tl50)
(declare-fun Z0_tl50 () Real)
; Wide-strip logarithm
(declare-fun wide_log_tl50 () Real)
; Total microstrip inductance [H] (tl50)
(declare-fun Ltot_tl50 () Real)
; Total microstrip capacitance [F] (tl50)
(declare-fun Ctot_tl50 () Real)
;  Copper trace DC resistance [Ohm] (tl50)
(declare-fun Rdc_tl50 () Real)

; --- Constitutive & Conservation Laws (MNA / PCB EM / TCAD) ---
; Voltage source constitutive equation (Vdrv)
(assert (= v_tx 1.0))
; Positive microstrip dimension or conductivity
(assert (> (+ 0.00018 dw_etch) 0.0))
; Positive microstrip dimension or conductivity
(assert (> (+ 0.0001 dh_lam) 0.0))
; Positive microstrip dimension or conductivity
(assert (> t_cu 0.0))
; Positive microstrip dimension or conductivity
(assert (> 58000000.0 0.0))
; Pure-exp logarithm constraint exp(thickness_log_tl50) = arg (Bahl-Garg thickness correction)
(assert (= (exp thickness_log_tl50) (/ (* 2.0 (+ 0.0001 dh_lam)) t_cu)))
; Nonnegative square root
(assert (>= su_tl50 0.0))
; Algebraic sqrt constraint su_tl50^2 = radicand (Hammerstad-Jensen sqrt(1 + 12/u) for tl50)
(assert (= (* su_tl50 su_tl50) (+ 1.0 (/ 12.0 (/ (+ (+ 0.00018 dw_etch) (* (/ t_cu 3.141592653589793) (+ 1.0 thickness_log_tl50))) (+ 0.0001 dh_lam))))))
; Hammerstad-Jensen effective permittivity (tl50)
(assert (= eeff_tl50 (+ (/ (+ er_lam 1.0) 2.0) (/ (- er_lam 1.0) (* 2.0 su_tl50)))))
; Nonnegative square root
(assert (>= seeff_tl50 0.0))
; Algebraic sqrt constraint seeff_tl50^2 = radicand (sqrt(e_eff) for tl50)
(assert (= (* seeff_tl50 seeff_tl50) eeff_tl50))
; Pure-exp logarithm constraint exp(lnz_tl50) = arg (Wheeler-Hammerstad log geometry factor (tl50))
(assert (= (exp lnz_tl50) (+ (/ 8.0 (/ (+ (+ 0.00018 dw_etch) (* (/ t_cu 3.141592653589793) (+ 1.0 thickness_log_tl50))) (+ 0.0001 dh_lam))) (/ (/ (+ (+ 0.00018 dw_etch) (* (/ t_cu 3.141592653589793) (+ 1.0 thickness_log_tl50))) (+ 0.0001 dh_lam)) 4.0))))
; Pure-exp logarithm constraint exp(wide_log_tl50) = arg (Wide-strip logarithm)
(assert (= (exp wide_log_tl50) (+ (/ (+ (+ 0.00018 dw_etch) (* (/ t_cu 3.141592653589793) (+ 1.0 thickness_log_tl50))) (+ 0.0001 dh_lam)) 1.444)))
; Hammerstad-Jensen wide-strip impedance (tl50)
(assert (= Z0_tl50 (/ 376.99111843077515 (* seeff_tl50 (+ (+ (/ (+ (+ 0.00018 dw_etch) (* (/ t_cu 3.141592653589793) (+ 1.0 thickness_log_tl50))) (+ 0.0001 dh_lam)) 1.393) (* 0.667 wide_log_tl50))))))
; Microstrip total inductance L_tot (tl50)
(assert (= Ltot_tl50 (/ (* 0.05 (* Z0_tl50 seeff_tl50)) 299792458.0)))
; Microstrip total capacitance C_tot (tl50)
(assert (= (* Ctot_tl50 Z0_tl50) (/ (* 0.05 seeff_tl50) 299792458.0)))
; Rectangular copper cross-section DC resistance R_dc (tl50)
(assert (= (* Rdc_tl50 (* 58000000.0 (* (+ 0.00018 dw_etch) t_cu))) 0.05))
; MNA Kirchhoff Current Law at node `rx`
(assert (= (+ (- (/ (- v_tx v_rx) Rdc_tl50)) (/ v_rx 50.0)) 0.0))
; MNA Kirchhoff Current Law at node `tx`
(assert (= (+ i_Vdrv (/ (- v_tx v_rx) Rdc_tl50)) 0.0))

(assert (=> (>= lnz_tl50 25.0) (>= (exp lnz_tl50) 8000000000.0)))
(assert (=> (>= thickness_log_tl50 25.0) (>= (exp thickness_log_tl50) 8000000000.0)))
(assert (=> (>= wide_log_tl50 25.0) (>= (exp wide_log_tl50) 8000000000.0)))
; --- Negated Safety Specification (.unsafe) ---
(assert (> Z0_tl50 56.0))

(check-sat)
(exit)
