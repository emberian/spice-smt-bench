; ============================================================================
; Benchmark : Suite C-09a: IPC Class-3 Controlled-Impedance PCB Microstrip & Diffpair Over 5D Fab Defect Polytope
; Dialect   : smt2-exp (QF_NRA + transcendental exp)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic ALL)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)

; --- Continuous Parameter / Defect / Litho Uncertainty Box ---
(declare-fun dw_etch () Real)
(assert (and (>= dw_etch (- 0.000008)) (<= dw_etch 0.000004)))
(declare-fun ds_etch () Real)
(assert (and (>= ds_etch (- 0.000004)) (<= ds_etch 0.000008)))
(declare-fun dh_lam () Real)
(assert (and (>= dh_lam (- 0.000005)) (<= dh_lam 0.000005)))
(declare-fun t_cu () Real)
(assert (and (>= t_cu 0.000032) (<= t_cu 0.000038)))
(declare-fun er_lam () Real)
(assert (and (>= er_lam 4.15) (<= er_lam 4.35)))

; --- State & Auxiliary Variables ---
; Node voltage v(tx) [V]
(declare-fun v_tx () Real)
(assert (and (>= v_tx (- 0.5)) (<= v_tx 5.0)))
; Voltage source branch current (Vdrv)
(declare-fun i_Vdrv () Real)
; Node voltage v(tx_p) [V]
(declare-fun v_tx_p () Real)
(assert (and (>= v_tx_p (- 0.5)) (<= v_tx_p 5.0)))
; Voltage source branch current (Vdp)
(declare-fun i_Vdp () Real)
; Node voltage v(tx_n) [V]
(declare-fun v_tx_n () Real)
(assert (and (>= v_tx_n (- 0.5)) (<= v_tx_n 5.0)))
; Voltage source branch current (Vdn)
(declare-fun i_Vdn () Real)
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
; Node voltage v(rx_p) [V]
(declare-fun v_rx_p () Real)
(assert (and (>= v_rx_p (- 0.5)) (<= v_rx_p 5.0)))
; Node voltage v(rx_n) [V]
(declare-fun v_rx_n () Real)
(assert (and (>= v_rx_n (- 0.5)) (<= v_rx_n 5.0)))
; Bahl-Garg thickness correction
(declare-fun thickness_log_diff90_p () Real)
; Hammerstad-Jensen sqrt(1 + 12/u) for diff90_p
(declare-fun su_diff90_p () Real)
; Effective microstrip permittivity e_eff (diff90_p)
(declare-fun eeff_diff90_p () Real)
; sqrt(e_eff) for diff90_p
(declare-fun seeff_diff90_p () Real)
; Wheeler-Hammerstad log geometry factor (diff90_p)
(declare-fun lnz_diff90_p () Real)
; Characteristic impedance Z0 [Ohm] (diff90_p)
(declare-fun Z0_diff90_p () Real)
; Wide-strip logarithm
(declare-fun wide_log_diff90_p () Real)
; Total microstrip inductance [H] (diff90_p)
(declare-fun Ltot_diff90_p () Real)
; Total microstrip capacitance [F] (diff90_p)
(declare-fun Ctot_diff90_p () Real)
;  Copper trace DC resistance [Ohm] (diff90_p)
(declare-fun Rdc_diff90_p () Real)
; Bahl-Garg thickness correction
(declare-fun thickness_log_diff90_n () Real)
; Hammerstad-Jensen sqrt(1 + 12/u) for diff90_n
(declare-fun su_diff90_n () Real)
; Effective microstrip permittivity e_eff (diff90_n)
(declare-fun eeff_diff90_n () Real)
; sqrt(e_eff) for diff90_n
(declare-fun seeff_diff90_n () Real)
; Wheeler-Hammerstad log geometry factor (diff90_n)
(declare-fun lnz_diff90_n () Real)
; Characteristic impedance Z0 [Ohm] (diff90_n)
(declare-fun Z0_diff90_n () Real)
; Wide-strip logarithm
(declare-fun wide_log_diff90_n () Real)
; Total microstrip inductance [H] (diff90_n)
(declare-fun Ltot_diff90_n () Real)
; Total microstrip capacitance [F] (diff90_n)
(declare-fun Ctot_diff90_n () Real)
;  Copper trace DC resistance [Ohm] (diff90_n)
(declare-fun Rdc_diff90_n () Real)
; Edge-coupled microstrip coupling factor kc (diff90)
(declare-fun kc_diff90 () Real)
; Differential impedance Z_diff [Ohm] (diff90)
(declare-fun Zdiff_diff90 () Real)
; Odd-mode impedance factor
(declare-fun odd_factor_diff90 () Real)
; Mutual trace capacitance C_m [F] (diff90)
(declare-fun Cm_diff90 () Real)
; Mutual trace inductance L_m [H] (diff90)
(declare-fun Lm_diff90 () Real)

; --- Constitutive & Conservation Laws (MNA / PCB EM / TCAD) ---
; Voltage source constitutive equation (Vdrv)
(assert (= v_tx 1.0))
; Voltage source constitutive equation (Vdp)
(assert (= v_tx_p 0.5))
; Voltage source constitutive equation (Vdn)
(assert (= v_tx_n (- 0.5)))
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
; Positive microstrip dimension or conductivity
(assert (> (+ 0.00017 dw_etch) 0.0))
; Positive microstrip dimension or conductivity
(assert (> (+ 0.0001 dh_lam) 0.0))
; Positive microstrip dimension or conductivity
(assert (> t_cu 0.0))
; Positive microstrip dimension or conductivity
(assert (> 58000000.0 0.0))
; Pure-exp logarithm constraint exp(thickness_log_diff90_p) = arg (Bahl-Garg thickness correction)
(assert (= (exp thickness_log_diff90_p) (/ (* 2.0 (+ 0.0001 dh_lam)) t_cu)))
; Nonnegative square root
(assert (>= su_diff90_p 0.0))
; Algebraic sqrt constraint su_diff90_p^2 = radicand (Hammerstad-Jensen sqrt(1 + 12/u) for diff90_p)
(assert (= (* su_diff90_p su_diff90_p) (+ 1.0 (/ 12.0 (/ (+ (+ 0.00017 dw_etch) (* (/ t_cu 3.141592653589793) (+ 1.0 thickness_log_diff90_p))) (+ 0.0001 dh_lam))))))
; Hammerstad-Jensen effective permittivity (diff90_p)
(assert (= eeff_diff90_p (+ (/ (+ er_lam 1.0) 2.0) (/ (- er_lam 1.0) (* 2.0 su_diff90_p)))))
; Nonnegative square root
(assert (>= seeff_diff90_p 0.0))
; Algebraic sqrt constraint seeff_diff90_p^2 = radicand (sqrt(e_eff) for diff90_p)
(assert (= (* seeff_diff90_p seeff_diff90_p) eeff_diff90_p))
; Pure-exp logarithm constraint exp(lnz_diff90_p) = arg (Wheeler-Hammerstad log geometry factor (diff90_p))
(assert (= (exp lnz_diff90_p) (+ (/ 8.0 (/ (+ (+ 0.00017 dw_etch) (* (/ t_cu 3.141592653589793) (+ 1.0 thickness_log_diff90_p))) (+ 0.0001 dh_lam))) (/ (/ (+ (+ 0.00017 dw_etch) (* (/ t_cu 3.141592653589793) (+ 1.0 thickness_log_diff90_p))) (+ 0.0001 dh_lam)) 4.0))))
; Pure-exp logarithm constraint exp(wide_log_diff90_p) = arg (Wide-strip logarithm)
(assert (= (exp wide_log_diff90_p) (+ (/ (+ (+ 0.00017 dw_etch) (* (/ t_cu 3.141592653589793) (+ 1.0 thickness_log_diff90_p))) (+ 0.0001 dh_lam)) 1.444)))
; Hammerstad-Jensen wide-strip impedance (diff90_p)
(assert (= Z0_diff90_p (/ 376.99111843077515 (* seeff_diff90_p (+ (+ (/ (+ (+ 0.00017 dw_etch) (* (/ t_cu 3.141592653589793) (+ 1.0 thickness_log_diff90_p))) (+ 0.0001 dh_lam)) 1.393) (* 0.667 wide_log_diff90_p))))))
; Microstrip total inductance L_tot (diff90_p)
(assert (= Ltot_diff90_p (/ (* 0.05 (* Z0_diff90_p seeff_diff90_p)) 299792458.0)))
; Microstrip total capacitance C_tot (diff90_p)
(assert (= (* Ctot_diff90_p Z0_diff90_p) (/ (* 0.05 seeff_diff90_p) 299792458.0)))
; Rectangular copper cross-section DC resistance R_dc (diff90_p)
(assert (= (* Rdc_diff90_p (* 58000000.0 (* (+ 0.00017 dw_etch) t_cu))) 0.05))
; Positive microstrip dimension or conductivity
(assert (> (+ 0.00017 dw_etch) 0.0))
; Positive microstrip dimension or conductivity
(assert (> (+ 0.0001 dh_lam) 0.0))
; Positive microstrip dimension or conductivity
(assert (> t_cu 0.0))
; Positive microstrip dimension or conductivity
(assert (> 58000000.0 0.0))
; Pure-exp logarithm constraint exp(thickness_log_diff90_n) = arg (Bahl-Garg thickness correction)
(assert (= (exp thickness_log_diff90_n) (/ (* 2.0 (+ 0.0001 dh_lam)) t_cu)))
; Nonnegative square root
(assert (>= su_diff90_n 0.0))
; Algebraic sqrt constraint su_diff90_n^2 = radicand (Hammerstad-Jensen sqrt(1 + 12/u) for diff90_n)
(assert (= (* su_diff90_n su_diff90_n) (+ 1.0 (/ 12.0 (/ (+ (+ 0.00017 dw_etch) (* (/ t_cu 3.141592653589793) (+ 1.0 thickness_log_diff90_n))) (+ 0.0001 dh_lam))))))
; Hammerstad-Jensen effective permittivity (diff90_n)
(assert (= eeff_diff90_n (+ (/ (+ er_lam 1.0) 2.0) (/ (- er_lam 1.0) (* 2.0 su_diff90_n)))))
; Nonnegative square root
(assert (>= seeff_diff90_n 0.0))
; Algebraic sqrt constraint seeff_diff90_n^2 = radicand (sqrt(e_eff) for diff90_n)
(assert (= (* seeff_diff90_n seeff_diff90_n) eeff_diff90_n))
; Pure-exp logarithm constraint exp(lnz_diff90_n) = arg (Wheeler-Hammerstad log geometry factor (diff90_n))
(assert (= (exp lnz_diff90_n) (+ (/ 8.0 (/ (+ (+ 0.00017 dw_etch) (* (/ t_cu 3.141592653589793) (+ 1.0 thickness_log_diff90_n))) (+ 0.0001 dh_lam))) (/ (/ (+ (+ 0.00017 dw_etch) (* (/ t_cu 3.141592653589793) (+ 1.0 thickness_log_diff90_n))) (+ 0.0001 dh_lam)) 4.0))))
; Pure-exp logarithm constraint exp(wide_log_diff90_n) = arg (Wide-strip logarithm)
(assert (= (exp wide_log_diff90_n) (+ (/ (+ (+ 0.00017 dw_etch) (* (/ t_cu 3.141592653589793) (+ 1.0 thickness_log_diff90_n))) (+ 0.0001 dh_lam)) 1.444)))
; Hammerstad-Jensen wide-strip impedance (diff90_n)
(assert (= Z0_diff90_n (/ 376.99111843077515 (* seeff_diff90_n (+ (+ (/ (+ (+ 0.00017 dw_etch) (* (/ t_cu 3.141592653589793) (+ 1.0 thickness_log_diff90_n))) (+ 0.0001 dh_lam)) 1.393) (* 0.667 wide_log_diff90_n))))))
; Microstrip total inductance L_tot (diff90_n)
(assert (= Ltot_diff90_n (/ (* 0.05 (* Z0_diff90_n seeff_diff90_n)) 299792458.0)))
; Microstrip total capacitance C_tot (diff90_n)
(assert (= (* Ctot_diff90_n Z0_diff90_n) (/ (* 0.05 seeff_diff90_n) 299792458.0)))
; Rectangular copper cross-section DC resistance R_dc (diff90_n)
(assert (= (* Rdc_diff90_n (* 58000000.0 (* (+ 0.00017 dw_etch) t_cu))) 0.05))
; Exponential edge-coupling law kc = exp(-1.9 * s_eff / h_eff) (diff90)
(assert (= kc_diff90 (exp (- (/ (* 1.9 (+ 0.00018 ds_etch)) (+ 0.0001 dh_lam))))))
; Nonnegative square root
(assert (>= odd_factor_diff90 0.0))
; Algebraic sqrt constraint odd_factor_diff90^2 = radicand (Odd-mode impedance factor)
(assert (= (* odd_factor_diff90 odd_factor_diff90) (/ (- 1.0 kc_diff90) (+ 1.0 kc_diff90))))
; Differential impedance of coupled LC ladder (diff90)
(assert (= Zdiff_diff90 (* (+ Z0_diff90_p Z0_diff90_n) odd_factor_diff90)))
; Mutual capacitance C_m = 0.5 * kc * (C_p + C_n) (diff90)
(assert (= Cm_diff90 (* 0.5 (* kc_diff90 (+ Ctot_diff90_p Ctot_diff90_n)))))
; Mutual inductance L_m = 0.5 * kc * (L_p + L_n) (diff90)
(assert (= Lm_diff90 (* 0.5 (* kc_diff90 (+ Ltot_diff90_p Ltot_diff90_n)))))
; MNA Kirchhoff Current Law at node `rx`
(assert (= (+ (- (/ (- v_tx v_rx) Rdc_tl50)) (/ v_rx 50.0)) 0.0))
; MNA Kirchhoff Current Law at node `rx_n`
(assert (= (+ (- (/ (- v_tx_n v_rx_n) Rdc_diff90_n)) (/ v_rx_n 45.0)) 0.0))
; MNA Kirchhoff Current Law at node `rx_p`
(assert (= (+ (- (/ (- v_tx_p v_rx_p) Rdc_diff90_p)) (/ v_rx_p 45.0)) 0.0))
; MNA Kirchhoff Current Law at node `tx`
(assert (= (+ i_Vdrv (/ (- v_tx v_rx) Rdc_tl50)) 0.0))
; MNA Kirchhoff Current Law at node `tx_n`
(assert (= (+ i_Vdn (/ (- v_tx_n v_rx_n) Rdc_diff90_n)) 0.0))
; MNA Kirchhoff Current Law at node `tx_p`
(assert (= (+ i_Vdp (/ (- v_tx_p v_rx_p) Rdc_diff90_p)) 0.0))

(assert (=> (>= (- (/ (* 1.9 (+ 0.00018 ds_etch)) (+ 0.0001 dh_lam))) 25.0) (>= (exp (- (/ (* 1.9 (+ 0.00018 ds_etch)) (+ 0.0001 dh_lam)))) 8000000000.0)))
(assert (=> (>= lnz_diff90_n 25.0) (>= (exp lnz_diff90_n) 8000000000.0)))
(assert (=> (>= lnz_diff90_p 25.0) (>= (exp lnz_diff90_p) 8000000000.0)))
(assert (=> (>= lnz_tl50 25.0) (>= (exp lnz_tl50) 8000000000.0)))
(assert (=> (>= thickness_log_diff90_n 25.0) (>= (exp thickness_log_diff90_n) 8000000000.0)))
(assert (=> (>= thickness_log_diff90_p 25.0) (>= (exp thickness_log_diff90_p) 8000000000.0)))
(assert (=> (>= thickness_log_tl50 25.0) (>= (exp thickness_log_tl50) 8000000000.0)))
(assert (=> (>= wide_log_diff90_n 25.0) (>= (exp wide_log_diff90_n) 8000000000.0)))
(assert (=> (>= wide_log_diff90_p 25.0) (>= (exp wide_log_diff90_p) 8000000000.0)))
(assert (=> (>= wide_log_tl50 25.0) (>= (exp wide_log_tl50) 8000000000.0)))
; --- Negated Safety Specification (.unsafe) ---
(assert (or (< Z0_tl50 45.0) (> Z0_tl50 55.0) (< Zdiff_diff90 90.0) (> Zdiff_diff90 110.0)))

(check-sat)
(exit)
