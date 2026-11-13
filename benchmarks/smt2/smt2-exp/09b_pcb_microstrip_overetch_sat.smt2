; ============================================================================
; Benchmark : Suite C-09b: Uncontrolled PCB Fab Over-Etch + Resin-Rich Prepreg Corner Violating Z0 Tolerance (SAT)
; Dialect   : smt2-exp (QF_NRA + transcendental exp)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :status sat)

; --- Continuous Parameter / Defect / Litho Uncertainty Box ---
(declare-fun dw_etch () Real)
(assert (and (>= dw_etch (- (/ 4.2 100000.0))) (<= dw_etch (/ 5.0 1000000.0))))
(declare-fun dh_lam () Real)
(assert (and (>= dh_lam (- (/ 1.2 100000.0))) (<= dh_lam (/ 1.8 100000.0))))
(declare-fun t_cu () Real)
(assert (and (>= t_cu (/ 2.8 100000.0)) (<= t_cu (/ 3.8 100000.0))))
(declare-fun er_lam () Real)
(assert (and (>= er_lam 3.85) (<= er_lam 4.5)))

; --- State & Auxiliary Variables ---
; Node voltage v(tx) [V]
(declare-fun v_tx () Real)
(assert (and (>= v_tx (- 0.5)) (<= v_tx 5.0)))
; Voltage source branch current (Vdrv)
(declare-fun i_Vdrv () Real)
(assert (and (>= i_Vdrv (- 50.0)) (<= i_Vdrv 50.0)))
; Node voltage v(rx) [V]
(declare-fun v_rx () Real)
(assert (and (>= v_rx (- 0.5)) (<= v_rx 5.0)))
; Hammerstad-Jensen sqrt(1 + 12/u) for tl50
(declare-fun su_tl50 () Real)
(assert (and (>= su_tl50 1.0) (<= su_tl50 20.0)))
; Effective microstrip permittivity e_eff (tl50)
(declare-fun eeff_tl50 () Real)
(assert (and (>= eeff_tl50 1.0) (<= eeff_tl50 15.0)))
; sqrt(e_eff) for tl50
(declare-fun seeff_tl50 () Real)
(assert (and (>= seeff_tl50 1.0) (<= seeff_tl50 4.0)))
; Wheeler-Hammerstad log geometry factor (tl50)
(declare-fun lnz_tl50 () Real)
(assert (and (>= lnz_tl50 0.05) (<= lnz_tl50 6.0)))
; Characteristic impedance Z0 [Ohm] (tl50)
(declare-fun Z0_tl50 () Real)
(assert (and (>= Z0_tl50 10.0) (<= Z0_tl50 200.0)))
; Total microstrip inductance [H] (tl50)
(declare-fun Ltot_tl50 () Real)
(assert (and (>= Ltot_tl50 (/ 1.0 10000000000000.0)) (<= Ltot_tl50 (/ 1.0 100000.0))))
; Total microstrip capacitance [F] (tl50)
(declare-fun Ctot_tl50 () Real)
(assert (and (>= Ctot_tl50 (/ 1.0 1000000000000000.0)) (<= Ctot_tl50 (/ 1.0 100000000.0))))
;  Copper trace DC resistance [Ohm] (tl50)
(declare-fun Rdc_tl50 () Real)
(assert (and (>= Rdc_tl50 (/ 1.0 100000.0)) (<= Rdc_tl50 100.0)))

; --- Constitutive & Conservation Laws (MNA / PCB EM / TCAD) ---
; Voltage source constitutive equation (Vdrv)
(assert (= v_tx 1.0))
; Algebraic sqrt constraint su_tl50^2 = radicand (Hammerstad-Jensen sqrt(1 + 12/u) for tl50)
(assert (= (* su_tl50 su_tl50) (+ 1.0 (/ 12.0 (/ (+ (+ (/ 1.8 10000.0) dw_etch) (* 0.48 t_cu)) (+ (/ 1.0 10000.0) dh_lam))))))
; Hammerstad-Jensen effective permittivity (tl50)
(assert (= eeff_tl50 (+ (/ (+ er_lam 1.0) 2.0) (/ (- er_lam 1.0) (* 2.0 su_tl50)))))
; Algebraic sqrt constraint seeff_tl50^2 = radicand (sqrt(e_eff) for tl50)
(assert (= (* seeff_tl50 seeff_tl50) eeff_tl50))
; Pure-exp logarithm constraint exp(lnz_tl50) = arg (Wheeler-Hammerstad log geometry factor (tl50))
(assert (= (exp lnz_tl50) (+ (/ 8.0 (/ (+ (+ (/ 1.8 10000.0) dw_etch) (* 0.48 t_cu)) (+ (/ 1.0 10000.0) dh_lam))) (/ (/ (+ (+ (/ 1.8 10000.0) dw_etch) (* 0.48 t_cu)) (+ (/ 1.0 10000.0) dh_lam)) 4.0))))
; Characteristic impedance Z0 * sqrt(e_eff) = 60 * ln(8/u + u/4) (tl50)
(assert (= (* Z0_tl50 seeff_tl50) (* 60.0 lnz_tl50)))
; Microstrip total inductance L_tot (tl50)
(assert (= Ltot_tl50 (/ (* 0.05 (* Z0_tl50 seeff_tl50)) 299792458.0)))
; Microstrip total capacitance C_tot (tl50)
(assert (= (* Ctot_tl50 Z0_tl50) (/ (* 0.05 seeff_tl50) 299792458.0)))
; Trapezoidal-etched copper DC resistance R_dc (tl50)
(assert (= (* Rdc_tl50 (* 58000000.0 (* (+ (/ 1.8 10000.0) dw_etch) t_cu))) 0.05))
; MNA Kirchhoff Current Law at node `rx`
(assert (= (+ (- (/ (- v_tx v_rx) Rdc_tl50)) (/ v_rx 50.0)) 0.0))
; MNA Kirchhoff Current Law at node `tx`
(assert (= (+ i_Vdrv (/ (- v_tx v_rx) Rdc_tl50)) 0.0))

; --- Negated Safety Specification (.unsafe) ---
(assert (> Z0_tl50 56.0))

(check-sat)
(exit)
