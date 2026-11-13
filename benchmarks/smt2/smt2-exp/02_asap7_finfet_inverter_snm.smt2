; ============================================================================
; Benchmark : Suite A-02: ASAP7 7nm Multi-Gate FinFET Inverter Static Noise Margin (Quantum Confinement + DIBL)
; PDK       : asap7 (7nm Multi-Gate FinFET (Clark et al. ASAP7 class: Lg=21nm, Tfin=6.5nm, Hfin=32nm, HfO2 EOT=1.0nm, quantum confinement + DIBL))
; Dialect   : smt2-exp (QF_NRA + transcendental exp)
; Generator : spice2smt (zero-dependency SPICE / Multi-PDK / PCB / TCAD compiler)
; ============================================================================
(set-logic ALL)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)

; --- Continuous Parameter / Defect / Litho Uncertainty Box ---
(declare-fun vdd () Real)
(assert (and (>= vdd 0.65) (<= vdd 0.75)))
(declare-fun vin_low () Real)
(assert (and (>= vin_low 0.0) (<= vin_low 0.14)))
(declare-fun dtfin_nm () Real)
(assert (and (>= dtfin_nm (- 0.45)) (<= dtfin_nm 0.45)))
(declare-fun dlg_nm () Real)
(assert (and (>= dlg_nm (- 1.0)) (<= dlg_nm 1.0)))
(declare-fun temp_k () Real)
(assert (and (>= temp_k 273.0) (<= temp_k 360.0)))

; --- State & Auxiliary Variables ---
; Node voltage v(vdd) [V]
(declare-fun v_vdd () Real)
(assert (and (>= v_vdd 0.65) (<= v_vdd 0.75)))
; Voltage source branch current (Vsup)
(declare-fun i_Vsup () Real)
; Node voltage v(in) [V]
(declare-fun v_in () Real)
(assert (and (>= v_in 0.0) (<= v_in 0.14)))
; Voltage source branch current (Vin)
(declare-fun i_Vin () Real)
; Node voltage v(out) [V]
(declare-fun v_out () Real)
(assert (and (>= v_out 0.0) (<= v_out 0.78)))
; Multi-gate natural scaling length lambda [nm] (Mp)
(declare-fun lam_Mp () Real)
; Softplus auxiliary y = ln(1 + exp(z)) for Mp_f
(declare-fun y_sp_Mp_f_1 () Real)
; Softplus auxiliary y = ln(1 + exp(z)) for Mp_r
(declare-fun y_sp_Mp_r_2 () Real)
; Transistor channel current (Mp)
(declare-fun i_Mp () Real)
; Multi-gate natural scaling length lambda [nm] (Mn)
(declare-fun lam_Mn () Real)
; Softplus auxiliary y = ln(1 + exp(z)) for Mn_f
(declare-fun y_sp_Mn_f_3 () Real)
; Softplus auxiliary y = ln(1 + exp(z)) for Mn_r
(declare-fun y_sp_Mn_r_4 () Real)
; Transistor channel current (Mn)
(declare-fun i_Mn () Real)

; --- Constitutive & Conservation Laws (MNA / PCB EM / TCAD) ---
; Voltage source constitutive equation (Vsup)
(assert (= v_vdd vdd))
; Voltage source constitutive equation (Vin)
(assert (= v_in vin_low))
; Positive device temperature
(assert (> temp_k 0.0))
; Positive thermal voltage
(assert (> (* 0.00008617333262 temp_k) 0.0))
; Positive body thickness
(assert (> (+ 6.5 dtfin_nm) 0.0))
; Positive gate length
(assert (> (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) 0.0))
; Nonnegative square root
(assert (>= lam_Mp 0.0))
; Algebraic sqrt constraint lam_Mp^2 = radicand (Multi-gate natural scaling length lambda [nm] (Mp))
(assert (= (* lam_Mp lam_Mp) (+ 6.5 dtfin_nm)))
; Softplus domain
(assert (>= y_sp_Mp_f_1 0.0))
; Pure-exp softplus link exp(y) = 1 + exp(z) (Mp_f)
(assert (= (exp y_sp_Mp_f_1) (+ 1.0 (exp (/ (* 0.85 (- (- v_vdd v_in) (- (+ (+ 0.28 (* (- 0.00085) (- temp_k 300.0))) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.4 (exp (- (/ (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) (* 2.0 lam_Mp))))) (- v_vdd v_out))))) (* 2.0 (* 0.00008617333262 temp_k)))))))
; Softplus domain
(assert (>= y_sp_Mp_r_2 0.0))
; Pure-exp softplus link exp(y) = 1 + exp(z) (Mp_r)
(assert (= (exp y_sp_Mp_r_2) (+ 1.0 (exp (/ (- (* 0.85 (- (- v_vdd v_in) (- (+ (+ 0.28 (* (- 0.00085) (- temp_k 300.0))) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.4 (exp (- (/ (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) (* 2.0 lam_Mp))))) (- v_vdd v_out))))) (- v_vdd v_out)) (* 2.0 (* 0.00008617333262 temp_k)))))))
; Transistor constitutive current (Mp, model ASAP7_PFET_RVT)
(assert (= i_Mp (- (/ (* (* 0.00000026 (* 2.0 (/ (+ 64.0 (+ 6.5 dtfin_nm)) (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001))))) (- (* y_sp_Mp_f_1 y_sp_Mp_f_1) (* y_sp_Mp_r_2 y_sp_Mp_r_2))) (+ 1.0 (* 0.1 y_sp_Mp_f_1))))))
; Positive device temperature
(assert (> temp_k 0.0))
; Positive thermal voltage
(assert (> (* 0.00008617333262 temp_k) 0.0))
; Positive body thickness
(assert (> (+ 6.5 dtfin_nm) 0.0))
; Positive gate length
(assert (> (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) 0.0))
; Nonnegative square root
(assert (>= lam_Mn 0.0))
; Algebraic sqrt constraint lam_Mn^2 = radicand (Multi-gate natural scaling length lambda [nm] (Mn))
(assert (= (* lam_Mn lam_Mn) (+ 6.5 dtfin_nm)))
; Softplus domain
(assert (>= y_sp_Mn_f_3 0.0))
; Pure-exp softplus link exp(y) = 1 + exp(z) (Mn_f)
(assert (= (exp y_sp_Mn_f_3) (+ 1.0 (exp (/ (* 0.86 (- v_in (- (+ (+ 0.27 (* (- 0.00085) (- temp_k 300.0))) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.2 (exp (- (/ (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) (* 2.0 lam_Mn))))) v_out)))) (* 2.0 (* 0.00008617333262 temp_k)))))))
; Softplus domain
(assert (>= y_sp_Mn_r_4 0.0))
; Pure-exp softplus link exp(y) = 1 + exp(z) (Mn_r)
(assert (= (exp y_sp_Mn_r_4) (+ 1.0 (exp (/ (- (* 0.86 (- v_in (- (+ (+ 0.27 (* (- 0.00085) (- temp_k 300.0))) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.2 (exp (- (/ (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) (* 2.0 lam_Mn))))) v_out)))) v_out) (* 2.0 (* 0.00008617333262 temp_k)))))))
; Transistor constitutive current (Mn, model ASAP7_NFET_RVT)
(assert (= i_Mn (/ (* (* 0.0000003 (* 2.0 (/ (+ 64.0 (+ 6.5 dtfin_nm)) (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001))))) (- (* y_sp_Mn_f_3 y_sp_Mn_f_3) (* y_sp_Mn_r_4 y_sp_Mn_r_4))) (+ 1.0 (* 0.1 y_sp_Mn_f_3)))))
; MNA Kirchhoff Current Law at node `in`
(assert (= i_Vin 0.0))
; MNA Kirchhoff Current Law at node `out`
(assert (= (+ i_Mp i_Mn) 0.0))
; MNA Kirchhoff Current Law at node `vdd`
(assert (= (- i_Vsup i_Mp) 0.0))

(assert (=> (>= (- (/ (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) (* 2.0 lam_Mn))) 25.0) (>= (exp (- (/ (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) (* 2.0 lam_Mn)))) 8000000000.0)))
(assert (=> (>= (- (/ (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) (* 2.0 lam_Mp))) 25.0) (>= (exp (- (/ (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) (* 2.0 lam_Mp)))) 8000000000.0)))
(assert (=> (>= (/ (* 0.85 (- (- v_vdd v_in) (- (+ (+ 0.28 (* (- 0.00085) (- temp_k 300.0))) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.4 (exp (- (/ (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) (* 2.0 lam_Mp))))) (- v_vdd v_out))))) (* 2.0 (* 0.00008617333262 temp_k))) 25.0) (>= (exp (/ (* 0.85 (- (- v_vdd v_in) (- (+ (+ 0.28 (* (- 0.00085) (- temp_k 300.0))) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.4 (exp (- (/ (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) (* 2.0 lam_Mp))))) (- v_vdd v_out))))) (* 2.0 (* 0.00008617333262 temp_k)))) 8000000000.0)))
(assert (=> (>= (/ (* 0.86 (- v_in (- (+ (+ 0.27 (* (- 0.00085) (- temp_k 300.0))) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.2 (exp (- (/ (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) (* 2.0 lam_Mn))))) v_out)))) (* 2.0 (* 0.00008617333262 temp_k))) 25.0) (>= (exp (/ (* 0.86 (- v_in (- (+ (+ 0.27 (* (- 0.00085) (- temp_k 300.0))) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.2 (exp (- (/ (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) (* 2.0 lam_Mn))))) v_out)))) (* 2.0 (* 0.00008617333262 temp_k)))) 8000000000.0)))
(assert (=> (>= (/ (- (* 0.85 (- (- v_vdd v_in) (- (+ (+ 0.28 (* (- 0.00085) (- temp_k 300.0))) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.4 (exp (- (/ (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) (* 2.0 lam_Mp))))) (- v_vdd v_out))))) (- v_vdd v_out)) (* 2.0 (* 0.00008617333262 temp_k))) 25.0) (>= (exp (/ (- (* 0.85 (- (- v_vdd v_in) (- (+ (+ 0.28 (* (- 0.00085) (- temp_k 300.0))) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.4 (exp (- (/ (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) (* 2.0 lam_Mp))))) (- v_vdd v_out))))) (- v_vdd v_out)) (* 2.0 (* 0.00008617333262 temp_k)))) 8000000000.0)))
(assert (=> (>= (/ (- (* 0.86 (- v_in (- (+ (+ 0.27 (* (- 0.00085) (- temp_k 300.0))) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.2 (exp (- (/ (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) (* 2.0 lam_Mn))))) v_out)))) v_out) (* 2.0 (* 0.00008617333262 temp_k))) 25.0) (>= (exp (/ (- (* 0.86 (- v_in (- (+ (+ 0.27 (* (- 0.00085) (- temp_k 300.0))) (* 0.8356225825687458 (- (/ 1.0 (* (+ 6.5 dtfin_nm) (+ 6.5 dtfin_nm))) 0.023668639053254437))) (* (* 3.2 (exp (- (/ (* 1000000000.0 (* (+ 21.0 dlg_nm) 0.000000001)) (* 2.0 lam_Mn))))) v_out)))) v_out) (* 2.0 (* 0.00008617333262 temp_k)))) 8000000000.0)))
(assert (=> (>= y_sp_Mn_f_3 25.0) (>= (exp y_sp_Mn_f_3) 8000000000.0)))
(assert (=> (>= y_sp_Mn_r_4 25.0) (>= (exp y_sp_Mn_r_4) 8000000000.0)))
(assert (=> (>= y_sp_Mp_f_1 25.0) (>= (exp y_sp_Mp_f_1) 8000000000.0)))
(assert (=> (>= y_sp_Mp_r_2 25.0) (>= (exp y_sp_Mp_r_2) 8000000000.0)))
; --- Negated Safety Specification (.unsafe) ---
(assert (< v_out 0.54))

(check-sat)
(exit)
