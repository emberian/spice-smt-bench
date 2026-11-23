import SpiceSmtBench.SlotReplay
import SpiceSmtBench.TargetsGenerated

namespace SpiceSmtBench.SlotLine
open LinearTransient Enclosed
noncomputable section

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

private def extended (x : Nat → Fin 16 → ℝ) (k i : Nat) := x k (Fin.ofNat 16 i)

/-- Lift the sampled trajectory at the selected material corner into every
geometry, box, integration and threshold clause of the generated proposition. -/
theorem fault_of_trajectory (x : Nat → Fin 16 → ℝ)
    (hi : ∀ i, x 0 i = 0)
    (safe : ∀ k, k ≤ 80 → ∀ i, -(1:ℝ) ≤ x k i ∧ x k i ≤ 1)
    (gnd : ∀ k, k ≤ 80 → ((-4)/5:ℝ) ≤ x k 4 ∧ x k 4 ≤ 4/5)
    (step : ∀ k i, x (k+1) i = x k i + ((flow i).eval (Fin.cases (drive k).val (x k)) +
      (flow i).eval (Fin.cases (drive (k+1)).val (x (k+1)))))
    (fault : (fraction 1 40).val < x 53 4) : Targets.Bench_12a_pcb_split_plane_slot_emi_sat realTF := by
  unfold Targets.Bench_12a_pcb_split_plane_slot_emi_sat
  refine ⟨er_p.val, er_n.val, slot_width.val, thickness_log_bus_p.val, su_bus_p.val, eeff_bus_p.val, seeff_bus_p.val, lnz_bus_p.val, Z0_bus_p.val, wide_log_bus_p.val, ?_⟩
  refine ⟨Ltot_bus_p.val, Ctot_bus_p.val, Rdc_bus_p.val, thickness_log_bus_n.val, su_bus_n.val, eeff_bus_n.val, seeff_bus_n.val, lnz_bus_n.val, Z0_bus_n.val, wide_log_bus_n.val, ?_⟩
  refine ⟨Ltot_bus_n.val, Ctot_bus_n.val, Rdc_bus_n.val, kc_bus.val, Zdiff_bus.val, odd_factor_bus.val, Cm_bus.val, Lm_bus.val, thickness_log_bus_p.val, su_bus_p.val, ?_⟩
  refine ⟨eeff_bus_p.val, seeff_bus_p.val, lnz_bus_p.val, Z0_bus_p.val, wide_log_bus_p.val, Ltot_bus_p.val, Ctot_bus_p.val, Rdc_bus_p.val, thickness_log_bus_n.val, su_bus_n.val, ?_⟩
  refine ⟨eeff_bus_n.val, seeff_bus_n.val, lnz_bus_n.val, Z0_bus_n.val, wide_log_bus_n.val, Ltot_bus_n.val, Ctot_bus_n.val, Rdc_bus_n.val, kc_bus.val, Zdiff_bus.val, ?_⟩
  refine ⟨odd_factor_bus.val, Cm_bus.val, Lm_bus.val, thickness_log_bus_p.val, su_bus_p.val, eeff_bus_p.val, seeff_bus_p.val, lnz_bus_p.val, Z0_bus_p.val, wide_log_bus_p.val, ?_⟩
  refine ⟨Ltot_bus_p.val, Ctot_bus_p.val, Rdc_bus_p.val, thickness_log_bus_n.val, su_bus_n.val, eeff_bus_n.val, seeff_bus_n.val, lnz_bus_n.val, Z0_bus_n.val, wide_log_bus_n.val, ?_⟩
  refine ⟨Ltot_bus_n.val, Ctot_bus_n.val, Rdc_bus_n.val, kc_bus.val, Zdiff_bus.val, odd_factor_bus.val, Cm_bus.val, Lm_bus.val, extended x, ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · norm_num [er_p,Enclosed.fraction,realTF]
  · norm_num [er_n,Enclosed.fraction,realTF]
  · norm_num [slot_width,Enclosed.fraction,realTF]
  · intro k hk
    repeat' apply And.intro
    · exact le_trans (by norm_num [realTF]) (safe k hk 0).1
    · exact le_trans (safe k hk 0).2 (by norm_num [realTF])
    · exact le_trans (by norm_num [realTF]) (safe k hk 1).1
    · exact le_trans (safe k hk 1).2 (by norm_num [realTF])
    · exact le_trans (by norm_num [realTF]) (safe k hk 2).1
    · exact le_trans (safe k hk 2).2 (by norm_num [realTF])
    · exact le_trans (by norm_num [realTF]) (safe k hk 3).1
    · exact le_trans (safe k hk 3).2 (by norm_num [realTF])
    · simpa [realTF,extended] using (gnd k hk).1
    · exact (gnd k hk).2
    · exact le_trans (by norm_num [realTF]) (safe k hk 5).1
    · exact le_trans (safe k hk 5).2 (by norm_num [realTF])
    · exact le_trans (by norm_num [realTF]) (safe k hk 6).1
    · exact le_trans (safe k hk 6).2 (by norm_num [realTF])
    · exact le_trans (by norm_num [realTF]) (safe k hk 7).1
    · exact le_trans (safe k hk 7).2 (by norm_num [realTF])
    · exact le_trans (by norm_num [realTF]) (safe k hk 8).1
    · exact le_trans (safe k hk 8).2 (by norm_num [realTF])
    · exact le_trans (by norm_num [realTF]) (safe k hk 9).1
    · exact le_trans (safe k hk 9).2 (by norm_num [realTF])
    · exact le_trans (by norm_num [realTF]) (safe k hk 10).1
    · exact le_trans (safe k hk 10).2 (by norm_num [realTF])
    · exact le_trans (by norm_num [realTF]) (safe k hk 11).1
    · exact le_trans (safe k hk 11).2 (by norm_num [realTF])
    · exact le_trans (by norm_num [realTF]) (safe k hk 12).1
    · exact le_trans (safe k hk 12).2 (by norm_num [realTF])
    · exact le_trans (by norm_num [realTF]) (safe k hk 13).1
    · exact le_trans (safe k hk 13).2 (by norm_num [realTF])
    · exact le_trans (by norm_num [realTF]) (safe k hk 14).1
    · exact le_trans (safe k hk 14).2 (by norm_num [realTF])
    · exact le_trans (by norm_num [realTF]) (safe k hk 15).1
    · exact le_trans (safe k hk 15).2 (by norm_num [realTF])
  · have dynamics (k : Nat) (i : Fin 16) :
        x (k+1) i = x k i + (fraction 1 200000000000).val *
        ((rates i).eval (Fin.cases (drive k).val (x k)) +
         (rates i).eval (Fin.cases (drive (k+1)).val (x (k+1)))) := by
      rw [mul_add]; exact step k i
    repeat' apply And.intro
    all_goals first
      | exact hi _
      | rfl
      | exact thickness_log_bus_p_law
      | exact su_bus_p_law
      | exact seeff_bus_p_law
      | exact lnz_bus_p_law
      | exact wide_log_bus_p_law
      | exact Ctot_bus_p_law
      | exact Rdc_bus_p_law
      | exact seeff_bus_n_law
      | exact Ctot_bus_n_law
      | exact odd_factor_bus_law
      | exact Real.sqrt_nonneg _
      | (intro k _; repeat' apply And.intro
         · exact dynamics k 0
         · exact dynamics k 1
         · exact dynamics k 2
         · exact dynamics k 3
         · exact dynamics k 4
         · exact dynamics k 5
         · exact dynamics k 6
         · exact dynamics k 7
         · exact dynamics k 8
         · exact dynamics k 9
         · exact dynamics k 10
         · exact dynamics k 11
         · exact dynamics k 12
         · exact dynamics k 13
         · exact dynamics k 14
         · exact dynamics k 15)
      | norm_num [realTF]
  · exact ⟨53, by decide, Or.inl fault⟩

/-- At 530 ps the receiver reference rises by at least 70 mV. -/
theorem certified : Targets.Bench_12a_pcb_split_plane_slot_emi_sat realTF := by
  obtain ⟨P,hP,law⟩ := transfer_exists
  let x := trajectory P drive
  have mem (k : Nat) (hk : k ≤ 80) (i : Fin 16) :
      TransientWindows.holds (stateBox k i) (x k i).val :=
    TransientWindows.boxes_sound P drive coefficientBox driveBox hP k
      (fun j hj => TransientWindows.holds_of_fits (drive_verified ⟨j,by omega⟩)) i
  apply fault_of_trajectory (fun k i => (x k i).val)
  · intro i; simp [x,trajectory]
  · intro k hk i
    obtain ⟨l,h⟩ := (state_verified ⟨k,by omega⟩ i).1
    obtain ⟨lo,hi⟩ := mem k hk i
    dsimp only [Fin.val_mk] at l h
    have L : (-900000000000000000:ℝ) ≤ (stateBox k i).lo := by exact_mod_cast l
    have H : ((stateBox k i).hi:ℝ) ≤ 900000000000000000 := by exact_mod_cast h
    norm_num [TransientWindows.scale] at lo hi
    constructor <;> linarith
  · intro k hk
    obtain ⟨l,h⟩ := (state_verified ⟨k,by omega⟩ 4).2 rfl
    obtain ⟨lo,hi⟩ := mem k hk 4
    dsimp only [Fin.val_mk] at l h
    have L : (-100000000000000000:ℝ) ≤ (stateBox k 4).lo := by exact_mod_cast l
    have H : ((stateBox k 4).hi:ℝ) ≤ 100000000000000000 := by exact_mod_cast h
    norm_num [TransientWindows.scale] at lo hi
    constructor <;> linarith
  · exact balance flow P drive law
  · have L : (70000000000000000:ℝ) ≤ (stateBox 53 4).lo := by exact_mod_cast threshold_verified
    have lo := (mem 53 (by decide) 4).1
    norm_num [TransientWindows.scale,Enclosed.fraction] at lo ⊢
    linarith
end
end SpiceSmtBench.SlotLine
