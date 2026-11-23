import SpiceSmtBench.RingEnvelope

namespace SpiceSmtBench.RingEnvelope

open LeanCert.Core
set_option Elab.async false
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000

-- These four-dimensional cells enclose stage voltage, successor, predecessor,
-- and supply. Separate reductions bound the memory needed for replay.

private def boxL := Function.update whole (0 : Fin 4) ((whole 0).bisect.1)

private def boxLL := Function.update boxL (0 : Fin 4) ((boxL 0).bisect.1)

private def boxLLL := Function.update boxLL (0 : Fin 4) ((boxLL 0).bisect.1)

private def boxLLLL := Function.update boxLLL (0 : Fin 4) ((boxLLL 0).bisect.1)

private theorem cellLLLL : check boxLLLL .leaf := by decide +kernel

private def boxLLLR := Function.update boxLLL (0 : Fin 4) ((boxLLL 0).bisect.2)

private def boxLLLRL := Function.update boxLLLR (0 : Fin 4) ((boxLLLR 0).bisect.1)

private theorem cellLLLRL : check boxLLLRL (.split 2 .leaf .leaf) := by decide +kernel

private def boxLLLRR := Function.update boxLLLR (0 : Fin 4) ((boxLLLR 0).bisect.2)

private def boxLLLRRL := Function.update boxLLLRR (2 : Fin 4) ((boxLLLRR 2).bisect.1)

private def boxLLLRRLL := Function.update boxLLLRRL (1 : Fin 4) ((boxLLLRRL 1).bisect.1)

private theorem cellLLLRRLL : check boxLLLRRLL (.split 2 .leaf .leaf) := by decide +kernel

private def boxLLLRRLR := Function.update boxLLLRRL (1 : Fin 4) ((boxLLLRRL 1).bisect.2)

private def boxLLLRRLRL := Function.update boxLLLRRLR (2 : Fin 4) ((boxLLLRRLR 2).bisect.1)

private theorem cellLLLRRLRL : check boxLLLRRLRL .leaf := by decide +kernel

private def boxLLLRRLRR := Function.update boxLLLRRLR (2 : Fin 4) ((boxLLLRRLR 2).bisect.2)

private def boxLLLRRLRRL := Function.update boxLLLRRLRR (1 : Fin 4) ((boxLLLRRLRR 1).bisect.1)

private theorem cellLLLRRLRRL : check boxLLLRRLRRL (.split 2 .leaf (.split 2 .leaf (.split 2 .leaf .leaf))) := by decide +kernel

private def boxLLLRRLRRR := Function.update boxLLLRRLRR (1 : Fin 4) ((boxLLLRRLRR 1).bisect.2)

private def boxLLLRRLRRRL := Function.update boxLLLRRLRRR (2 : Fin 4) ((boxLLLRRLRRR 2).bisect.1)

private theorem cellLLLRRLRRRL : check boxLLLRRLRRRL (.split 1 .leaf .leaf) := by decide +kernel

private def boxLLLRRLRRRR := Function.update boxLLLRRLRRR (2 : Fin 4) ((boxLLLRRLRRR 2).bisect.2)

private def boxLLLRRLRRRRL := Function.update boxLLLRRLRRRR (2 : Fin 4) ((boxLLLRRLRRRR 2).bisect.1)

private def boxLLLRRLRRRRLL := Function.update boxLLLRRLRRRRL (1 : Fin 4) ((boxLLLRRLRRRRL 1).bisect.1)

private theorem cellLLLRRLRRRRLL : check boxLLLRRLRRRRLL (.split 2 .leaf .leaf) := by decide +kernel

private def boxLLLRRLRRRRLR := Function.update boxLLLRRLRRRRL (1 : Fin 4) ((boxLLLRRLRRRRL 1).bisect.2)

private def boxLLLRRLRRRRLRL := Function.update boxLLLRRLRRRRLR (2 : Fin 4) ((boxLLLRRLRRRRLR 2).bisect.1)

private theorem cellLLLRRLRRRRLRL : check boxLLLRRLRRRRLRL (.split 2 .leaf (.split 3 .leaf .leaf)) := by decide +kernel

private def boxLLLRRLRRRRLRR := Function.update boxLLLRRLRRRRLR (2 : Fin 4) ((boxLLLRRLRRRRLR 2).bisect.2)

private def boxLLLRRLRRRRLRRL := Function.update boxLLLRRLRRRRLRR (3 : Fin 4) ((boxLLLRRLRRRRLRR 3).bisect.1)

private def boxLLLRRLRRRRLRRLL := Function.update boxLLLRRLRRRRLRRL (1 : Fin 4) ((boxLLLRRLRRRRLRRL 1).bisect.1)

private theorem cellLLLRRLRRRRLRRLL : check boxLLLRRLRRRRLRRLL (.split 2 .leaf .leaf) := by decide +kernel

private def boxLLLRRLRRRRLRRLR := Function.update boxLLLRRLRRRRLRRL (1 : Fin 4) ((boxLLLRRLRRRRLRRL 1).bisect.2)

private def boxLLLRRLRRRRLRRLRL := Function.update boxLLLRRLRRRRLRRLR (2 : Fin 4) ((boxLLLRRLRRRRLRRLR 2).bisect.1)

private theorem cellLLLRRLRRRRLRRLRL : check boxLLLRRLRRRRLRRLRL (.split 3 (.split 1 .leaf .leaf) .leaf) := by decide +kernel

private def boxLLLRRLRRRRLRRLRR := Function.update boxLLLRRLRRRRLRRLR (2 : Fin 4) ((boxLLLRRLRRRRLRRLR 2).bisect.2)

private theorem cellLLLRRLRRRRLRRLRR : check boxLLLRRLRRRRLRRLRR (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf) := by decide +kernel

private theorem cellLLLRRLRRRRLRRLR : check boxLLLRRLRRRRLRRLR (.split 2 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRLRRLRL,cellLLLRRLRRRRLRRLRR⟩

private theorem cellLLLRRLRRRRLRRL : check boxLLLRRLRRRRLRRL (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRLRRLL,cellLLLRRLRRRRLRRLR⟩

private def boxLLLRRLRRRRLRRR := Function.update boxLLLRRLRRRRLRR (3 : Fin 4) ((boxLLLRRLRRRRLRR 3).bisect.2)

private theorem cellLLLRRLRRRRLRRR : check boxLLLRRLRRRRLRRR .leaf := by decide +kernel

private theorem cellLLLRRLRRRRLRR : check boxLLLRRLRRRRLRR (.split 3 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRLRRL,cellLLLRRLRRRRLRRR⟩

private theorem cellLLLRRLRRRRLR : check boxLLLRRLRRRRLR (.split 2 (.split 2 .leaf (.split 3 .leaf .leaf)) (.split 3 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRLRL,cellLLLRRLRRRRLRR⟩

private theorem cellLLLRRLRRRRL : check boxLLLRRLRRRRL (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 3 .leaf .leaf)) (.split 3 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRLL,cellLLLRRLRRRRLR⟩

private def boxLLLRRLRRRRR := Function.update boxLLLRRLRRRR (2 : Fin 4) ((boxLLLRRLRRRR 2).bisect.2)

private def boxLLLRRLRRRRRL := Function.update boxLLLRRLRRRRR (1 : Fin 4) ((boxLLLRRLRRRRR 1).bisect.1)

private def boxLLLRRLRRRRRLL := Function.update boxLLLRRLRRRRRL (2 : Fin 4) ((boxLLLRRLRRRRRL 2).bisect.1)

private theorem cellLLLRRLRRRRRLL : check boxLLLRRLRRRRRLL (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf)) := by decide +kernel

private def boxLLLRRLRRRRRLR := Function.update boxLLLRRLRRRRRL (2 : Fin 4) ((boxLLLRRLRRRRRL 2).bisect.2)

private theorem cellLLLRRLRRRRRLR : check boxLLLRRLRRRRRLR (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf (.split 3 .leaf .leaf))) := by decide +kernel

private theorem cellLLLRRLRRRRRL : check boxLLLRRLRRRRRL (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf (.split 3 .leaf .leaf)))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRLL,cellLLLRRLRRRRRLR⟩

private def boxLLLRRLRRRRRR := Function.update boxLLLRRLRRRRR (1 : Fin 4) ((boxLLLRRLRRRRR 1).bisect.2)

private def boxLLLRRLRRRRRRL := Function.update boxLLLRRLRRRRRR (2 : Fin 4) ((boxLLLRRLRRRRRR 2).bisect.1)

private def boxLLLRRLRRRRRRLL := Function.update boxLLLRRLRRRRRRL (3 : Fin 4) ((boxLLLRRLRRRRRRL 3).bisect.1)

private def boxLLLRRLRRRRRRLLL := Function.update boxLLLRRLRRRRRRLL (1 : Fin 4) ((boxLLLRRLRRRRRRLL 1).bisect.1)

private theorem cellLLLRRLRRRRRRLLL : check boxLLLRRLRRRRRRLLL (.split 2 (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf) (.split 0 .leaf .leaf)) := by decide +kernel

private def boxLLLRRLRRRRRRLLR := Function.update boxLLLRRLRRRRRRLL (1 : Fin 4) ((boxLLLRRLRRRRRRLL 1).bisect.2)

private def boxLLLRRLRRRRRRLLRL := Function.update boxLLLRRLRRRRRRLLR (2 : Fin 4) ((boxLLLRRLRRRRRRLLR 2).bisect.1)

private def boxLLLRRLRRRRRRLLRLL := Function.update boxLLLRRLRRRRRRLLRL (0 : Fin 4) ((boxLLLRRLRRRRRRLLRL 0).bisect.1)

private theorem cellLLLRRLRRRRRRLLRLL : check boxLLLRRLRRRRRRLLRLL (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) := by decide +kernel

private def boxLLLRRLRRRRRRLLRLR := Function.update boxLLLRRLRRRRRRLLRL (0 : Fin 4) ((boxLLLRRLRRRRRRLLRL 0).bisect.2)

private def boxLLLRRLRRRRRRLLRLRL := Function.update boxLLLRRLRRRRRRLLRLR (3 : Fin 4) ((boxLLLRRLRRRRRRLLRLR 3).bisect.1)

private def boxLLLRRLRRRRRRLLRLRLL := Function.update boxLLLRRLRRRRRRLLRLRL (1 : Fin 4) ((boxLLLRRLRRRRRRLLRLRL 1).bisect.1)

private theorem cellLLLRRLRRRRRRLLRLRLL : check boxLLLRRLRRRRRRLLRLRLL (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) := by decide +kernel

private def boxLLLRRLRRRRRRLLRLRLR := Function.update boxLLLRRLRRRRRRLLRLRL (1 : Fin 4) ((boxLLLRRLRRRRRRLLRLRL 1).bisect.2)

private theorem cellLLLRRLRRRRRRLLRLRLR : check boxLLLRRLRRRRRRLLRLRLR (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf)) := by decide +kernel

private theorem cellLLLRRLRRRRRRLLRLRL : check boxLLLRRLRRRRRRLLRLRL (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRLLRLRLL,cellLLLRRLRRRRRRLLRLRLR⟩

private def boxLLLRRLRRRRRRLLRLRR := Function.update boxLLLRRLRRRRRRLLRLR (3 : Fin 4) ((boxLLLRRLRRRRRRLLRLR 3).bisect.2)

private theorem cellLLLRRLRRRRRRLLRLRR : check boxLLLRRLRRRRRRLLRLRR (.split 2 .leaf .leaf) := by decide +kernel

private theorem cellLLLRRLRRRRRRLLRLR : check boxLLLRRLRRRRRRLLRLR (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRLLRLRL,cellLLLRRLRRRRRRLLRLRR⟩

private theorem cellLLLRRLRRRRRRLLRL : check boxLLLRRLRRRRRRLLRL (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRLLRLL,cellLLLRRLRRRRRRLLRLR⟩

private def boxLLLRRLRRRRRRLLRR := Function.update boxLLLRRLRRRRRRLLR (2 : Fin 4) ((boxLLLRRLRRRRRRLLR 2).bisect.2)

private def boxLLLRRLRRRRRRLLRRL := Function.update boxLLLRRLRRRRRRLLRR (0 : Fin 4) ((boxLLLRRLRRRRRRLLRR 0).bisect.1)

private theorem cellLLLRRLRRRRRRLLRRL : check boxLLLRRLRRRRRRLLRRL (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) := by decide +kernel

private def boxLLLRRLRRRRRRLLRRR := Function.update boxLLLRRLRRRRRRLLRR (0 : Fin 4) ((boxLLLRRLRRRRRRLLRR 0).bisect.2)

private theorem cellLLLRRLRRRRRRLLRRR : check boxLLLRRLRRRRRRLLRRR (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) := by decide +kernel

private theorem cellLLLRRLRRRRRRLLRR : check boxLLLRRLRRRRRRLLRR (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRLLRRL,cellLLLRRLRRRRRRLLRRR⟩

private theorem cellLLLRRLRRRRRRLLR : check boxLLLRRLRRRRRRLLR (.split 2 (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRLLRL,cellLLLRRLRRRRRRLLRR⟩

private theorem cellLLLRRLRRRRRRLL : check boxLLLRRLRRRRRRLL (.split 1 (.split 2 (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf)))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRLLL,cellLLLRRLRRRRRRLLR⟩

private def boxLLLRRLRRRRRRLR := Function.update boxLLLRRLRRRRRRL (3 : Fin 4) ((boxLLLRRLRRRRRRL 3).bisect.2)

private theorem cellLLLRRLRRRRRRLR : check boxLLLRRLRRRRRRLR (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf)) := by decide +kernel

private theorem cellLLLRRLRRRRRRL : check boxLLLRRLRRRRRRL (.split 3 (.split 1 (.split 2 (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf)))) (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRLL,cellLLLRRLRRRRRRLR⟩

private def boxLLLRRLRRRRRRR := Function.update boxLLLRRLRRRRRR (2 : Fin 4) ((boxLLLRRLRRRRRR 2).bisect.2)

private def boxLLLRRLRRRRRRRL := Function.update boxLLLRRLRRRRRRR (3 : Fin 4) ((boxLLLRRLRRRRRRR 3).bisect.1)

private def boxLLLRRLRRRRRRRLL := Function.update boxLLLRRLRRRRRRRL (1 : Fin 4) ((boxLLLRRLRRRRRRRL 1).bisect.1)

private def boxLLLRRLRRRRRRRLLL := Function.update boxLLLRRLRRRRRRRLL (0 : Fin 4) ((boxLLLRRLRRRRRRRLL 0).bisect.1)

private theorem cellLLLRRLRRRRRRRLLL : check boxLLLRRLRRRRRRRLLL (.split 2 .leaf .leaf) := by decide +kernel

private def boxLLLRRLRRRRRRRLLR := Function.update boxLLLRRLRRRRRRRLL (0 : Fin 4) ((boxLLLRRLRRRRRRRLL 0).bisect.2)

private def boxLLLRRLRRRRRRRLLRL := Function.update boxLLLRRLRRRRRRRLLR (2 : Fin 4) ((boxLLLRRLRRRRRRRLLR 2).bisect.1)

private theorem cellLLLRRLRRRRRRRLLRL : check boxLLLRRLRRRRRRRLLRL (.split 2 .leaf .leaf) := by decide +kernel

private def boxLLLRRLRRRRRRRLLRR := Function.update boxLLLRRLRRRRRRRLLR (2 : Fin 4) ((boxLLLRRLRRRRRRRLLR 2).bisect.2)

private theorem cellLLLRRLRRRRRRRLLRR : check boxLLLRRLRRRRRRRLLRR (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) := by decide +kernel

private theorem cellLLLRRLRRRRRRRLLR : check boxLLLRRLRRRRRRRLLR (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRLLRL,cellLLLRRLRRRRRRRLLRR⟩

private theorem cellLLLRRLRRRRRRRLL : check boxLLLRRLRRRRRRRLL (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRLLL,cellLLLRRLRRRRRRRLLR⟩

private def boxLLLRRLRRRRRRRLR := Function.update boxLLLRRLRRRRRRRL (1 : Fin 4) ((boxLLLRRLRRRRRRRL 1).bisect.2)

private def boxLLLRRLRRRRRRRLRL := Function.update boxLLLRRLRRRRRRRLR (0 : Fin 4) ((boxLLLRRLRRRRRRRLR 0).bisect.1)

private def boxLLLRRLRRRRRRRLRLL := Function.update boxLLLRRLRRRRRRRLRL (2 : Fin 4) ((boxLLLRRLRRRRRRRLRL 2).bisect.1)

private theorem cellLLLRRLRRRRRRRLRLL : check boxLLLRRLRRRRRRRLRLL (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) := by decide +kernel

private def boxLLLRRLRRRRRRRLRLR := Function.update boxLLLRRLRRRRRRRLRL (2 : Fin 4) ((boxLLLRRLRRRRRRRLRL 2).bisect.2)

private def boxLLLRRLRRRRRRRLRLRL := Function.update boxLLLRRLRRRRRRRLRLR (3 : Fin 4) ((boxLLLRRLRRRRRRRLRLR 3).bisect.1)

private theorem cellLLLRRLRRRRRRRLRLRL : check boxLLLRRLRRRRRRRLRLRL (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) := by decide +kernel

private def boxLLLRRLRRRRRRRLRLRR := Function.update boxLLLRRLRRRRRRRLRLR (3 : Fin 4) ((boxLLLRRLRRRRRRRLRLR 3).bisect.2)

private theorem cellLLLRRLRRRRRRRLRLRR : check boxLLLRRLRRRRRRRLRLRR .leaf := by decide +kernel

private theorem cellLLLRRLRRRRRRRLRLR : check boxLLLRRLRRRRRRRLRLR (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRLRLRL,cellLLLRRLRRRRRRRLRLRR⟩

private theorem cellLLLRRLRRRRRRRLRL : check boxLLLRRLRRRRRRRLRL (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRLRLL,cellLLLRRLRRRRRRRLRLR⟩

private def boxLLLRRLRRRRRRRLRR := Function.update boxLLLRRLRRRRRRRLR (0 : Fin 4) ((boxLLLRRLRRRRRRRLR 0).bisect.2)

private def boxLLLRRLRRRRRRRLRRL := Function.update boxLLLRRLRRRRRRRLRR (2 : Fin 4) ((boxLLLRRLRRRRRRRLRR 2).bisect.1)

private def boxLLLRRLRRRRRRRLRRLL := Function.update boxLLLRRLRRRRRRRLRRL (3 : Fin 4) ((boxLLLRRLRRRRRRRLRRL 3).bisect.1)

private def boxLLLRRLRRRRRRRLRRLLL := Function.update boxLLLRRLRRRRRRRLRRLL (1 : Fin 4) ((boxLLLRRLRRRRRRRLRRLL 1).bisect.1)

private theorem cellLLLRRLRRRRRRRLRRLLL : check boxLLLRRLRRRRRRRLRRLLL (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) := by decide +kernel

private def boxLLLRRLRRRRRRRLRRLLR := Function.update boxLLLRRLRRRRRRRLRRLL (1 : Fin 4) ((boxLLLRRLRRRRRRRLRRLL 1).bisect.2)

private theorem cellLLLRRLRRRRRRRLRRLLR : check boxLLLRRLRRRRRRRLRRLLR (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf) := by decide +kernel

private theorem cellLLLRRLRRRRRRRLRRLL : check boxLLLRRLRRRRRRRLRRLL (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRLRRLLL,cellLLLRRLRRRRRRRLRRLLR⟩

private def boxLLLRRLRRRRRRRLRRLR := Function.update boxLLLRRLRRRRRRRLRRL (3 : Fin 4) ((boxLLLRRLRRRRRRRLRRL 3).bisect.2)

private theorem cellLLLRRLRRRRRRRLRRLR : check boxLLLRRLRRRRRRRLRRLR (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf))) := by decide +kernel

private theorem cellLLLRRLRRRRRRRLRRL : check boxLLLRRLRRRRRRRLRRL (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRLRRLL,cellLLLRRLRRRRRRRLRRLR⟩

private def boxLLLRRLRRRRRRRLRRR := Function.update boxLLLRRLRRRRRRRLRR (2 : Fin 4) ((boxLLLRRLRRRRRRRLRR 2).bisect.2)

private def boxLLLRRLRRRRRRRLRRRL := Function.update boxLLLRRLRRRRRRRLRRR (3 : Fin 4) ((boxLLLRRLRRRRRRRLRRR 3).bisect.1)

private def boxLLLRRLRRRRRRRLRRRLL := Function.update boxLLLRRLRRRRRRRLRRRL (0 : Fin 4) ((boxLLLRRLRRRRRRRLRRRL 0).bisect.1)

private def boxLLLRRLRRRRRRRLRRRLLL := Function.update boxLLLRRLRRRRRRRLRRRLL (1 : Fin 4) ((boxLLLRRLRRRRRRRLRRRLL 1).bisect.1)

private theorem cellLLLRRLRRRRRRRLRRRLLL : check boxLLLRRLRRRRRRRLRRRLLL (.split 2 .leaf .leaf) := by decide +kernel

private def boxLLLRRLRRRRRRRLRRRLLR := Function.update boxLLLRRLRRRRRRRLRRRLL (1 : Fin 4) ((boxLLLRRLRRRRRRRLRRRLL 1).bisect.2)

private def boxLLLRRLRRRRRRRLRRRLLRL := Function.update boxLLLRRLRRRRRRRLRRRLLR (2 : Fin 4) ((boxLLLRRLRRRRRRRLRRRLLR 2).bisect.1)

private theorem cellLLLRRLRRRRRRRLRRRLLRL : check boxLLLRRLRRRRRRRLRRRLLRL (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) := by decide +kernel

private def boxLLLRRLRRRRRRRLRRRLLRR := Function.update boxLLLRRLRRRRRRRLRRRLLR (2 : Fin 4) ((boxLLLRRLRRRRRRRLRRRLLR 2).bisect.2)

private def boxLLLRRLRRRRRRRLRRRLLRRL := Function.update boxLLLRRLRRRRRRRLRRRLLRR (3 : Fin 4) ((boxLLLRRLRRRRRRRLRRRLLRR 3).bisect.1)

private def boxLLLRRLRRRRRRRLRRRLLRRLL := Function.update boxLLLRRLRRRRRRRLRRRLLRRL (2 : Fin 4) ((boxLLLRRLRRRRRRRLRRRLLRRL 2).bisect.1)

private theorem cellLLLRRLRRRRRRRLRRRLLRRLL : check boxLLLRRLRRRRRRRLRRRLLRRLL (.split 1 .leaf (.split 1 .leaf .leaf)) := by decide +kernel

private def boxLLLRRLRRRRRRRLRRRLLRRLR := Function.update boxLLLRRLRRRRRRRLRRRLLRRL (2 : Fin 4) ((boxLLLRRLRRRRRRRLRRRLLRRL 2).bisect.2)

private theorem cellLLLRRLRRRRRRRLRRRLLRRLR : check boxLLLRRLRRRRRRRLRRRLLRRLR (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf))) := by decide +kernel

private theorem cellLLLRRLRRRRRRRLRRRLLRRL : check boxLLLRRLRRRRRRRLRRRLLRRL (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRLRRRLLRRLL,cellLLLRRLRRRRRRRLRRRLLRRLR⟩

private def boxLLLRRLRRRRRRRLRRRLLRRR := Function.update boxLLLRRLRRRRRRRLRRRLLRR (3 : Fin 4) ((boxLLLRRLRRRRRRRLRRRLLRR 3).bisect.2)

private theorem cellLLLRRLRRRRRRRLRRRLLRRR : check boxLLLRRLRRRRRRRLRRRLLRRR .leaf := by decide +kernel

private theorem cellLLLRRLRRRRRRRLRRRLLRR : check boxLLLRRLRRRRRRRLRRRLLRR (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRLRRRLLRRL,cellLLLRRLRRRRRRRLRRRLLRRR⟩

private theorem cellLLLRRLRRRRRRRLRRRLLR : check boxLLLRRLRRRRRRRLRRRLLR (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRLRRRLLRL,cellLLLRRLRRRRRRRLRRRLLRR⟩

private theorem cellLLLRRLRRRRRRRLRRRLL : check boxLLLRRLRRRRRRRLRRRLL (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRLRRRLLL,cellLLLRRLRRRRRRRLRRRLLR⟩

private def boxLLLRRLRRRRRRRLRRRLR := Function.update boxLLLRRLRRRRRRRLRRRL (0 : Fin 4) ((boxLLLRRLRRRRRRRLRRRL 0).bisect.2)

private theorem cellLLLRRLRRRRRRRLRRRLR : check boxLLLRRLRRRRRRRLRRRLR .leaf := by decide +kernel

private theorem cellLLLRRLRRRRRRRLRRRL : check boxLLLRRLRRRRRRRLRRRL (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRLRRRLL,cellLLLRRLRRRRRRRLRRRLR⟩

private def boxLLLRRLRRRRRRRLRRRR := Function.update boxLLLRRLRRRRRRRLRRR (3 : Fin 4) ((boxLLLRRLRRRRRRRLRRR 3).bisect.2)

private theorem cellLLLRRLRRRRRRRLRRRR : check boxLLLRRLRRRRRRRLRRRR (.split 0 (.split 1 .leaf .leaf) .leaf) := by decide +kernel

private theorem cellLLLRRLRRRRRRRLRRR : check boxLLLRRLRRRRRRRLRRR (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRLRRRL,cellLLLRRLRRRRRRRLRRRR⟩

private theorem cellLLLRRLRRRRRRRLRR : check boxLLLRRLRRRRRRRLRR (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRLRRL,cellLLLRRLRRRRRRRLRRR⟩

private theorem cellLLLRRLRRRRRRRLR : check boxLLLRRLRRRRRRRLR (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRLRL,cellLLLRRLRRRRRRRLRR⟩

private theorem cellLLLRRLRRRRRRRL : check boxLLLRRLRRRRRRRL (.split 1 (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRLL,cellLLLRRLRRRRRRRLR⟩

private def boxLLLRRLRRRRRRRR := Function.update boxLLLRRLRRRRRRR (3 : Fin 4) ((boxLLLRRLRRRRRRR 3).bisect.2)

private def boxLLLRRLRRRRRRRRL := Function.update boxLLLRRLRRRRRRRR (1 : Fin 4) ((boxLLLRRLRRRRRRRR 1).bisect.1)

private theorem cellLLLRRLRRRRRRRRL : check boxLLLRRLRRRRRRRRL (.split 2 .leaf .leaf) := by decide +kernel

private def boxLLLRRLRRRRRRRRR := Function.update boxLLLRRLRRRRRRRR (1 : Fin 4) ((boxLLLRRLRRRRRRRR 1).bisect.2)

private theorem cellLLLRRLRRRRRRRRR : check boxLLLRRLRRRRRRRRR (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 0 .leaf (.split 2 .leaf .leaf))) := by decide +kernel

private theorem cellLLLRRLRRRRRRRR : check boxLLLRRLRRRRRRRR (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 0 .leaf (.split 2 .leaf .leaf)))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRRL,cellLLLRRLRRRRRRRRR⟩

private theorem cellLLLRRLRRRRRRR : check boxLLLRRLRRRRRRR (.split 3 (.split 1 (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 0 .leaf (.split 2 .leaf .leaf))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRRL,cellLLLRRLRRRRRRRR⟩

private theorem cellLLLRRLRRRRRR : check boxLLLRRLRRRRRR (.split 2 (.split 3 (.split 1 (.split 2 (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf)))) (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 3 (.split 1 (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 0 .leaf (.split 2 .leaf .leaf)))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRRL,cellLLLRRLRRRRRRR⟩

private theorem cellLLLRRLRRRRR : check boxLLLRRLRRRRR (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf (.split 3 .leaf .leaf)))) (.split 2 (.split 3 (.split 1 (.split 2 (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf)))) (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 3 (.split 1 (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 0 .leaf (.split 2 .leaf .leaf))))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRRL,cellLLLRRLRRRRRR⟩

private theorem cellLLLRRLRRRR : check boxLLLRRLRRRR (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 3 .leaf .leaf)) (.split 3 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf (.split 3 .leaf .leaf)))) (.split 2 (.split 3 (.split 1 (.split 2 (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf)))) (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 3 (.split 1 (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 0 .leaf (.split 2 .leaf .leaf)))))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRRL,cellLLLRRLRRRRR⟩

private theorem cellLLLRRLRRR : check boxLLLRRLRRR (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 3 .leaf .leaf)) (.split 3 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf (.split 3 .leaf .leaf)))) (.split 2 (.split 3 (.split 1 (.split 2 (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf)))) (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 3 (.split 1 (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 0 .leaf (.split 2 .leaf .leaf))))))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRRL,cellLLLRRLRRRR⟩

private theorem cellLLLRRLRR : check boxLLLRRLRR (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 2 .leaf .leaf))) (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 3 .leaf .leaf)) (.split 3 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf (.split 3 .leaf .leaf)))) (.split 2 (.split 3 (.split 1 (.split 2 (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf)))) (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 3 (.split 1 (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 0 .leaf (.split 2 .leaf .leaf)))))))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRRL,cellLLLRRLRRR⟩

private theorem cellLLLRRLR : check boxLLLRRLR (.split 2 .leaf (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 2 .leaf .leaf))) (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 3 .leaf .leaf)) (.split 3 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf (.split 3 .leaf .leaf)))) (.split 2 (.split 3 (.split 1 (.split 2 (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf)))) (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 3 (.split 1 (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 0 .leaf (.split 2 .leaf .leaf))))))))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLRL,cellLLLRRLRR⟩

private theorem cellLLLRRL : check boxLLLRRL (.split 1 (.split 2 .leaf .leaf) (.split 2 .leaf (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 2 .leaf .leaf))) (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 3 .leaf .leaf)) (.split 3 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf (.split 3 .leaf .leaf)))) (.split 2 (.split 3 (.split 1 (.split 2 (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf)))) (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 3 (.split 1 (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 0 .leaf (.split 2 .leaf .leaf)))))))))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRLL,cellLLLRRLR⟩

private def boxLLLRRR := Function.update boxLLLRR (2 : Fin 4) ((boxLLLRR 2).bisect.2)

private def boxLLLRRRL := Function.update boxLLLRRR (1 : Fin 4) ((boxLLLRRR 1).bisect.1)

private theorem cellLLLRRRL : check boxLLLRRRL (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf))) := by decide +kernel

private def boxLLLRRRR := Function.update boxLLLRRR (1 : Fin 4) ((boxLLLRRR 1).bisect.2)

private def boxLLLRRRRL := Function.update boxLLLRRRR (1 : Fin 4) ((boxLLLRRRR 1).bisect.1)

private theorem cellLLLRRRRL : check boxLLLRRRRL (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 2 .leaf .leaf)) := by decide +kernel

private def boxLLLRRRRR := Function.update boxLLLRRRR (1 : Fin 4) ((boxLLLRRRR 1).bisect.2)

private def boxLLLRRRRRL := Function.update boxLLLRRRRR (2 : Fin 4) ((boxLLLRRRRR 2).bisect.1)

private def boxLLLRRRRRLL := Function.update boxLLLRRRRRL (2 : Fin 4) ((boxLLLRRRRRL 2).bisect.1)

private def boxLLLRRRRRLLL := Function.update boxLLLRRRRRLL (1 : Fin 4) ((boxLLLRRRRRLL 1).bisect.1)

private def boxLLLRRRRRLLLL := Function.update boxLLLRRRRRLLL (2 : Fin 4) ((boxLLLRRRRRLLL 2).bisect.1)

private theorem cellLLLRRRRRLLLL : check boxLLLRRRRRLLLL (.split 1 (.split 2 .leaf .leaf) (.split 0 .leaf (.split 2 (.split 2 .leaf .leaf) .leaf))) := by decide +kernel

private def boxLLLRRRRRLLLR := Function.update boxLLLRRRRRLLL (2 : Fin 4) ((boxLLLRRRRRLLL 2).bisect.2)

private theorem cellLLLRRRRRLLLR : check boxLLLRRRRRLLLR (.split 2 (.split 1 .leaf .leaf) .leaf) := by decide +kernel

private theorem cellLLLRRRRRLLL : check boxLLLRRRRRLLL (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 0 .leaf (.split 2 (.split 2 .leaf .leaf) .leaf))) (.split 2 (.split 1 .leaf .leaf) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLLL,cellLLLRRRRRLLLR⟩

private def boxLLLRRRRRLLR := Function.update boxLLLRRRRRLL (1 : Fin 4) ((boxLLLRRRRRLL 1).bisect.2)

private def boxLLLRRRRRLLRL := Function.update boxLLLRRRRRLLR (2 : Fin 4) ((boxLLLRRRRRLLR 2).bisect.1)

private def boxLLLRRRRRLLRLL := Function.update boxLLLRRRRRLLRL (1 : Fin 4) ((boxLLLRRRRRLLRL 1).bisect.1)

private def boxLLLRRRRRLLRLLL := Function.update boxLLLRRRRRLLRLL (0 : Fin 4) ((boxLLLRRRRRLLRLL 0).bisect.1)

private theorem cellLLLRRRRRLLRLLL : check boxLLLRRRRRLLRLLL (.split 2 (.split 2 .leaf .leaf) .leaf) := by decide +kernel

private def boxLLLRRRRRLLRLLR := Function.update boxLLLRRRRRLLRLL (0 : Fin 4) ((boxLLLRRRRRLLRLL 0).bisect.2)

private def boxLLLRRRRRLLRLLRL := Function.update boxLLLRRRRRLLRLLR (2 : Fin 4) ((boxLLLRRRRRLLRLLR 2).bisect.1)

private def boxLLLRRRRRLLRLLRLL := Function.update boxLLLRRRRRLLRLLRL (2 : Fin 4) ((boxLLLRRRRRLLRLLRL 2).bisect.1)

private def boxLLLRRRRRLLRLLRLLL := Function.update boxLLLRRRRRLLRLLRLL (2 : Fin 4) ((boxLLLRRRRRLLRLLRLL 2).bisect.1)

private theorem cellLLLRRRRRLLRLLRLLL : check boxLLLRRRRRLLRLLRLLL (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) := by decide +kernel

private def boxLLLRRRRRLLRLLRLLR := Function.update boxLLLRRRRRLLRLLRLL (2 : Fin 4) ((boxLLLRRRRRLLRLLRLL 2).bisect.2)

private theorem cellLLLRRRRRLLRLLRLLR : check boxLLLRRRRRLLRLLRLLR (.split 1 .leaf .leaf) := by decide +kernel

private theorem cellLLLRRRRRLLRLLRLL : check boxLLLRRRRRLLRLLRLL (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLLRLLL,cellLLLRRRRRLLRLLRLLR⟩

private def boxLLLRRRRRLLRLLRLR := Function.update boxLLLRRRRRLLRLLRL (2 : Fin 4) ((boxLLLRRRRRLLRLLRL 2).bisect.2)

private theorem cellLLLRRRRRLLRLLRLR : check boxLLLRRRRRLLRLLRLR (.split 3 (.split 2 .leaf .leaf) .leaf) := by decide +kernel

private theorem cellLLLRRRRRLLRLLRL : check boxLLLRRRRRLLRLLRL (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf .leaf) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLLRLL,cellLLLRRRRRLLRLLRLR⟩

private def boxLLLRRRRRLLRLLRR := Function.update boxLLLRRRRRLLRLLR (2 : Fin 4) ((boxLLLRRRRRLLRLLR 2).bisect.2)

private def boxLLLRRRRRLLRLLRRL := Function.update boxLLLRRRRRLLRLLRR (3 : Fin 4) ((boxLLLRRRRRLLRLLRR 3).bisect.1)

private theorem cellLLLRRRRRLLRLLRRL : check boxLLLRRRRRLLRLLRRL (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) := by decide +kernel

private def boxLLLRRRRRLLRLLRRR := Function.update boxLLLRRRRRLLRLLRR (3 : Fin 4) ((boxLLLRRRRRLLRLLRR 3).bisect.2)

private theorem cellLLLRRRRRLLRLLRRR : check boxLLLRRRRRLLRLLRRR (.split 1 .leaf .leaf) := by decide +kernel

private theorem cellLLLRRRRRLLRLLRR : check boxLLLRRRRRLLRLLRR (.split 3 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLLRRL,cellLLLRRRRRLLRLLRRR⟩

private theorem cellLLLRRRRRLLRLLR : check boxLLLRRRRRLLRLLR (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLLRL,cellLLLRRRRRLLRLLRR⟩

private theorem cellLLLRRRRRLLRLL : check boxLLLRRRRRLLRLL (.split 0 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf)))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLLL,cellLLLRRRRRLLRLLR⟩

private def boxLLLRRRRRLLRLR := Function.update boxLLLRRRRRLLRL (1 : Fin 4) ((boxLLLRRRRRLLRL 1).bisect.2)

private def boxLLLRRRRRLLRLRL := Function.update boxLLLRRRRRLLRLR (0 : Fin 4) ((boxLLLRRRRRLLRLR 0).bisect.1)

private def boxLLLRRRRRLLRLRLL := Function.update boxLLLRRRRRLLRLRL (2 : Fin 4) ((boxLLLRRRRRLLRLRL 2).bisect.1)

private def boxLLLRRRRRLLRLRLLL := Function.update boxLLLRRRRRLLRLRLL (2 : Fin 4) ((boxLLLRRRRRLLRLRLL 2).bisect.1)

private def boxLLLRRRRRLLRLRLLLL := Function.update boxLLLRRRRRLLRLRLLL (2 : Fin 4) ((boxLLLRRRRRLLRLRLLL 2).bisect.1)

private theorem cellLLLRRRRRLLRLRLLLL : check boxLLLRRRRRLLRLRLLLL (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) := by decide +kernel

private def boxLLLRRRRRLLRLRLLLR := Function.update boxLLLRRRRRLLRLRLLL (2 : Fin 4) ((boxLLLRRRRRLLRLRLLL 2).bisect.2)

private theorem cellLLLRRRRRLLRLRLLLR : check boxLLLRRRRRLLRLRLLLR (.split 3 .leaf .leaf) := by decide +kernel

private theorem cellLLLRRRRRLLRLRLLL : check boxLLLRRRRRLLRLRLLL (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLRLLLL,cellLLLRRRRRLLRLRLLLR⟩

private def boxLLLRRRRRLLRLRLLR := Function.update boxLLLRRRRRLLRLRLL (2 : Fin 4) ((boxLLLRRRRRLLRLRLL 2).bisect.2)

private theorem cellLLLRRRRRLLRLRLLR : check boxLLLRRRRRLLRLRLLR (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf)) := by decide +kernel

private theorem cellLLLRRRRRLLRLRLL : check boxLLLRRRRRLLRLRLL (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLRLLL,cellLLLRRRRRLLRLRLLR⟩

private def boxLLLRRRRRLLRLRLR := Function.update boxLLLRRRRRLLRLRL (2 : Fin 4) ((boxLLLRRRRRLLRLRL 2).bisect.2)

private theorem cellLLLRRRRRLLRLRLR : check boxLLLRRRRRLLRLRLR (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) := by decide +kernel

private theorem cellLLLRRRRRLLRLRL : check boxLLLRRRRRLLRLRL (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLRLL,cellLLLRRRRRLLRLRLR⟩

private def boxLLLRRRRRLLRLRR := Function.update boxLLLRRRRRLLRLR (0 : Fin 4) ((boxLLLRRRRRLLRLR 0).bisect.2)

private def boxLLLRRRRRLLRLRRL := Function.update boxLLLRRRRRLLRLRR (2 : Fin 4) ((boxLLLRRRRRLLRLRR 2).bisect.1)

private def boxLLLRRRRRLLRLRRLL := Function.update boxLLLRRRRRLLRLRRL (2 : Fin 4) ((boxLLLRRRRRLLRLRRL 2).bisect.1)

private def boxLLLRRRRRLLRLRRLLL := Function.update boxLLLRRRRRLLRLRRLL (3 : Fin 4) ((boxLLLRRRRRLLRLRRLL 3).bisect.1)

private def boxLLLRRRRRLLRLRRLLLL := Function.update boxLLLRRRRRLLRLRRLLL (2 : Fin 4) ((boxLLLRRRRRLLRLRRLLL 2).bisect.1)

private theorem cellLLLRRRRRLLRLRRLLLL : check boxLLLRRRRRLLRLRRLLLL (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) := by decide +kernel

private def boxLLLRRRRRLLRLRRLLLR := Function.update boxLLLRRRRRLLRLRRLLL (2 : Fin 4) ((boxLLLRRRRRLLRLRRLLL 2).bisect.2)

private theorem cellLLLRRRRRLLRLRRLLLR : check boxLLLRRRRRLLRLRRLLLR (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf) := by decide +kernel

private theorem cellLLLRRRRRLLRLRRLLL : check boxLLLRRRRRLLRLRRLLL (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLRRLLLL,cellLLLRRRRRLLRLRRLLLR⟩

private def boxLLLRRRRRLLRLRRLLR := Function.update boxLLLRRRRRLLRLRRLL (3 : Fin 4) ((boxLLLRRRRRLLRLRRLL 3).bisect.2)

private theorem cellLLLRRRRRLLRLRRLLR : check boxLLLRRRRRLLRLRRLLR (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf) := by decide +kernel

private theorem cellLLLRRRRRLLRLRRLL : check boxLLLRRRRRLLRLRRLL (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLRRLLL,cellLLLRRRRRLLRLRRLLR⟩

private def boxLLLRRRRRLLRLRRLR := Function.update boxLLLRRRRRLLRLRRL (2 : Fin 4) ((boxLLLRRRRRLLRLRRL 2).bisect.2)

private def boxLLLRRRRRLLRLRRLRL := Function.update boxLLLRRRRRLLRLRRLR (3 : Fin 4) ((boxLLLRRRRRLLRLRRLR 3).bisect.1)

private theorem cellLLLRRRRRLLRLRRLRL : check boxLLLRRRRRLLRLRRLRL (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) := by decide +kernel

private def boxLLLRRRRRLLRLRRLRR := Function.update boxLLLRRRRRLLRLRRLR (3 : Fin 4) ((boxLLLRRRRRLLRLRRLR 3).bisect.2)

private theorem cellLLLRRRRRLLRLRRLRR : check boxLLLRRRRRLLRLRRLRR (.split 2 .leaf (.split 1 .leaf .leaf)) := by decide +kernel

private theorem cellLLLRRRRRLLRLRRLR : check boxLLLRRRRRLLRLRRLR (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLRRLRL,cellLLLRRRRRLLRLRRLRR⟩

private theorem cellLLLRRRRRLLRLRRL : check boxLLLRRRRRLLRLRRL (.split 2 (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLRRLL,cellLLLRRRRRLLRLRRLR⟩

private def boxLLLRRRRRLLRLRRR := Function.update boxLLLRRRRRLLRLRR (2 : Fin 4) ((boxLLLRRRRRLLRLRR 2).bisect.2)

private def boxLLLRRRRRLLRLRRRL := Function.update boxLLLRRRRRLLRLRRR (3 : Fin 4) ((boxLLLRRRRRLLRLRRR 3).bisect.1)

private def boxLLLRRRRRLLRLRRRLL := Function.update boxLLLRRRRRLLRLRRRL (2 : Fin 4) ((boxLLLRRRRRLLRLRRRL 2).bisect.1)

private theorem cellLLLRRRRRLLRLRRRLL : check boxLLLRRRRRLLRLRRRLL (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) := by decide +kernel

private def boxLLLRRRRRLLRLRRRLR := Function.update boxLLLRRRRRLLRLRRRL (2 : Fin 4) ((boxLLLRRRRRLLRLRRRL 2).bisect.2)

private theorem cellLLLRRRRRLLRLRRRLR : check boxLLLRRRRRLLRLRRRLR (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf) := by decide +kernel

private theorem cellLLLRRRRRLLRLRRRL : check boxLLLRRRRRLLRLRRRL (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLRRRLL,cellLLLRRRRRLLRLRRRLR⟩

private def boxLLLRRRRRLLRLRRRR := Function.update boxLLLRRRRRLLRLRRR (3 : Fin 4) ((boxLLLRRRRRLLRLRRR 3).bisect.2)

private def boxLLLRRRRRLLRLRRRRL := Function.update boxLLLRRRRRLLRLRRRR (2 : Fin 4) ((boxLLLRRRRRLLRLRRRR 2).bisect.1)

private theorem cellLLLRRRRRLLRLRRRRL : check boxLLLRRRRRLLRLRRRRL (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) := by decide +kernel

private def boxLLLRRRRRLLRLRRRRR := Function.update boxLLLRRRRRLLRLRRRR (2 : Fin 4) ((boxLLLRRRRRLLRLRRRR 2).bisect.2)

private def boxLLLRRRRRLLRLRRRRRL := Function.update boxLLLRRRRRLLRLRRRRR (1 : Fin 4) ((boxLLLRRRRRLLRLRRRRR 1).bisect.1)

private theorem cellLLLRRRRRLLRLRRRRRL : check boxLLLRRRRRLLRLRRRRRL .leaf := by decide +kernel

private def boxLLLRRRRRLLRLRRRRRR := Function.update boxLLLRRRRRLLRLRRRRR (1 : Fin 4) ((boxLLLRRRRRLLRLRRRRR 1).bisect.2)

private def boxLLLRRRRRLLRLRRRRRRL := Function.update boxLLLRRRRRLLRLRRRRRR (2 : Fin 4) ((boxLLLRRRRRLLRLRRRRRR 2).bisect.1)

private theorem cellLLLRRRRRLLRLRRRRRRL : check boxLLLRRRRRLLRLRRRRRRL (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) := by decide +kernel

private def boxLLLRRRRRLLRLRRRRRRR := Function.update boxLLLRRRRRLLRLRRRRRR (2 : Fin 4) ((boxLLLRRRRRLLRLRRRRRR 2).bisect.2)

private theorem cellLLLRRRRRLLRLRRRRRRR : check boxLLLRRRRRLLRLRRRRRRR (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf) := by decide +kernel

private theorem cellLLLRRRRRLLRLRRRRRR : check boxLLLRRRRRLLRLRRRRRR (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLRRRRRRL,cellLLLRRRRRLLRLRRRRRRR⟩

private theorem cellLLLRRRRRLLRLRRRRR : check boxLLLRRRRRLLRLRRRRR (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLRRRRRL,cellLLLRRRRRLLRLRRRRRR⟩

private theorem cellLLLRRRRRLLRLRRRR : check boxLLLRRRRRLLRLRRRR (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLRRRRL,cellLLLRRRRRLLRLRRRRR⟩

private theorem cellLLLRRRRRLLRLRRR : check boxLLLRRRRRLLRLRRR (.split 3 (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLRRRL,cellLLLRRRRRLLRLRRRR⟩

private theorem cellLLLRRRRRLLRLRR : check boxLLLRRRRRLLRLRR (.split 2 (.split 2 (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLRRL,cellLLLRRRRRLLRLRRR⟩

private theorem cellLLLRRRRRLLRLR : check boxLLLRRRRRLLRLR (.split 0 (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf))) (.split 2 (.split 2 (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf))))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLRL,cellLLLRRRRRLLRLRR⟩

private theorem cellLLLRRRRRLLRL : check boxLLLRRRRRLLRL (.split 1 (.split 0 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf)))) (.split 0 (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf))) (.split 2 (.split 2 (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)))))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRLL,cellLLLRRRRRLLRLR⟩

private def boxLLLRRRRRLLRR := Function.update boxLLLRRRRRLLR (2 : Fin 4) ((boxLLLRRRRRLLR 2).bisect.2)

private def boxLLLRRRRRLLRRL := Function.update boxLLLRRRRRLLRR (0 : Fin 4) ((boxLLLRRRRRLLRR 0).bisect.1)

private theorem cellLLLRRRRRLLRRL : check boxLLLRRRRRLLRRL (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) := by decide +kernel

private def boxLLLRRRRRLLRRR := Function.update boxLLLRRRRRLLRR (0 : Fin 4) ((boxLLLRRRRRLLRR 0).bisect.2)

private def boxLLLRRRRRLLRRRL := Function.update boxLLLRRRRRLLRRR (1 : Fin 4) ((boxLLLRRRRRLLRRR 1).bisect.1)

private theorem cellLLLRRRRRLLRRRL : check boxLLLRRRRRLLRRRL (.split 2 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) := by decide +kernel

private def boxLLLRRRRRLLRRRR := Function.update boxLLLRRRRRLLRRR (1 : Fin 4) ((boxLLLRRRRRLLRRR 1).bisect.2)

private def boxLLLRRRRRLLRRRRL := Function.update boxLLLRRRRRLLRRRR (2 : Fin 4) ((boxLLLRRRRRLLRRRR 2).bisect.1)

private def boxLLLRRRRRLLRRRRLL := Function.update boxLLLRRRRRLLRRRRL (0 : Fin 4) ((boxLLLRRRRRLLRRRRL 0).bisect.1)

private theorem cellLLLRRRRRLLRRRRLL : check boxLLLRRRRRLLRRRRLL (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) := by decide +kernel

private def boxLLLRRRRRLLRRRRLR := Function.update boxLLLRRRRRLLRRRRL (0 : Fin 4) ((boxLLLRRRRRLLRRRRL 0).bisect.2)

private theorem cellLLLRRRRRLLRRRRLR : check boxLLLRRRRRLLRRRRLR .leaf := by decide +kernel

private theorem cellLLLRRRRRLLRRRRL : check boxLLLRRRRRLLRRRRL (.split 0 (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) .leaf) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRRRRLL,cellLLLRRRRRLLRRRRLR⟩

private def boxLLLRRRRRLLRRRRR := Function.update boxLLLRRRRRLLRRRR (2 : Fin 4) ((boxLLLRRRRRLLRRRR 2).bisect.2)

private theorem cellLLLRRRRRLLRRRRR : check boxLLLRRRRRLLRRRRR (.split 2 (.split 0 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf)) := by decide +kernel

private theorem cellLLLRRRRRLLRRRR : check boxLLLRRRRRLLRRRR (.split 2 (.split 0 (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRRRRL,cellLLLRRRRRLLRRRRR⟩

private theorem cellLLLRRRRRLLRRR : check boxLLLRRRRRLLRRR (.split 1 (.split 2 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf)))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRRRL,cellLLLRRRRRLLRRRR⟩

private theorem cellLLLRRRRRLLRR : check boxLLLRRRRRLLRR (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 1 (.split 2 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRRL,cellLLLRRRRRLLRRR⟩

private theorem cellLLLRRRRRLLR : check boxLLLRRRRRLLR (.split 2 (.split 1 (.split 0 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf)))) (.split 0 (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf))) (.split 2 (.split 2 (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)))))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 1 (.split 2 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf)))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLRL,cellLLLRRRRRLLRR⟩

private theorem cellLLLRRRRRLL : check boxLLLRRRRRLL (.split 1 (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 0 .leaf (.split 2 (.split 2 .leaf .leaf) .leaf))) (.split 2 (.split 1 .leaf .leaf) .leaf)) (.split 2 (.split 1 (.split 0 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf)))) (.split 0 (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf))) (.split 2 (.split 2 (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)))))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 1 (.split 2 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf))))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLLL,cellLLLRRRRRLLR⟩

private def boxLLLRRRRRLR := Function.update boxLLLRRRRRL (2 : Fin 4) ((boxLLLRRRRRL 2).bisect.2)

private def boxLLLRRRRRLRL := Function.update boxLLLRRRRRLR (1 : Fin 4) ((boxLLLRRRRRLR 1).bisect.1)

private theorem cellLLLRRRRRLRL : check boxLLLRRRRRLRL (.split 2 .leaf .leaf) := by decide +kernel

private def boxLLLRRRRRLRR := Function.update boxLLLRRRRRLR (1 : Fin 4) ((boxLLLRRRRRLR 1).bisect.2)

private def boxLLLRRRRRLRRL := Function.update boxLLLRRRRRLRR (2 : Fin 4) ((boxLLLRRRRRLRR 2).bisect.1)

private def boxLLLRRRRRLRRLL := Function.update boxLLLRRRRRLRRL (0 : Fin 4) ((boxLLLRRRRRLRRL 0).bisect.1)

private theorem cellLLLRRRRRLRRLL : check boxLLLRRRRRLRRLL .leaf := by decide +kernel

private def boxLLLRRRRRLRRLR := Function.update boxLLLRRRRRLRRL (0 : Fin 4) ((boxLLLRRRRRLRRL 0).bisect.2)

private theorem cellLLLRRRRRLRRLR : check boxLLLRRRRRLRRLR (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf)) := by decide +kernel

private theorem cellLLLRRRRRLRRL : check boxLLLRRRRRLRRL (.split 0 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLRRLL,cellLLLRRRRRLRRLR⟩

private def boxLLLRRRRRLRRR := Function.update boxLLLRRRRRLRR (2 : Fin 4) ((boxLLLRRRRRLRR 2).bisect.2)

private theorem cellLLLRRRRRLRRR : check boxLLLRRRRRLRRR (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) := by decide +kernel

private theorem cellLLLRRRRRLRR : check boxLLLRRRRRLRR (.split 2 (.split 0 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLRRL,cellLLLRRRRRLRRR⟩

private theorem cellLLLRRRRRLR : check boxLLLRRRRRLR (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLRL,cellLLLRRRRRLRR⟩

private theorem cellLLLRRRRRL : check boxLLLRRRRRL (.split 2 (.split 1 (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 0 .leaf (.split 2 (.split 2 .leaf .leaf) .leaf))) (.split 2 (.split 1 .leaf .leaf) .leaf)) (.split 2 (.split 1 (.split 0 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf)))) (.split 0 (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf))) (.split 2 (.split 2 (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)))))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 1 (.split 2 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf))))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRLL,cellLLLRRRRRLR⟩

private def boxLLLRRRRRR := Function.update boxLLLRRRRR (2 : Fin 4) ((boxLLLRRRRR 2).bisect.2)

private def boxLLLRRRRRRL := Function.update boxLLLRRRRRR (2 : Fin 4) ((boxLLLRRRRRR 2).bisect.1)

private theorem cellLLLRRRRRRL : check boxLLLRRRRRRL (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf)) := by decide +kernel

private def boxLLLRRRRRRR := Function.update boxLLLRRRRRR (2 : Fin 4) ((boxLLLRRRRRR 2).bisect.2)

private theorem cellLLLRRRRRRR : check boxLLLRRRRRRR (.split 2 (.split 1 .leaf .leaf) .leaf) := by decide +kernel

private theorem cellLLLRRRRRR : check boxLLLRRRRRR (.split 2 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRRL,cellLLLRRRRRRR⟩

private theorem cellLLLRRRRR : check boxLLLRRRRR (.split 2 (.split 2 (.split 1 (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 0 .leaf (.split 2 (.split 2 .leaf .leaf) .leaf))) (.split 2 (.split 1 .leaf .leaf) .leaf)) (.split 2 (.split 1 (.split 0 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf)))) (.split 0 (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf))) (.split 2 (.split 2 (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)))))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 1 (.split 2 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf))))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf))))) (.split 2 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRRL,cellLLLRRRRRR⟩

private theorem cellLLLRRRR : check boxLLLRRRR (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 2 .leaf .leaf)) (.split 2 (.split 2 (.split 1 (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 0 .leaf (.split 2 (.split 2 .leaf .leaf) .leaf))) (.split 2 (.split 1 .leaf .leaf) .leaf)) (.split 2 (.split 1 (.split 0 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf)))) (.split 0 (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf))) (.split 2 (.split 2 (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)))))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 1 (.split 2 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf))))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf))))) (.split 2 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) .leaf)))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRRL,cellLLLRRRRR⟩

private theorem cellLLLRRR : check boxLLLRRR (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 2 .leaf .leaf)) (.split 2 (.split 2 (.split 1 (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 0 .leaf (.split 2 (.split 2 .leaf .leaf) .leaf))) (.split 2 (.split 1 .leaf .leaf) .leaf)) (.split 2 (.split 1 (.split 0 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf)))) (.split 0 (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf))) (.split 2 (.split 2 (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)))))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 1 (.split 2 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf))))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf))))) (.split 2 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) .leaf))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRRL,cellLLLRRRR⟩

private theorem cellLLLRR : check boxLLLRR (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 .leaf (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 2 .leaf .leaf))) (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 3 .leaf .leaf)) (.split 3 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf (.split 3 .leaf .leaf)))) (.split 2 (.split 3 (.split 1 (.split 2 (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf)))) (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 3 (.split 1 (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 0 .leaf (.split 2 .leaf .leaf)))))))))))) (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 2 .leaf .leaf)) (.split 2 (.split 2 (.split 1 (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 0 .leaf (.split 2 (.split 2 .leaf .leaf) .leaf))) (.split 2 (.split 1 .leaf .leaf) .leaf)) (.split 2 (.split 1 (.split 0 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf)))) (.split 0 (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf))) (.split 2 (.split 2 (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)))))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 1 (.split 2 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf))))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf))))) (.split 2 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) .leaf)))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRRL,cellLLLRRR⟩

private theorem cellLLLR : check boxLLLR (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 .leaf (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 2 .leaf .leaf))) (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 3 .leaf .leaf)) (.split 3 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf (.split 3 .leaf .leaf)))) (.split 2 (.split 3 (.split 1 (.split 2 (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf)))) (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 3 (.split 1 (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 0 .leaf (.split 2 .leaf .leaf)))))))))))) (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 2 .leaf .leaf)) (.split 2 (.split 2 (.split 1 (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 0 .leaf (.split 2 (.split 2 .leaf .leaf) .leaf))) (.split 2 (.split 1 .leaf .leaf) .leaf)) (.split 2 (.split 1 (.split 0 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf)))) (.split 0 (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf))) (.split 2 (.split 2 (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)))))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 1 (.split 2 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf))))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf))))) (.split 2 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) .leaf))))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLRL,cellLLLRR⟩

private theorem cellLLL : check boxLLL (.split 0 .leaf (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 .leaf (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 2 .leaf .leaf))) (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 3 .leaf .leaf)) (.split 3 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf (.split 3 .leaf .leaf)))) (.split 2 (.split 3 (.split 1 (.split 2 (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf)))) (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 3 (.split 1 (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 0 .leaf (.split 2 .leaf .leaf)))))))))))) (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 2 .leaf .leaf)) (.split 2 (.split 2 (.split 1 (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 0 .leaf (.split 2 (.split 2 .leaf .leaf) .leaf))) (.split 2 (.split 1 .leaf .leaf) .leaf)) (.split 2 (.split 1 (.split 0 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf)))) (.split 0 (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf))) (.split 2 (.split 2 (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)))))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 1 (.split 2 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf))))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf))))) (.split 2 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) .leaf)))))))) := Bool.and_eq_true_iff.mpr ⟨cellLLLL,cellLLLR⟩

private def boxLLR := Function.update boxLL (0 : Fin 4) ((boxLL 0).bisect.2)

private def boxLLRL := Function.update boxLLR (0 : Fin 4) ((boxLLR 0).bisect.1)

private theorem cellLLRL : check boxLLRL (.split 0 (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 1 .leaf .leaf)) := by decide +kernel

private def boxLLRR := Function.update boxLLR (0 : Fin 4) ((boxLLR 0).bisect.2)

private theorem cellLLRR : check boxLLRR .leaf := by decide +kernel

private theorem cellLLR : check boxLLR (.split 0 (.split 0 (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 1 .leaf .leaf)) .leaf) := Bool.and_eq_true_iff.mpr ⟨cellLLRL,cellLLRR⟩

private theorem cellLL : check boxLL (.split 0 (.split 0 .leaf (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 .leaf (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 2 .leaf .leaf))) (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 3 .leaf .leaf)) (.split 3 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf (.split 3 .leaf .leaf)))) (.split 2 (.split 3 (.split 1 (.split 2 (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf)))) (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 3 (.split 1 (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 0 .leaf (.split 2 .leaf .leaf)))))))))))) (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 2 .leaf .leaf)) (.split 2 (.split 2 (.split 1 (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 0 .leaf (.split 2 (.split 2 .leaf .leaf) .leaf))) (.split 2 (.split 1 .leaf .leaf) .leaf)) (.split 2 (.split 1 (.split 0 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf)))) (.split 0 (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf))) (.split 2 (.split 2 (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)))))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 1 (.split 2 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf))))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf))))) (.split 2 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) .leaf)))))))) (.split 0 (.split 0 (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 1 .leaf .leaf)) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellLLL,cellLLR⟩

private def boxLR := Function.update boxL (0 : Fin 4) ((boxL 0).bisect.2)

private theorem cellLR : check boxLR .leaf := by decide +kernel

private theorem cellL : check boxL (.split 0 (.split 0 (.split 0 .leaf (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 .leaf (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 2 .leaf .leaf))) (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 3 .leaf .leaf)) (.split 3 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf (.split 3 .leaf .leaf)))) (.split 2 (.split 3 (.split 1 (.split 2 (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf)))) (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 3 (.split 1 (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 0 .leaf (.split 2 .leaf .leaf)))))))))))) (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 2 .leaf .leaf)) (.split 2 (.split 2 (.split 1 (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 0 .leaf (.split 2 (.split 2 .leaf .leaf) .leaf))) (.split 2 (.split 1 .leaf .leaf) .leaf)) (.split 2 (.split 1 (.split 0 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf)))) (.split 0 (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf))) (.split 2 (.split 2 (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)))))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 1 (.split 2 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf))))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf))))) (.split 2 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) .leaf)))))))) (.split 0 (.split 0 (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 1 .leaf .leaf)) .leaf)) .leaf) := Bool.and_eq_true_iff.mpr ⟨cellLL,cellLR⟩

private def boxR := Function.update whole (0 : Fin 4) ((whole 0).bisect.2)

private def boxRL := Function.update boxR (0 : Fin 4) ((boxR 0).bisect.1)

private theorem cellRL : check boxRL .leaf := by decide +kernel

private def boxRR := Function.update boxR (0 : Fin 4) ((boxR 0).bisect.2)

private def boxRRL := Function.update boxRR (0 : Fin 4) ((boxRR 0).bisect.1)

private theorem cellRRL : check boxRRL .leaf := by decide +kernel

private def boxRRR := Function.update boxRR (0 : Fin 4) ((boxRR 0).bisect.2)

private def boxRRRL := Function.update boxRRR (0 : Fin 4) ((boxRRR 0).bisect.1)

private def boxRRRLL := Function.update boxRRRL (0 : Fin 4) ((boxRRRL 0).bisect.1)

private theorem cellRRRLL : check boxRRRLL .leaf := by decide +kernel

private def boxRRRLR := Function.update boxRRRL (0 : Fin 4) ((boxRRRL 0).bisect.2)

private def boxRRRLRL := Function.update boxRRRLR (2 : Fin 4) ((boxRRRLR 2).bisect.1)

private def boxRRRLRLL := Function.update boxRRRLRL (1 : Fin 4) ((boxRRRLRL 1).bisect.1)

private def boxRRRLRLLL := Function.update boxRRRLRLL (1 : Fin 4) ((boxRRRLRLL 1).bisect.1)

private def boxRRRLRLLLL := Function.update boxRRRLRLLL (2 : Fin 4) ((boxRRRLRLLL 2).bisect.1)

private theorem cellRRRLRLLLL : check boxRRRLRLLLL (.split 1 .leaf .leaf) := by decide +kernel

private def boxRRRLRLLLR := Function.update boxRRRLRLLL (2 : Fin 4) ((boxRRRLRLLL 2).bisect.2)

private def boxRRRLRLLLRL := Function.update boxRRRLRLLLR (2 : Fin 4) ((boxRRRLRLLLR 2).bisect.1)

private theorem cellRRRLRLLLRL : check boxRRRLRLLLRL (.split 2 .leaf .leaf) := by decide +kernel

private def boxRRRLRLLLRR := Function.update boxRRRLRLLLR (2 : Fin 4) ((boxRRRLRLLLR 2).bisect.2)

private theorem cellRRRLRLLLRR : check boxRRRLRLLLRR (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf)) := by decide +kernel

private theorem cellRRRLRLLLR : check boxRRRLRLLLR (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellRRRLRLLLRL,cellRRRLRLLLRR⟩

private theorem cellRRRLRLLL : check boxRRRLRLLL (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf)))) := Bool.and_eq_true_iff.mpr ⟨cellRRRLRLLLL,cellRRRLRLLLR⟩

private def boxRRRLRLLR := Function.update boxRRRLRLL (1 : Fin 4) ((boxRRRLRLL 1).bisect.2)

private theorem cellRRRLRLLR : check boxRRRLRLLR (.split 2 .leaf (.split 1 .leaf .leaf)) := by decide +kernel

private theorem cellRRRLRLL : check boxRRRLRLL (.split 1 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf)))) (.split 2 .leaf (.split 1 .leaf .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellRRRLRLLL,cellRRRLRLLR⟩

private def boxRRRLRLR := Function.update boxRRRLRL (1 : Fin 4) ((boxRRRLRL 1).bisect.2)

private theorem cellRRRLRLR : check boxRRRLRLR (.split 2 .leaf .leaf) := by decide +kernel

private theorem cellRRRLRL : check boxRRRLRL (.split 1 (.split 1 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf)))) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 2 .leaf .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellRRRLRLL,cellRRRLRLR⟩

private def boxRRRLRR := Function.update boxRRRLR (2 : Fin 4) ((boxRRRLR 2).bisect.2)

private theorem cellRRRLRR : check boxRRRLRR (.split 2 (.split 1 (.split 1 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) .leaf) .leaf) := by decide +kernel

private theorem cellRRRLR : check boxRRRLR (.split 2 (.split 1 (.split 1 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf)))) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 2 .leaf .leaf)) (.split 2 (.split 1 (.split 1 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) .leaf) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellRRRLRL,cellRRRLRR⟩

private theorem cellRRRL : check boxRRRL (.split 0 .leaf (.split 2 (.split 1 (.split 1 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf)))) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 2 .leaf .leaf)) (.split 2 (.split 1 (.split 1 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) .leaf) .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellRRRLL,cellRRRLR⟩

private def boxRRRR := Function.update boxRRR (0 : Fin 4) ((boxRRR 0).bisect.2)

private def boxRRRRL := Function.update boxRRRR (0 : Fin 4) ((boxRRRR 0).bisect.1)

private def boxRRRRLL := Function.update boxRRRRL (1 : Fin 4) ((boxRRRRL 1).bisect.1)

private def boxRRRRLLL := Function.update boxRRRRLL (2 : Fin 4) ((boxRRRRLL 2).bisect.1)

private theorem cellRRRRLLL : check boxRRRRLLL (.split 1 (.split 2 .leaf (.split 3 .leaf (.split 1 .leaf .leaf))) (.split 2 .leaf .leaf)) := by decide +kernel

private def boxRRRRLLR := Function.update boxRRRRLL (2 : Fin 4) ((boxRRRRLL 2).bisect.2)

private theorem cellRRRRLLR : check boxRRRRLLR (.split 1 (.split 2 .leaf .leaf) .leaf) := by decide +kernel

private theorem cellRRRRLL : check boxRRRRLL (.split 2 (.split 1 (.split 2 .leaf (.split 3 .leaf (.split 1 .leaf .leaf))) (.split 2 .leaf .leaf)) (.split 1 (.split 2 .leaf .leaf) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellRRRRLLL,cellRRRRLLR⟩

private def boxRRRRLR := Function.update boxRRRRL (1 : Fin 4) ((boxRRRRL 1).bisect.2)

private theorem cellRRRRLR : check boxRRRRLR (.split 2 (.split 1 .leaf .leaf) .leaf) := by decide +kernel

private theorem cellRRRRL : check boxRRRRL (.split 1 (.split 2 (.split 1 (.split 2 .leaf (.split 3 .leaf (.split 1 .leaf .leaf))) (.split 2 .leaf .leaf)) (.split 1 (.split 2 .leaf .leaf) .leaf)) (.split 2 (.split 1 .leaf .leaf) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellRRRRLL,cellRRRRLR⟩

private def boxRRRRR := Function.update boxRRRR (0 : Fin 4) ((boxRRRR 0).bisect.2)

private theorem cellRRRRR : check boxRRRRR .leaf := by decide +kernel

private theorem cellRRRR : check boxRRRR (.split 0 (.split 1 (.split 2 (.split 1 (.split 2 .leaf (.split 3 .leaf (.split 1 .leaf .leaf))) (.split 2 .leaf .leaf)) (.split 1 (.split 2 .leaf .leaf) .leaf)) (.split 2 (.split 1 .leaf .leaf) .leaf)) .leaf) := Bool.and_eq_true_iff.mpr ⟨cellRRRRL,cellRRRRR⟩

private theorem cellRRR : check boxRRR (.split 0 (.split 0 .leaf (.split 2 (.split 1 (.split 1 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf)))) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 2 .leaf .leaf)) (.split 2 (.split 1 (.split 1 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) .leaf) .leaf))) (.split 0 (.split 1 (.split 2 (.split 1 (.split 2 .leaf (.split 3 .leaf (.split 1 .leaf .leaf))) (.split 2 .leaf .leaf)) (.split 1 (.split 2 .leaf .leaf) .leaf)) (.split 2 (.split 1 .leaf .leaf) .leaf)) .leaf)) := Bool.and_eq_true_iff.mpr ⟨cellRRRL,cellRRRR⟩

private theorem cellRR : check boxRR (.split 0 .leaf (.split 0 (.split 0 .leaf (.split 2 (.split 1 (.split 1 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf)))) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 2 .leaf .leaf)) (.split 2 (.split 1 (.split 1 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) .leaf) .leaf))) (.split 0 (.split 1 (.split 2 (.split 1 (.split 2 .leaf (.split 3 .leaf (.split 1 .leaf .leaf))) (.split 2 .leaf .leaf)) (.split 1 (.split 2 .leaf .leaf) .leaf)) (.split 2 (.split 1 .leaf .leaf) .leaf)) .leaf))) := Bool.and_eq_true_iff.mpr ⟨cellRRL,cellRRR⟩

private theorem cellR : check boxR (.split 0 .leaf (.split 0 .leaf (.split 0 (.split 0 .leaf (.split 2 (.split 1 (.split 1 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf)))) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 2 .leaf .leaf)) (.split 2 (.split 1 (.split 1 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) .leaf) .leaf))) (.split 0 (.split 1 (.split 2 (.split 1 (.split 2 .leaf (.split 3 .leaf (.split 1 .leaf .leaf))) (.split 2 .leaf .leaf)) (.split 1 (.split 2 .leaf .leaf) .leaf)) (.split 2 (.split 1 .leaf .leaf) .leaf)) .leaf)))) := Bool.and_eq_true_iff.mpr ⟨cellRL,cellRR⟩

private theorem cell : check whole (.split 0 (.split 0 (.split 0 (.split 0 .leaf (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 .leaf (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 2 .leaf .leaf))) (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 3 .leaf .leaf)) (.split 3 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 3 (.split 1 .leaf .leaf) .leaf) (.split 3 (.split 0 .leaf (.split 2 .leaf (.split 1 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf (.split 3 .leaf .leaf)))) (.split 2 (.split 3 (.split 1 (.split 2 (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf) (.split 0 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 1 .leaf .leaf) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 3 (.split 1 .leaf .leaf) .leaf))) (.split 2 (.split 3 (.split 0 .leaf .leaf) .leaf) (.split 0 (.split 2 .leaf .leaf) .leaf))) (.split 2 .leaf .leaf))) (.split 0 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 1 .leaf .leaf)) .leaf) .leaf) .leaf) (.split 3 (.split 1 (.split 0 .leaf .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf)))) (.split 2 (.split 1 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 3 (.split 1 (.split 0 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 2 .leaf (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 0 .leaf .leaf))) (.split 0 (.split 2 .leaf (.split 2 .leaf .leaf)) .leaf)) (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 0 (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf))) (.split 3 (.split 2 (.split 1 .leaf (.split 1 .leaf .leaf)) (.split 1 .leaf (.split 2 .leaf (.split 1 .leaf .leaf)))) .leaf))) .leaf) (.split 0 (.split 1 .leaf .leaf) .leaf))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) (.split 0 .leaf (.split 2 .leaf .leaf)))))))))))) (.split 1 (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 1 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 2 .leaf .leaf)) (.split 2 (.split 2 (.split 1 (.split 2 (.split 1 (.split 2 .leaf .leaf) (.split 0 .leaf (.split 2 (.split 2 .leaf .leaf) .leaf))) (.split 2 (.split 1 .leaf .leaf) .leaf)) (.split 2 (.split 1 (.split 0 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 0 .leaf .leaf)) .leaf)) .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf .leaf) .leaf)) (.split 3 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf)) (.split 1 .leaf .leaf)))) (.split 0 (.split 2 (.split 2 (.split 2 (.split 3 (.split 1 .leaf (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 3 .leaf .leaf)) (.split 2 (.split 3 .leaf .leaf) (.split 3 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 2 .leaf .leaf))) (.split 2 (.split 2 (.split 3 (.split 2 (.split 0 (.split 3 (.split 1 .leaf (.split 0 (.split 1 .leaf .leaf) .leaf)) .leaf) .leaf) (.split 0 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 2 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)) (.split 3 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 2 .leaf (.split 1 .leaf .leaf)))) (.split 3 (.split 2 (.split 0 (.split 1 .leaf (.split 2 (.split 2 .leaf .leaf) (.split 2 .leaf .leaf))) .leaf) (.split 0 (.split 1 .leaf (.split 2 (.split 3 .leaf .leaf) (.split 1 .leaf .leaf))) .leaf)) (.split 2 (.split 2 (.split 2 .leaf .leaf) (.split 1 .leaf (.split 2 .leaf .leaf))) (.split 1 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 3 (.split 2 .leaf (.split 1 .leaf .leaf)) .leaf)))))))) (.split 0 (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 1 (.split 2 (.split 2 (.split 2 .leaf .leaf) .leaf) (.split 1 .leaf .leaf)) (.split 2 (.split 0 (.split 2 (.split 3 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) (.split 3 .leaf .leaf)) .leaf) (.split 2 (.split 0 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf))))))) (.split 1 (.split 2 .leaf .leaf) (.split 2 (.split 0 .leaf (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf))) (.split 2 (.split 2 (.split 1 .leaf .leaf) .leaf) (.split 1 .leaf .leaf))))) (.split 2 (.split 2 (.split 2 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)) (.split 1 .leaf .leaf)) (.split 2 (.split 1 .leaf .leaf) .leaf)))))))) (.split 0 (.split 0 (.split 2 .leaf (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 1 .leaf .leaf)) .leaf)) .leaf) (.split 0 .leaf (.split 0 .leaf (.split 0 (.split 0 .leaf (.split 2 (.split 1 (.split 1 (.split 2 (.split 1 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 2 .leaf .leaf) (.split 2 (.split 1 .leaf .leaf) .leaf)))) (.split 2 .leaf (.split 1 .leaf .leaf))) (.split 2 .leaf .leaf)) (.split 2 (.split 1 (.split 1 (.split 2 (.split 1 .leaf .leaf) .leaf) .leaf) .leaf) .leaf))) (.split 0 (.split 1 (.split 2 (.split 1 (.split 2 .leaf (.split 3 .leaf (.split 1 .leaf .leaf))) (.split 2 .leaf .leaf)) (.split 1 (.split 2 .leaf .leaf) .leaf)) (.split 2 (.split 1 .leaf .leaf) .leaf)) .leaf))))) := Bool.and_eq_true_iff.mpr ⟨cellL,cellR⟩

theorem barrier {p : Process} (hp : Admissible p) {x y z v : ℝ}
    (hx : x ∈ nodeBox) (hy : y ∈ nodeBox) (hz : z ∈ nodeBox) (hv : v ∈ supplyBox) :
    -abs (x-(-2/25)) < halfStep p x y z v ∧ halfStep p x y z v < abs (x-83/100) :=
  checked hp ![x,y,z,v] _ whole (by intro i; fin_cases i <;> assumption) cell

end SpiceSmtBench.RingEnvelope
