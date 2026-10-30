import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace KernelR

def copySetting (cap own incoming : ℝ) : ℝ := min cap (max own incoming)

theorem copy_bounded {cap own incoming : ℝ} : copySetting cap own incoming ≤ cap := min_le_left _ _

theorem copy_never_lowers {cap own incoming : ℝ} (hown : own ≤ cap) :
    own ≤ copySetting cap own incoming := le_min hown (le_max_left _ _)

theorem copy_exact {cap own incoming : ℝ} (hown : own ≤ incoming) (hcap : incoming ≤ cap) :
    copySetting cap own incoming = incoming := by
  simp [copySetting,max_eq_right hown,min_eq_right hcap]

theorem copying_is_idempotent {cap own incoming : ℝ} (hcap : incoming ≤ cap) :
    copySetting cap (copySetting cap own incoming) incoming = copySetting cap own incoming := by
  have h : incoming ≤ copySetting cap own incoming := le_min hcap (le_max_right _ _)
  change min cap (max (copySetting cap own incoming) incoming) = _
  rw [max_eq_left h, min_eq_right copy_bounded]

/-- Any deterministic readout is preserved when every setting it reads is copied exactly. -/
theorem inherited_readout {ι Output : Type*} (readout : (ι → ℝ) → Output)
    (cap own learned : ι → ℝ) (hown : ∀ i, own i ≤ learned i)
    (hcap : ∀ i, learned i ≤ cap i) :
    readout (fun i => copySetting (cap i) (own i) (learned i)) = readout learned := by
  congr 1; funext i; exact copy_exact (hown i) (hcap i)

/-- Monotone memory cannot undo a previously acquired increase. -/
theorem monotone_memory_cannot_erase {memory : ℕ → ℝ} (hm : Monotone memory)
    {i j : ℕ} {baseline : ℝ} (hij : i ≤ j) (hacquired : baseline < memory i) :
    baseline < memory j := hacquired.trans_le (hm hij)

end KernelR
