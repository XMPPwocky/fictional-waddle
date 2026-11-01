import Mathlib

/-!
# Adverse selection in the unpaired pool

PROVED:
* `share_lt` : for `c < 1` (in particular `0 < c < 1`) and `0 ≤ x < c`, the cooperator share of the unpaired pool,
  `x / (x + 1 - c)` (single cooperator mass `x`, all defector mass `1 - c` single), is strictly
  below the population cooperator share `c`.
* `share_eq` : for any real `c` and `x = c` (no cooperator paired), the pool share equals `c`.
* `count_lt` : for naturals `C_pool < C` and `D > 0`, `C_pool / (C_pool + D) < C / (C + D)` in `ℝ`.
* `count_le` : for naturals `C_pool ≤ C` and `D > 0`, `C_pool / (C_pool + D) ≤ C / (C + D)` in `ℝ`.
* `steady_state_exists` : for `0 < c < 1` and `δ > 0`, there is `x ∈ (0, c)` with
  `δ * (c - x) = x ^ 2 / (x + 1 - c)` (by the intermediate value theorem).
-/

namespace PartnerPoolAdverseSelection

theorem share_lt {c x : ℝ} (hc1 : c < 1) (hx0 : 0 ≤ x) (hxc : x < c) :
    x / (x + 1 - c) < c := by
  have hden : 0 < x + 1 - c := by linarith
  rw [div_lt_iff₀ hden]
  nlinarith

theorem share_eq {c x : ℝ} (hx : x = c) :
    x / (x + 1 - c) = c := by
  rw [hx]
  have : c + 1 - c = 1 := by ring
  rw [this, div_one]

theorem count_lt {Cp C D : ℕ} (hC : Cp < C) (hD : 0 < D) :
    (Cp : ℝ) / (Cp + D) < (C : ℝ) / (C + D) := by
  have hC' : (Cp : ℝ) < C := by exact_mod_cast hC
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hCp0 : (0 : ℝ) ≤ Cp := Nat.cast_nonneg _
  have h1 : (0 : ℝ) < Cp + D := by linarith
  have h2 : (0 : ℝ) < C + D := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith

theorem count_le {Cp C D : ℕ} (hC : Cp ≤ C) (hD : 0 < D) :
    (Cp : ℝ) / (Cp + D) ≤ (C : ℝ) / (C + D) := by
  have hC' : (Cp : ℝ) ≤ C := by exact_mod_cast hC
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hCp0 : (0 : ℝ) ≤ Cp := Nat.cast_nonneg _
  have h1 : (0 : ℝ) < Cp + D := by linarith
  have h2 : (0 : ℝ) < C + D := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

theorem steady_state_exists {c δ : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hδ : 0 < δ) :
    ∃ x ∈ Set.Ioo 0 c, δ * (c - x) = x ^ 2 / (x + 1 - c) := by
  set f : ℝ → ℝ := fun x => δ * (c - x) - x ^ 2 / (x + 1 - c) with hf
  have hcont : ContinuousOn f (Set.Icc 0 c) := by
    apply ContinuousOn.sub
    · fun_prop
    · apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro x hx
        have := hx.1
        linarith
  have hf0 : f 0 = δ * c := by simp [hf]
  have hfc : f c = -c ^ 2 := by
    simp only [hf]
    have : c + 1 - c = 1 := by ring
    rw [this, div_one]
    ring
  have hmem : (0 : ℝ) ∈ Set.Ioo (f c) (f 0) := by
    rw [hf0, hfc]
    constructor
    · nlinarith
    · positivity
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo' hc0.le hcont hmem
  refine ⟨x, hx, ?_⟩
  simp only [hf] at hfx
  linarith

end PartnerPoolAdverseSelection
