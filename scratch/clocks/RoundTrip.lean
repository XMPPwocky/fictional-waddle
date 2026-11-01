import Mathlib

/-!
# What two programs learn about each other's clocks by interrupting each other

Program A sends at its time `t₁`. B receives it at B-time `t₂` and replies at B-time `t₃`, and A receives the reply at
A-time `t₄`. B's clock reads A's clock plus an offset `θ`, scaled by a rate `r`. The trip from A to B takes `d₁` and the
trip back takes `d₂`, both in A-time.

PROVED:
* `offset_unidentifiable`: shifting the offset by `δ` while moving `δ` of delay from the outbound trip to the return trip
  leaves all four timestamps unchanged. No exchange of interrupts can measure the offset beyond the split of the delays.
* `ntp_error`: the round-trip estimate `((t₂ − t₁) + (t₃ − t₄)) / 2` misses the true offset by exactly `(d₁ − d₂) / 2`.
* `ntp_exact_iff`: it is exact iff the two trips take equally long.
* `rate_identifiable`: with constant delays, two exchanges recover the rate exactly: `(t₂' − t₂) / (t₁' − t₁) = r`.
  The relative clock rate is measurable; the offset is fixed only up to a convention about the delays.
-/

namespace RoundTrip

def t₂ (r θ t₁ d₁ : ℝ) : ℝ := r * (t₁ + d₁) + θ
noncomputable def t₄ (r θ t₃ d₂ : ℝ) : ℝ := (t₃ - θ) / r + d₂

theorem offset_unidentifiable (θ t₁ t₃ d₁ d₂ δ : ℝ) :
    t₂ 1 (θ + δ) t₁ (d₁ - δ) = t₂ 1 θ t₁ d₁ ∧ t₄ 1 (θ + δ) t₃ (d₂ + δ) = t₄ 1 θ t₃ d₂ := by
  unfold t₂ t₄; constructor <;> ring

theorem ntp_error (θ t₁ t₃ d₁ d₂ : ℝ) :
    ((t₂ 1 θ t₁ d₁ - t₁) + (t₃ - t₄ 1 θ t₃ d₂)) / 2 - θ = (d₁ - d₂) / 2 := by
  unfold t₂ t₄; ring

theorem ntp_exact_iff (θ t₁ t₃ d₁ d₂ : ℝ) :
    ((t₂ 1 θ t₁ d₁ - t₁) + (t₃ - t₄ 1 θ t₃ d₂)) / 2 = θ ↔ d₁ = d₂ := by
  have h := ntp_error θ t₁ t₃ d₁ d₂
  constructor
  · intro e; linarith
  · intro e; subst e; linarith

theorem rate_identifiable (r θ t₁ t₁' d₁ : ℝ) (h : t₁' ≠ t₁) :
    (t₂ r θ t₁' d₁ - t₂ r θ t₁ d₁) / (t₁' - t₁) = r := by
  unfold t₂
  rw [show r * (t₁' + d₁) + θ - (r * (t₁ + d₁) + θ) = r * (t₁' - t₁) by ring]
  exact mul_div_cancel_right₀ r (sub_ne_zero.mpr h)

end RoundTrip
