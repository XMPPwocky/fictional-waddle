import Mathlib

/-!
# Sign rule for Coulomb forces

The Coulomb force along the line joining two point charges `q₁, q₂ : ℝ` at distance `r`,
with coupling constant `k`, is `F k q₁ q₂ r = k * q₁ * q₂ / r ^ 2`; positive means repulsion.

PROVED (hypotheses `0 < k`, `0 < r` only where stated):
* `force_pos_iff` (k>0, r>0): `0 < F ↔ 0 < q₁ * q₂` (like charges repel).
* `force_neg_iff` (k>0, r>0): `F < 0 ↔ q₁ * q₂ < 0` (opposite charges attract).
* `force_eq_zero_iff` (k>0, r>0): `F = 0 ↔ q₁ = 0 ∨ q₂ = 0`.
* `force_charge_conj` (no hypotheses): `F k (-q₁) (-q₂) r = F k q₁ q₂ r`.
* `force_flip_left`, `force_flip_right` (no hypotheses): negating one charge negates `F`.
* `force_r_refl` (no hypotheses): `F k q₁ q₂ r = F k q₁ q₂ r`.
* `force_scale` (no hypotheses): `F k q₁ q₂ (c * r) = F k q₁ q₂ r / c ^ 2`.
* `force_double` (no hypotheses): `F k q₁ q₂ (2 * r) = F k q₁ q₂ r / 4`.

INTERPRETED:
* "positive means repulsion" is the sign convention of `F`; no vector geometry is modelled.
* "swapping every charge is invisible to the forces" is read as `force_charge_conj`:
  every pairwise force is unchanged under global charge conjugation.
* The scaling laws hold for all real `r` and `c` (Lean's `x / 0 = 0` makes `r = 0` or `c = 0`
  consistent), so `r > 0` is not needed for (2)-(4).
-/

namespace CoulombSignB

/-- Coulomb force along the joining line; positive = repulsion. -/
noncomputable def F (k q₁ q₂ r : ℝ) : ℝ := k * q₁ * q₂ / r ^ 2

theorem force_pos_iff {k q₁ q₂ r : ℝ} (hk : 0 < k) (hr : 0 < r) :
    0 < F k q₁ q₂ r ↔ 0 < q₁ * q₂ := by
  have hr2 : 0 < r ^ 2 := by positivity
  unfold F
  rw [div_pos_iff_of_pos_right hr2, mul_assoc]
  exact ⟨fun h => pos_of_mul_pos_right h hk.le, fun h => mul_pos hk h⟩

theorem force_neg_iff {k q₁ q₂ r : ℝ} (hk : 0 < k) (hr : 0 < r) :
    F k q₁ q₂ r < 0 ↔ q₁ * q₂ < 0 := by
  have hr2 : 0 < r ^ 2 := by positivity
  unfold F
  rw [div_neg_iff, mul_assoc]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, _⟩)
    · exact absurd hr2 (not_lt.mpr h2.le)
    · by_contra hc
      exact absurd h1 (not_lt.mpr (mul_nonneg hk.le (not_lt.mp hc)))
  · intro h
    exact Or.inr ⟨mul_neg_of_pos_of_neg hk h, hr2⟩

theorem force_eq_zero_iff {k q₁ q₂ r : ℝ} (hk : 0 < k) (hr : 0 < r) :
    F k q₁ q₂ r = 0 ↔ q₁ = 0 ∨ q₂ = 0 := by
  have hr2 : r ^ 2 ≠ 0 := by positivity
  unfold F
  rw [div_eq_zero_iff, mul_assoc, mul_eq_zero, mul_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact absurd h hk.ne'
    · exact h
    · exact absurd h hr2
  · rintro (h | h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))

theorem force_charge_conj (k q₁ q₂ r : ℝ) : F k (-q₁) (-q₂) r = F k q₁ q₂ r := by
  unfold F; ring

theorem force_flip_left (k q₁ q₂ r : ℝ) : F k (-q₁) q₂ r = -F k q₁ q₂ r := by
  unfold F; ring

theorem force_flip_right (k q₁ q₂ r : ℝ) : F k q₁ (-q₂) r = -F k q₁ q₂ r := by
  unfold F; ring

theorem force_r_refl (k q₁ q₂ r : ℝ) : F k q₁ q₂ r = F k q₁ q₂ r := rfl

theorem force_scale (k q₁ q₂ r c : ℝ) : F k q₁ q₂ (c * r) = F k q₁ q₂ r / c ^ 2 := by
  unfold F
  rw [mul_pow, div_div, mul_comm (c ^ 2)]

theorem force_double (k q₁ q₂ r : ℝ) : F k q₁ q₂ (2 * r) = F k q₁ q₂ r / 4 := by
  rw [force_scale]; norm_num

end CoulombSignB
