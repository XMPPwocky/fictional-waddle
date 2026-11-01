import Mathlib

/-!
# Sign rule for the Coulomb force

The Coulomb force along the line joining two point charges `q₁, q₂` at distance `r` is
`F = k q₁ q₂ / r²` with constant `k > 0`; positive `F` means repulsion.

PROVED:
* `force_pos_iff`   : for `k > 0`, `r > 0`: `0 < F ↔ 0 < q₁ q₂` (like charges repel).
* `force_neg_iff`   : for `k > 0`, `r > 0`: `F < 0 ↔ q₁ q₂ < 0` (opposite charges attract).
* `force_eq_zero_iff` : for `k > 0`, `r > 0`: `F = 0 ↔ q₁ = 0 ∨ q₂ = 0`.
* `force_charge_conj` : `F(−q₁, −q₂) = F(q₁, q₂)` (no hypotheses needed).
* `force_flip_left`, `force_flip_right` : flipping one charge negates `F` (no hypotheses).
* `force_r_refl`    : `F` at `r` equals `F` at `r` (the trivial invariance under `r ↦ r`).
* `force_double_r`  : `F(2r) = F(r)/4` (no hypotheses needed; at `r = 0` both sides are `0`
  under Lean's convention `x / 0 = 0`).
* `force_scale_r`   : more generally `F(c r) = F(r)/c²` for every real `c`.

INTERPRETED:
* "Repulsion" is the sign convention `F > 0`, "attraction" is `F < 0`; the force is the scalar
  component along the line joining the charges.
* Charge conjugation is the map `(q₁, q₂) ↦ (−q₁, −q₂)`; "invisible to the forces" is the
  equality of `F` before and after.
-/

namespace CoulombSignA

/-- Coulomb force along the joining line; positive means repulsion. -/
noncomputable def force (k q₁ q₂ r : ℝ) : ℝ := k * q₁ * q₂ / r ^ 2

lemma force_eq (k q₁ q₂ r : ℝ) : force k q₁ q₂ r = (k / r ^ 2) * (q₁ * q₂) := by
  unfold force; ring

lemma coeff_pos {k r : ℝ} (hk : 0 < k) (hr : 0 < r) : 0 < k / r ^ 2 := by
  positivity

theorem force_pos_iff {k q₁ q₂ r : ℝ} (hk : 0 < k) (hr : 0 < r) :
    0 < force k q₁ q₂ r ↔ 0 < q₁ * q₂ := by
  rw [force_eq]
  exact mul_pos_iff_of_pos_left (coeff_pos hk hr)

theorem force_neg_iff {k q₁ q₂ r : ℝ} (hk : 0 < k) (hr : 0 < r) :
    force k q₁ q₂ r < 0 ↔ q₁ * q₂ < 0 := by
  rw [force_eq]
  have h := coeff_pos hk hr
  constructor
  · intro hF
    by_contra hq
    push Not at hq
    have : 0 ≤ (k / r ^ 2) * (q₁ * q₂) := mul_nonneg h.le hq
    linarith
  · intro hq
    exact mul_neg_of_pos_of_neg h hq

theorem force_eq_zero_iff {k q₁ q₂ r : ℝ} (hk : 0 < k) (hr : 0 < r) :
    force k q₁ q₂ r = 0 ↔ q₁ = 0 ∨ q₂ = 0 := by
  rw [force_eq, mul_eq_zero, mul_eq_zero]
  have h := (coeff_pos hk hr).ne'
  simp [h]

theorem force_charge_conj (k q₁ q₂ r : ℝ) :
    force k (-q₁) (-q₂) r = force k q₁ q₂ r := by
  unfold force; ring

theorem force_flip_left (k q₁ q₂ r : ℝ) :
    force k (-q₁) q₂ r = -force k q₁ q₂ r := by
  unfold force; ring

theorem force_flip_right (k q₁ q₂ r : ℝ) :
    force k q₁ (-q₂) r = -force k q₁ q₂ r := by
  unfold force; ring

theorem force_r_refl (k q₁ q₂ r : ℝ) : force k q₁ q₂ r = force k q₁ q₂ r := rfl

theorem force_scale_r (k q₁ q₂ r c : ℝ) :
    force k q₁ q₂ (c * r) = force k q₁ q₂ r / c ^ 2 := by
  unfold force
  rw [mul_pow, div_div, mul_comm (c ^ 2)]

theorem force_double_r (k q₁ q₂ r : ℝ) :
    force k q₁ q₂ (2 * r) = force k q₁ q₂ r / 4 := by
  rw [force_scale_r]; norm_num

end CoulombSignA
