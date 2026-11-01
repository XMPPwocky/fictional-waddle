import Mathlib

/-!
# Quaternion units, the group Q8, and the double cover

PROVED:
* `i_mul_j`, `j_mul_i`, `i_mul_j_ne_j_mul_i`: in `ℍ[ℝ]`, `i * j = k`, `j * i = -k`, hence `i * j ≠ j * i`.
* `i_mul_i`, `j_mul_j`, `k_mul_k`, `i_mul_j_mul_k`: `i² = j² = k² = i * j * k = -1`.
* `q8_not_commutative`: `QuaternionGroup 2` (the quaternion group Q8) is non-commutative:
  there exist `a b` with `a * b ≠ b * a`; also `q8_card : Fintype.card (QuaternionGroup 2) = 8`.
* `unit_inv_eq_star`: for `‖q‖ = 1`, `q⁻¹ = star q`.
* `conj_neg`: for any unit quaternion `q` and pure-imaginary `v` (`v.re = 0`),
  `q * v * q⁻¹ = (-q) * v * (-q)⁻¹` (the hypotheses are not needed for the identity itself).
* `conj_pure`: for `‖q‖ = 1` and `v.re = 0`, `(q * v * q⁻¹).re = 0` (the conjugation acts on
  pure-imaginary quaternions).
* `rotI_norm`: `‖rotI θ‖ = 1`, where `rotI θ = cos(θ/2) + sin(θ/2) i`.
* `rotI_two_pi`: `rotI (2π) = -1`; `rotI_four_pi`: `rotI (4π) = 1`; `rotI_two_pi_ne_one`.

INTERPRETED:
* `conj_neg` is the statement that `q` and `-q` induce the same rotation `v ↦ q v q⁻¹` of the
  pure-imaginary quaternions (ℝ³), i.e. the map from unit quaternions to rotations is at
  least two-to-one.
* `rotI θ` is the unit quaternion of the rotation by angle `θ` about the `i` axis; one full
  turn (`θ = 2π`) gives `-1`, two full turns (`θ = 4π`) return to `1`.
-/

namespace QuaternionDoubleCoverB

open Quaternion

/-- The standard unit `i`. -/
def qi : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
/-- The standard unit `j`. -/
def qj : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
/-- The standard unit `k`. -/
def qk : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

theorem i_mul_j : qi * qj = qk := by
  ext <;> simp [qi, qj, qk]

theorem j_mul_i : qj * qi = -qk := by
  ext <;> simp [qi, qj, qk]

theorem i_mul_j_ne_j_mul_i : qi * qj ≠ qj * qi := by
  rw [i_mul_j, j_mul_i]
  intro h
  have := congrArg (fun x : ℍ[ℝ] => x.imK) h
  simp [qk] at this
  linarith

theorem i_mul_i : qi * qi = -1 := by
  ext <;> simp [qi]

theorem j_mul_j : qj * qj = -1 := by
  ext <;> simp [qj]

theorem k_mul_k : qk * qk = -1 := by
  ext <;> simp [qk]

theorem i_mul_j_mul_k : qi * qj * qk = -1 := by
  rw [i_mul_j, k_mul_k]

theorem q8_card : Fintype.card (QuaternionGroup 2) = 8 := by
  rw [QuaternionGroup.card]

theorem q8_not_commutative :
    ∃ a b : QuaternionGroup 2, a * b ≠ b * a :=
  ⟨QuaternionGroup.a 1, QuaternionGroup.xa 0, by decide⟩

theorem unit_inv_eq_star (q : ℍ[ℝ]) (hq : ‖q‖ = 1) : q⁻¹ = star q := by
  have h1 : normSq q = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hq, mul_one]
  rw [Quaternion.inv_def, h1]
  simp

theorem conj_neg (q v : ℍ[ℝ]) (_hq : ‖q‖ = 1) (_hv : v.re = 0) :
    q * v * q⁻¹ = (-q) * v * (-q)⁻¹ := by
  rw [inv_neg, neg_mul, mul_neg, neg_mul, neg_neg]

theorem conj_pure (q v : ℍ[ℝ]) (hq : ‖q‖ = 1) (hv : v.re = 0) :
    (q * v * q⁻¹).re = 0 := by
  rw [unit_inv_eq_star q hq]
  have h1 : normSq q = 1 := by
    have := Quaternion.normSq_eq_norm_mul_self q
    rw [hq] at this; simpa using this
  rw [Quaternion.normSq_def'] at h1
  simp [hv]
  ring

/-- The unit quaternion of the rotation by angle `θ` about the `i` axis. -/
noncomputable def rotI (θ : ℝ) : ℍ[ℝ] :=
  (Real.cos (θ / 2) : ℍ[ℝ]) + (Real.sin (θ / 2) : ℍ[ℝ]) * qi

theorem rotI_components (θ : ℝ) :
    rotI θ = ⟨Real.cos (θ / 2), Real.sin (θ / 2), 0, 0⟩ := by
  ext <;> simp [rotI, qi]

theorem rotI_norm (θ : ℝ) : ‖rotI θ‖ = 1 := by
  have h : normSq (rotI θ) = 1 := by
    rw [rotI_components, Quaternion.normSq_def']
    simp only
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have h2 := Quaternion.normSq_eq_norm_mul_self (rotI θ)
  rw [h] at h2
  have h3 : 0 ≤ ‖rotI θ‖ := norm_nonneg _
  nlinarith [h2, h3]

theorem rotI_two_pi : rotI (2 * Real.pi) = -1 := by
  rw [rotI_components]
  have : 2 * Real.pi / 2 = Real.pi := by ring
  rw [this, Real.cos_pi, Real.sin_pi]
  ext <;> simp

theorem rotI_four_pi : rotI (4 * Real.pi) = 1 := by
  rw [rotI_components]
  have : 4 * Real.pi / 2 = 2 * Real.pi := by ring
  rw [this, Real.cos_two_pi, Real.sin_two_pi]
  ext <;> simp

theorem rotI_two_pi_ne_one : rotI (2 * Real.pi) ≠ 1 := by
  rw [rotI_two_pi]
  intro h
  have := congrArg (fun x : ℍ[ℝ] => x.re) h
  simp at this
  linarith

end QuaternionDoubleCoverB
