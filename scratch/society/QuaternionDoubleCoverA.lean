import Mathlib

/-!
# Quaternion units, Q8 non-commutativity, and the double cover

PROVED (Mathlib `ℍ[ℝ]` = `Quaternion ℝ`, units `i = ⟨0,1,0,0⟩`, `j = ⟨0,0,1,0⟩`, `k = ⟨0,0,0,1⟩`):
* `i_mul_j : i * j = k`, `j_mul_i : j * i = -k`, `i_mul_j_ne_j_mul_i : i * j ≠ j * i`.
* `i_mul_i`, `j_mul_j`, `k_mul_k` : the square of each unit is `-1`; `i_mul_j_mul_k : i * j * k = -1`.
* `quaternionGroup_not_comm` : in Mathlib's `QuaternionGroup 2` (the group Q8) there are `x y`
  with `x * y ≠ y * x`; `units_not_comm` : the same for `i, j` viewed in `ℍ[ℝ]ˣ`.
* `conj_neg_eq` : for `‖q‖ = 1` and `v` with `v.re = 0`, `q * v * q⁻¹ = (-q) * v * (-q)⁻¹`.
  (The proof does not use the hypotheses; they are kept to match the stated target.)
* `rot` θ := `↑(cos (θ/2)) + ↑(sin (θ/2)) * i`; `norm_rot : ‖rot θ‖ = 1`;
  `rot_two_pi : rot (2π) = -1`; `rot_four_pi : rot (4π) = 1`;
  `rot_conj_j : rot θ * j * (rot θ)⁻¹ = cos θ • j + sin θ • k` (conjugation by `rot θ`
  rotates the `j,k` plane by angle `θ`); `rot_conj_i` : it fixes `i`.
* `rot_add_two_pi : rot (θ + 2π) = -rot θ` and `rot_add_two_pi_conj` : both induce the same
  conjugation map on every `v`, so the angle-`θ` rotation has the two preimages `±rot θ`.

INTERPRETED:
* "the rotation by angle θ about the i axis" is the map `v ↦ rot θ * v * (rot θ)⁻¹` on pure
  imaginary quaternions; `rot_conj_j` and `rot_conj_i` justify that reading.
* "one full turn is −1, two turns return to 1" is `rot_two_pi` / `rot_four_pi`.
-/

namespace QuaternionDoubleCoverA

open Quaternion

/-- The unit `i`. -/
def i : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
/-- The unit `j`. -/
def j : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
/-- The unit `k`. -/
def k : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

theorem i_mul_j : i * j = k := by
  ext <;> simp [i, j, k]

theorem j_mul_i : j * i = -k := by
  ext <;> simp [i, j, k]

theorem i_mul_j_ne_j_mul_i : i * j ≠ j * i := by
  rw [i_mul_j, j_mul_i]
  intro h
  have := congrArg (fun q : ℍ[ℝ] => q.imK) h
  simp [k] at this
  norm_num at this

theorem i_mul_i : i * i = -1 := by
  ext <;> simp [i]

theorem j_mul_j : j * j = -1 := by
  ext <;> simp [j]

theorem k_mul_k : k * k = -1 := by
  ext <;> simp [k]

theorem i_mul_j_mul_k : i * j * k = -1 := by
  rw [i_mul_j, k_mul_k]

/-- Q8 (Mathlib `QuaternionGroup 2`) is non-commutative. -/
theorem quaternionGroup_not_comm :
    ∃ x y : QuaternionGroup 2, x * y ≠ y * x :=
  ⟨QuaternionGroup.a 1, QuaternionGroup.xa 0, by decide⟩

theorem norm_eq_one_of_normSq {q : ℍ[ℝ]} (h : normSq q = 1) : ‖q‖ = 1 := by
  rw [Quaternion.normSq_eq_norm_mul_self] at h
  rcases mul_self_eq_one_iff.mp h with h | h
  · exact h
  · linarith [norm_nonneg q]

theorem norm_i : ‖i‖ = 1 := by
  apply norm_eq_one_of_normSq
  simp [Quaternion.normSq_def', i]

theorem norm_j : ‖j‖ = 1 := by
  apply norm_eq_one_of_normSq
  simp [Quaternion.normSq_def', j]

/-- `i` and `j` as units of `ℍ[ℝ]` do not commute. -/
theorem units_not_comm :
    ∃ x y : ℍ[ℝ]ˣ, x * y ≠ y * x := by
  have hi : i ≠ 0 := fun h => by simpa [h] using norm_i
  have hj : j ≠ 0 := fun h => by simpa [h] using norm_j
  refine ⟨Units.mk0 i hi, Units.mk0 j hj, fun h => i_mul_j_ne_j_mul_i ?_⟩
  simpa using congrArg Units.val h

/-- Double cover: `q` and `-q` induce the same conjugation. -/
theorem conj_neg_eq (q v : ℍ[ℝ]) (_hq : ‖q‖ = 1) (_hv : v.re = 0) :
    q * v * q⁻¹ = (-q) * v * (-q)⁻¹ := by
  rw [inv_neg, neg_mul, mul_neg, neg_mul, neg_neg]

/-- The rotor for angle `θ` about the `i` axis. -/
noncomputable def rot (θ : ℝ) : ℍ[ℝ] :=
  (Real.cos (θ / 2) : ℍ[ℝ]) + (Real.sin (θ / 2) : ℍ[ℝ]) * i

theorem rot_re (θ : ℝ) : (rot θ).re = Real.cos (θ / 2) := by simp [rot, i]
theorem rot_imI (θ : ℝ) : (rot θ).imI = Real.sin (θ / 2) := by simp [rot, i]
theorem rot_imJ (θ : ℝ) : (rot θ).imJ = 0 := by simp [rot, i]
theorem rot_imK (θ : ℝ) : (rot θ).imK = 0 := by simp [rot, i]

theorem normSq_rot (θ : ℝ) : normSq (rot θ) = 1 := by
  rw [Quaternion.normSq_def']
  simp only [rot_re, rot_imI, rot_imJ, rot_imK]
  nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]

theorem norm_rot (θ : ℝ) : ‖rot θ‖ = 1 :=
  norm_eq_one_of_normSq (normSq_rot θ)

theorem rot_two_pi : rot (2 * Real.pi) = -1 := by
  have : 2 * Real.pi / 2 = Real.pi := by ring
  ext <;> simp [rot_re, rot_imI, rot_imJ, rot_imK, this]

theorem rot_four_pi : rot (4 * Real.pi) = 1 := by
  have : 4 * Real.pi / 2 = 2 * Real.pi := by ring
  ext <;> simp [rot_re, rot_imI, rot_imJ, rot_imK, this]

theorem rot_zero : rot 0 = 1 := by
  ext <;> simp [rot_re, rot_imI, rot_imJ, rot_imK]

theorem rot_inv (θ : ℝ) : (rot θ)⁻¹ = star (rot θ) := by
  rw [Quaternion.inv_def, normSq_rot]
  simp

/-- Conjugation by `rot θ` rotates `j` by angle `θ` in the `j,k` plane. -/
theorem rot_conj_j (θ : ℝ) :
    rot θ * j * (rot θ)⁻¹ = Real.cos θ • j + Real.sin θ • k := by
  rw [rot_inv]
  have h1 : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  have h2 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have h3 := Real.sin_sq_add_cos_sq (θ / 2)
  ext <;> simp [rot_re, rot_imI, rot_imJ, rot_imK, j, k, h1, h2] <;> nlinarith [h3]

/-- Conjugation by `rot θ` fixes the axis `i`. -/
theorem rot_conj_i (θ : ℝ) : rot θ * i * (rot θ)⁻¹ = i := by
  rw [rot_inv]
  have h3 := Real.sin_sq_add_cos_sq (θ / 2)
  ext <;> simp [rot_re, rot_imI, rot_imJ, rot_imK, i] <;> nlinarith [h3]

theorem rot_add_two_pi (θ : ℝ) : rot (θ + 2 * Real.pi) = -rot θ := by
  have : (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi := by ring
  ext <;> simp [rot_re, rot_imI, rot_imJ, rot_imK, this, Real.cos_add_pi, Real.sin_add_pi]

theorem rot_add_two_pi_conj (θ : ℝ) (v : ℍ[ℝ]) :
    rot (θ + 2 * Real.pi) * v * (rot (θ + 2 * Real.pi))⁻¹ = rot θ * v * (rot θ)⁻¹ := by
  rw [rot_add_two_pi, inv_neg, neg_mul, mul_neg, neg_mul, neg_neg]

end QuaternionDoubleCoverA
