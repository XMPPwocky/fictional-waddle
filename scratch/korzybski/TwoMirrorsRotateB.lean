import Mathlib

/-!
# Two mirrors compose to a rotation

PROVED:
* `ref_mul_ref`    : `Ref α * Ref β = Rot (2 * (α - β))`.
* `ref_mul_self`   : `Ref θ * Ref θ = 1`.
* `det_ref`        : `(Ref θ).det = -1`.
* `det_rot`        : `(Rot φ).det = 1`.
* `rot_mul_ref`    : `Rot φ * Ref θ = Ref (θ + φ / 2)`.

INTERPRETED:
* `Ref θ` is the matrix `[[cos 2θ, sin 2θ], [sin 2θ, -cos 2θ]]` of the reflection of `ℝ²`
  across the line through the origin at angle `θ`.
* `Rot φ` is the matrix `[[cos φ, -sin φ], [sin φ, cos φ]]` of the rotation by `φ`.
-/

namespace TwoMirrorsRotateB

open Matrix Real

/-- Reflection across the line through the origin at angle `θ`. -/
noncomputable def Ref (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos (2 * θ), sin (2 * θ); sin (2 * θ), -cos (2 * θ)]

/-- Rotation by angle `φ`. -/
noncomputable def Rot (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos φ, -sin φ; sin φ, cos φ]

theorem ref_mul_ref (α β : ℝ) : Ref α * Ref β = Rot (2 * (α - β)) := by
  have h : 2 * (α - β) = 2 * α - 2 * β := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ref, Rot, Matrix.mul_apply, Fin.sum_univ_two, h, Real.cos_sub, Real.sin_sub] <;> ring

theorem ref_mul_self (θ : ℝ) : Ref θ * Ref θ = 1 := by
  rw [ref_mul_ref, sub_self, mul_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rot]

theorem det_ref (θ : ℝ) : (Ref θ).det = -1 := by
  rw [Ref, Matrix.det_fin_two_of]
  have := Real.sin_sq_add_cos_sq (2 * θ)
  linear_combination -this

theorem det_rot (φ : ℝ) : (Rot φ).det = 1 := by
  rw [Rot, Matrix.det_fin_two_of]
  have := Real.sin_sq_add_cos_sq φ
  linear_combination this

theorem rot_mul_ref (φ θ : ℝ) : Rot φ * Ref θ = Ref (θ + φ / 2) := by
  have h : 2 * (θ + φ / 2) = φ + 2 * θ := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ref, Rot, Matrix.mul_apply, Fin.sum_univ_two, h, Real.cos_add, Real.sin_add] <;> ring

end TwoMirrorsRotateB
