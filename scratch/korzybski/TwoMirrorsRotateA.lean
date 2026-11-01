import Mathlib

/-!
# Two mirrors compose to a rotation

PROVED:
* `ref_mul_ref`  : `Ref α * Ref β = Rot (2 * (α - β))`.
* `ref_mul_self` : `Ref θ * Ref θ = 1`.
* `det_ref`      : `(Ref θ).det = -1`.
* `det_rot`      : `(Rot φ).det = 1`.
* `rot_mul_ref`  : `Rot φ * Ref θ = Ref (θ + φ / 2)`.

INTERPRETED:
* `Ref θ` is the matrix of the reflection of `ℝ²` across the line through the origin
  at angle `θ`, namely `[[cos 2θ, sin 2θ], [sin 2θ, -cos 2θ]]`.
* `Rot φ` is the matrix of the rotation by `φ`, namely `[[cos φ, -sin φ], [sin φ, cos φ]]`.
-/

namespace TwoMirrorsRotateA

open Real Matrix

/-- Reflection across the line through the origin at angle `θ`. -/
noncomputable def Ref (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos (2 * θ), sin (2 * θ); sin (2 * θ), -cos (2 * θ)]

/-- Rotation by angle `φ`. -/
noncomputable def Rot (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos φ, -sin φ; sin φ, cos φ]

theorem ref_mul_ref (α β : ℝ) : Ref α * Ref β = Rot (2 * (α - β)) := by
  have hc : cos (2 * (α - β)) = cos (2 * α) * cos (2 * β) + sin (2 * α) * sin (2 * β) := by
    rw [mul_sub, Real.cos_sub]
  have hs : sin (2 * (α - β)) = sin (2 * α) * cos (2 * β) - cos (2 * α) * sin (2 * β) := by
    rw [mul_sub, Real.sin_sub]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ref, Rot, Matrix.mul_apply, Fin.sum_univ_two, hc, hs] <;> ring

theorem ref_mul_self (θ : ℝ) : Ref θ * Ref θ = 1 := by
  have h := Real.sin_sq_add_cos_sq (2 * θ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ref, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [h]

theorem det_ref (θ : ℝ) : (Ref θ).det = -1 := by
  have h := Real.sin_sq_add_cos_sq (2 * θ)
  simp [Ref, Matrix.det_fin_two]
  nlinarith [h]

theorem det_rot (φ : ℝ) : (Rot φ).det = 1 := by
  have h := Real.sin_sq_add_cos_sq φ
  simp [Rot, Matrix.det_fin_two]
  nlinarith [h]

theorem rot_mul_ref (φ θ : ℝ) : Rot φ * Ref θ = Ref (θ + φ / 2) := by
  have e : 2 * (θ + φ / 2) = φ + 2 * θ := by ring
  have hc : cos (2 * (θ + φ / 2)) = cos φ * cos (2 * θ) - sin φ * sin (2 * θ) := by
    rw [e, Real.cos_add]
  have hs : sin (2 * (θ + φ / 2)) = sin φ * cos (2 * θ) + cos φ * sin (2 * θ) := by
    rw [e, Real.sin_add]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ref, Rot, Matrix.mul_apply, Fin.sum_univ_two, hc, hs] <;> ring

end TwoMirrorsRotateA
