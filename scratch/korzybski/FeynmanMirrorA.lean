import Mathlib

/-!
# FeynmanMirrorA

3×3 real matrices. `M = diag(1, 1, -1)` (mirror in the xy-plane, reversing z),
`L = diag(-1, 1, 1)` (left/right reversal, x axis), `Rπ = diag(-1, 1, -1)`
(rotation by π about the y axis).

PROVED:
* `mirror_eq_swap_mul_turn` : `M = L * Rπ`.
* `det_M`, `det_L`, `det_Rπ` : `det M = -1`, `det L = -1`, `det Rπ = 1`.
* `Rπ_orthogonal`, `Rπ_proper_rotation` : `Rπᵀ * Rπ = 1`, and together with `det Rπ = 1`,
  `Rπ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ`.
* `det_one_ne_M_and_L` : every matrix `A` with `det A = 1` satisfies `A ≠ M ∧ A ≠ L`.
* `M_mul_M`, `L_mul_L` : `M * M = 1`, `L * L = 1`.

INTERPRETED:
* "M is a left/right swap followed by turning around": `M = L * Rπ`, i.e. apply `Rπ` to a
  column vector first and then `L` (both are diagonal, so the order does not matter here).
* "Orientation reversal cannot be produced by any rotation" is formalized in the stronger
  form stated in the target: no matrix of determinant 1 (orthogonal or not) equals `M` or `L`.
-/

namespace FeynmanMirrorA

open Matrix

/-- Front/back mirror: reverses the z axis. -/
noncomputable def M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 1, -1]

/-- Left/right reversal: reverses the x axis. -/
noncomputable def L : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![-1, 1, 1]

/-- Rotation by π about the vertical y axis. -/
noncomputable def Rπ : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![-1, 1, -1]

theorem mirror_eq_swap_mul_turn : M = L * Rπ := by
  unfold M L Rπ
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

theorem det_M : M.det = -1 := by
  unfold M
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp

theorem det_L : L.det = -1 := by
  unfold L
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp

theorem det_Rπ : Rπ.det = 1 := by
  unfold Rπ
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp

theorem Rπ_orthogonal : Rπᵀ * Rπ = 1 := by
  unfold Rπ
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem Rπ_proper_rotation :
    Rπᵀ * Rπ = 1 ∧ Rπ.det = 1 ∧ Rπ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  refine ⟨Rπ_orthogonal, det_Rπ, ?_⟩
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, det_Rπ⟩
  rw [Matrix.mem_orthogonalGroup_iff']
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    using Rπ_orthogonal

theorem det_one_ne_M_and_L (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.det = 1) :
    A ≠ M ∧ A ≠ L := by
  constructor
  · rintro rfl
    rw [det_M] at hA
    norm_num at hA
  · rintro rfl
    rw [det_L] at hA
    norm_num at hA

theorem M_mul_M : M * M = 1 := by
  unfold M
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem L_mul_L : L * L = 1 := by
  unfold L
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

end FeynmanMirrorA
