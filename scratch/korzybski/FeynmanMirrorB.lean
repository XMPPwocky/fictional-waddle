import Mathlib

/-!
# FeynmanMirrorB

3×3 real matrices: `M = diag(1, 1, -1)` (mirror in the xy-plane, reversing z),
`L = diag(-1, 1, 1)` (left/right reversal, x axis), `Rπ = diag(-1, 1, -1)`
(rotation by π about the y axis).

PROVED
* `mirror_eq_swap_mul_turn` : `M = L * Rπ`.
* `det_M`, `det_L`, `det_Rπ` : `det M = -1`, `det L = -1`, `det Rπ = 1`.
* `Rπ_orthogonal`, `Rπ_proper_rotation` : `Rπᵀ * Rπ = 1`, and with `det Rπ = 1`
  it lies in `Matrix.specialOrthogonalGroup (Fin 3) ℝ`.
* `det_one_ne_M_and_L` : every matrix `A` with `det A = 1` satisfies `A ≠ M` and `A ≠ L`.
* `M_mul_M`, `L_mul_L` : `M * M = 1`, `L * L = 1`.

INTERPRETED
* "Proper rotation" is read as membership in `SO(3)` = orthogonal with determinant 1.
* (4) is stated for all matrices of determinant 1, a superset of the rotations.
-/

namespace FeynmanMirrorB

open Matrix

/-- Front/back mirror: `diag(1, 1, -1)`. -/
def M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 1, -1]

/-- Left/right reversal: `diag(-1, 1, 1)`. -/
def L : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![-1, 1, 1]

/-- Rotation by π about the vertical y axis: `diag(-1, 1, -1)`. -/
def Rπ : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![-1, 1, -1]

/-- (1) A front/back mirror is a left/right swap composed with turning around. -/
theorem mirror_eq_swap_mul_turn : M = L * Rπ := by
  unfold M L Rπ
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

/-- (2a) -/
theorem det_M : M.det = -1 := by
  unfold M
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp

/-- (2b) -/
theorem det_L : L.det = -1 := by
  unfold L
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp

/-- (2c) -/
theorem det_Rπ : Rπ.det = 1 := by
  unfold Rπ
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp

/-- (3a) `Rπ` is orthogonal. -/
theorem Rπ_orthogonal : Rπᵀ * Rπ = 1 := by
  unfold Rπ
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

/-- (3b) `Rπ` is orthogonal with determinant 1, i.e. a proper rotation in `SO(3)`. -/
theorem Rπ_proper_rotation :
    Rπᵀ * Rπ = 1 ∧ Rπ.det = 1 ∧ Rπ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  refine ⟨Rπ_orthogonal, det_Rπ, ?_⟩
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, det_Rπ⟩
  rw [Matrix.mem_orthogonalGroup_iff]
  have h : Rπᵀ = Rπ := by
    unfold Rπ
    exact Matrix.diagonal_transpose _
  have h2 := Rπ_orthogonal
  rw [h] at h2
  simpa [Matrix.star_eq_conjTranspose, h] using h2

/-- (4) No matrix of determinant 1 equals `M` or `L`. -/
theorem det_one_ne_M_and_L (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.det = 1) :
    A ≠ M ∧ A ≠ L := by
  constructor
  · rintro rfl
    rw [det_M] at hA
    norm_num at hA
  · rintro rfl
    rw [det_L] at hA
    norm_num at hA

/-- (5a) -/
theorem M_mul_M : M * M = 1 := by
  unfold M
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

/-- (5b) -/
theorem L_mul_L : L * L = 1 := by
  unfold L
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

end FeynmanMirrorB
