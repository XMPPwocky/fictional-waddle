import Mathlib

/-!
# RoPE relative-position identity

PROVED
* `R_transpose_mul`: for all angles `θ φ`, `R(θ)ᵀ * R(φ) = R(φ - θ)`.
* `R_zero`: `R(0) = 1`.
* `R_transpose_mul_self`: `R(θ)ᵀ * R(θ) = 1`.
* `R_mul_transpose_self`: `R(θ) * R(θ)ᵀ = 1`.
* `R_mem_orthogonalGroup`: `R(θ)` lies in the orthogonal group of `Fin 2`.
* `Rot_transpose_mul`: for the block-diagonal rotation
  `Rot ω m = blockDiagonal (fun i => R (m * ω i))` on `Fin 2 × Fin k`,
  `(Rot ω m)ᵀ * Rot ω n = Rot ω (n - m)`.
* `Rot_zero`: `Rot ω 0 = 1`.
* `Rot_transpose_mul_self`: `(Rot ω m)ᵀ * Rot ω m = 1`.
* `Rot_mul_transpose_self`: `Rot ω m * (Rot ω m)ᵀ = 1`.
* `Rot_mem_orthogonalGroup`: `Rot ω m` lies in the orthogonal group of `Fin 2 × Fin k`.
* `score_eq`: for all vectors `q key`,
  `(Rot ω m *ᵥ q) ⬝ᵥ (Rot ω n *ᵥ key) = q ⬝ᵥ (Rot ω (n - m) *ᵥ key)`.
* `score_relative`: if `n - m = n' - m'` then
  `(Rot ω m *ᵥ q) ⬝ᵥ (Rot ω n *ᵥ key) = (Rot ω m' *ᵥ q) ⬝ᵥ (Rot ω n' *ᵥ key)`,
  i.e. the score depends on the positions only through `n - m`.
-/

namespace RopeRelativePosition

open Matrix Real

/-- The planar rotation by angle `θ`. -/
noncomputable def R (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos θ, -sin θ; sin θ, cos θ]

theorem R_transpose_mul (θ φ : ℝ) : (R θ)ᵀ * R φ = R (φ - θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R, Matrix.mul_apply, Fin.sum_univ_two, cos_sub, sin_sub] <;> ring

theorem R_zero : R 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R]

theorem R_transpose_mul_self (θ : ℝ) : (R θ)ᵀ * R θ = 1 := by
  rw [R_transpose_mul, sub_self, R_zero]

theorem R_mul_transpose_self (θ : ℝ) : R θ * (R θ)ᵀ = 1 :=
  mul_eq_one_comm.mp (R_transpose_mul_self θ)

theorem R_mem_orthogonalGroup (θ : ℝ) : R θ ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  exact R_mul_transpose_self θ

/-- The block-diagonal RoPE rotation at position `m` with frequencies `ω`. -/
noncomputable def Rot {k : ℕ} (ω : Fin k → ℝ) (m : ℝ) :
    Matrix (Fin 2 × Fin k) (Fin 2 × Fin k) ℝ :=
  Matrix.blockDiagonal (fun i => R (m * ω i))

theorem Rot_transpose_mul {k : ℕ} (ω : Fin k → ℝ) (m n : ℝ) :
    (Rot ω m)ᵀ * Rot ω n = Rot ω (n - m) := by
  unfold Rot
  rw [Matrix.blockDiagonal_transpose, ← Matrix.blockDiagonal_mul]
  congr 1
  funext i
  rw [R_transpose_mul, sub_mul]

theorem Rot_zero {k : ℕ} (ω : Fin k → ℝ) : Rot ω 0 = 1 := by
  unfold Rot
  simp only [zero_mul, R_zero]
  exact Matrix.blockDiagonal_one

theorem Rot_transpose_mul_self {k : ℕ} (ω : Fin k → ℝ) (m : ℝ) :
    (Rot ω m)ᵀ * Rot ω m = 1 := by
  rw [Rot_transpose_mul, sub_self, Rot_zero]

theorem Rot_mul_transpose_self {k : ℕ} (ω : Fin k → ℝ) (m : ℝ) :
    Rot ω m * (Rot ω m)ᵀ = 1 :=
  mul_eq_one_comm.mp (Rot_transpose_mul_self ω m)

theorem Rot_mem_orthogonalGroup {k : ℕ} (ω : Fin k → ℝ) (m : ℝ) :
    Rot ω m ∈ Matrix.orthogonalGroup (Fin 2 × Fin k) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  exact Rot_mul_transpose_self ω m

theorem score_eq {k : ℕ} (ω : Fin k → ℝ) (m n : ℝ) (q key : Fin 2 × Fin k → ℝ) :
    (Rot ω m *ᵥ q) ⬝ᵥ (Rot ω n *ᵥ key) = q ⬝ᵥ (Rot ω (n - m) *ᵥ key) := by
  rw [← Rot_transpose_mul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec q (Rot ω m)ᵀ,
    Matrix.vecMul_transpose]

theorem score_relative {k : ℕ} (ω : Fin k → ℝ) (m n m' n' : ℝ)
    (h : n - m = n' - m') (q key : Fin 2 × Fin k → ℝ) :
    (Rot ω m *ᵥ q) ⬝ᵥ (Rot ω n *ᵥ key) = (Rot ω m' *ᵥ q) ⬝ᵥ (Rot ω n' *ᵥ key) := by
  rw [score_eq, score_eq, h]

end RopeRelativePosition
