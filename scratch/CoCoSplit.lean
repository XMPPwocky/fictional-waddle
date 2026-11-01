import Mathlib

/-!
# CoCo = trades + selection

Kalai & Kalai's CoCo decomposition splits a two-player game `(A, B)` into a team game `((A+B)/2, (A+B)/2)` (cooperative)
and a zero-sum game `((A−B)/2, −(A−B)/2)` (competitive). The learning dynamics of a bilinear game has Jacobian
`J = [[0, A], [Bᵀ, 0]]` (player 1's gradient `A y`, player 2's `Bᵀ x`).

* K1 `coco_is_jacobian_split`: `J = S + K`, where `S` is exactly the team game's Jacobian and is symmetric (selection:
  a common potential, gradient flow), and `K` is exactly the zero-sum game's Jacobian and is antisymmetric (trades:
  Hamiltonian, conserving).
* K2 `sym_antisym_unique`: such a split is unique. CoCo's split and the Jacobian's split are the same object.
-/

open Matrix

namespace CoCoSplit

variable {n m : Type*}

/-- **K1.** For a bilinear two-player game, CoCo's team part is the symmetric part of the learning Jacobian and its
zero-sum part is the antisymmetric part. -/
theorem coco_is_jacobian_split (A B : Matrix n m ℝ) :
    fromBlocks (0 : Matrix n n ℝ) A Bᵀ (0 : Matrix m m ℝ)
        = fromBlocks 0 ((1 / 2 : ℝ) • (A + B)) ((1 / 2 : ℝ) • (A + B))ᵀ 0
          + fromBlocks 0 ((1 / 2 : ℝ) • (A - B)) (-((1 / 2 : ℝ) • (A - B))ᵀ) 0 ∧
      (fromBlocks (0 : Matrix n n ℝ) ((1 / 2 : ℝ) • (A + B)) ((1 / 2 : ℝ) • (A + B))ᵀ (0 : Matrix m m ℝ))ᵀ
        = fromBlocks 0 ((1 / 2 : ℝ) • (A + B)) ((1 / 2 : ℝ) • (A + B))ᵀ 0 ∧
      (fromBlocks (0 : Matrix n n ℝ) ((1 / 2 : ℝ) • (A - B)) (-((1 / 2 : ℝ) • (A - B))ᵀ) (0 : Matrix m m ℝ))ᵀ
        = -fromBlocks 0 ((1 / 2 : ℝ) • (A - B)) (-((1 / 2 : ℝ) • (A - B))ᵀ) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [fromBlocks_add]
    congr 1 <;> ext i j <;> simp [transpose_apply] <;> ring
  · rw [fromBlocks_transpose]; simp
  · rw [fromBlocks_transpose, fromBlocks_neg]; simp

/-- **K2.** A split of a square matrix into symmetric plus antisymmetric is unique: the symmetric part is `(J + Jᵀ)/2`. -/
theorem sym_antisym_unique {ι : Type*} (J S K : Matrix ι ι ℝ) (hJ : J = S + K) (hS : Sᵀ = S) (hK : Kᵀ = -K) :
    S = (1 / 2 : ℝ) • (J + Jᵀ) := by
  have hT : Jᵀ = S - K := by rw [hJ, transpose_add, hS, hK, sub_eq_add_neg]
  rw [hT, hJ]
  ext i j
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  ring

end CoCoSplit
