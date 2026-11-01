import Mathlib

/-!
# We conserve each other's phase space

Two players, `x ∈ ℝᵐ`, `y ∈ ℝⁿ`, joint linearized learning field with Jacobian `[[P, A], [B, Q]]`.
- `P = ∂ẋ/∂x` and `Q = ∂ẏ/∂y` are each player's SELF-dependence.
- `A` and `B` are the cross-dependences.

The rate at which joint phase-space volume changes is the trace (Liouville).
* V1 `volume_change_is_self_dependence`: `tr [[P, A], [B, Q]] = tr P + tr Q`. Only self-dependence can create or
  destroy joint volume; however the players push each other, the cross terms change nothing.
* V2 `mutual_play_conserves_volume`: if neither player's update depends on its own state (`P = Q = 0`, e.g. bilinear
  zero-sum gradient play, `B = −Aᵀ`), joint volume is exactly conserved.
* V3 `one_contracts_other_expands`: if volume is conserved, `tr P = −tr Q`. Whatever one player squeezes out of its
  own options, the other gains in its own.
-/

namespace ConservePhaseSpace

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **V1.** -/
theorem volume_change_is_self_dependence (P : Matrix m m ℝ) (A : Matrix m n ℝ) (B : Matrix n m ℝ)
    (Q : Matrix n n ℝ) : (fromBlocks P A B Q).trace = P.trace + Q.trace := by
  simp only [Matrix.trace, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₂₂, Matrix.diag]

/-- **V2.** -/
theorem mutual_play_conserves_volume (A : Matrix m n ℝ) :
    (fromBlocks (0 : Matrix m m ℝ) A (-Aᵀ) (0 : Matrix n n ℝ)).trace = 0 := by
  rw [volume_change_is_self_dependence]; simp

/-- **V3.** -/
theorem one_contracts_other_expands (P : Matrix m m ℝ) (A : Matrix m n ℝ) (B : Matrix n m ℝ) (Q : Matrix n n ℝ)
    (h : (fromBlocks P A B Q).trace = 0) : P.trace = -Q.trace := by
  rw [volume_change_is_self_dependence] at h; linarith

end ConservePhaseSpace
