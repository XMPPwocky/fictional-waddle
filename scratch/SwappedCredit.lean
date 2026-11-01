import Mathlib

/-!
# Optimizing each other's objective time-reverses the rotation

Two players, `x ∈ ℝᵐ`, `y ∈ ℝⁿ`, losses `L₁ L₂`. Hessian blocks at a point:
- `A₁ = ∂ₓₓL₁`, `B₁ = ∂ₓᵧL₁`, `D₁ = ∂ᵧᵧL₁`, and likewise `A₂, B₂, D₂`;
- `∂ᵧₓL = (∂ₓᵧL)ᵀ`, with `A, D` symmetric (Schwarz).

The Jacobians of the learning fields are:
- Selfish (each descends its OWN loss): `J  = −[[A₁, B₁], [B₂ᵀ, D₂]]`.
- Swapped (each descends the OTHER's loss, "optimizing each other's feature detectors"): `J' = −[[A₂, B₂], [B₁ᵀ, D₁]]`.
- Good (each descends the TOTAL): `Jg = −[[A₁+A₂, B₁+B₂], [(B₁+B₂)ᵀ, D₁+D₂]]`.

* X1 `swap_reverses_rotation`: `J' − J'ᵀ = −(J − Jᵀ)`. The rotational (antisymmetric, CoCo-K) part is exactly negated.
* X2 `good_has_no_rotation`: `Jg = Jgᵀ`. Total credit is a pure gradient flow.
* X3 `good_is_selfish_plus_swapped`: `Jg = J + J'`. So the Good field is the selfish field plus its rotation-reversed
  twin, and the rotations cancel.
-/

namespace SwappedCredit

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n]


/-- **X1.** -/
theorem swap_reverses_rotation (A₁ A₂ : Matrix m m ℝ) (D₁ D₂ : Matrix n n ℝ) (B₁ B₂ : Matrix m n ℝ)
    (hA₁ : A₁ᵀ = A₁) (hA₂ : A₂ᵀ = A₂) (hD₁ : D₁ᵀ = D₁) (hD₂ : D₂ᵀ = D₂) :
    let J := -fromBlocks A₁ B₁ B₂ᵀ D₂
    let J' := -fromBlocks A₂ B₂ B₁ᵀ D₁
    J' - J'ᵀ = -(J - Jᵀ) := by
  intro J J'
  simp only [J, J', fromBlocks_neg, fromBlocks_transpose, transpose_neg, transpose_transpose, hA₁, hA₂, hD₁, hD₂,
    sub_eq_add_neg, fromBlocks_add]
  congr 1 <;> abel

/-- **X2.** -/
theorem good_has_no_rotation (A₁ A₂ : Matrix m m ℝ) (D₁ D₂ : Matrix n n ℝ) (B₁ B₂ : Matrix m n ℝ)
    (hA₁ : A₁ᵀ = A₁) (hA₂ : A₂ᵀ = A₂) (hD₁ : D₁ᵀ = D₁) (hD₂ : D₂ᵀ = D₂) :
    let Jg := -fromBlocks (A₁ + A₂) (B₁ + B₂) (B₁ + B₂)ᵀ (D₁ + D₂)
    Jgᵀ = Jg := by
  intro Jg
  simp only [Jg, transpose_neg, fromBlocks_transpose, transpose_transpose, transpose_add, hA₁, hA₂, hD₁, hD₂]

/-- **X3.** -/
theorem good_is_selfish_plus_swapped (A₁ A₂ : Matrix m m ℝ) (D₁ D₂ : Matrix n n ℝ) (B₁ B₂ : Matrix m n ℝ) :
    -fromBlocks (A₁ + A₂) (B₁ + B₂) (B₁ + B₂)ᵀ (D₁ + D₂)
      = -fromBlocks A₁ B₁ B₂ᵀ D₂ + -fromBlocks A₂ B₂ B₁ᵀ D₁ := by
  rw [fromBlocks_neg, fromBlocks_neg, fromBlocks_neg, fromBlocks_add, transpose_add]
  congr 1 <;> abel

end SwappedCredit
