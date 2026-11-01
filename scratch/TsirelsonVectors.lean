import Mathlib

/-!
# Correlations made by rotating directions stop at 2√2

Tsirelson (1980): ±1-valued quantum correlations are exactly `E(x, y) = ⟪u_x, v_y⟫` for unit vectors in a real
inner-product space. Each setting is a DIRECTION, and correlation is the cosine between directions.

* T1 `rotation_correlations_tsirelson`: for unit vectors `u₀ u₁ v₀ v₁`,
  `|⟪u₀,v₀⟫ + ⟪u₀,v₁⟫ + ⟪u₁,v₀⟫ − ⟪u₁,v₁⟫| ≤ 2√2`.
* T2 `pr_box_is_not_a_rotation`: no unit vectors give the PR box (CHSH = 4).

Together with EchoesAndBounds (Q2: shared seeds ≤ 2; Q3: 2√2 attained; Q4: postselection reaches 4), quantum is
exactly what selection becomes when every correlation must be an inner product of directions.
-/

namespace TsirelsonVectors

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- **T1.** -/
theorem rotation_correlations_tsirelson (u₀ u₁ v₀ v₁ : V) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) (hv₀ : ‖v₀‖ = 1)
    (hv₁ : ‖v₁‖ = 1) : |⟪u₀, v₀⟫ + ⟪u₀, v₁⟫ + ⟪u₁, v₀⟫ - ⟪u₁, v₁⟫| ≤ 2 * √2 := by
  have e : ⟪u₀, v₀⟫ + ⟪u₀, v₁⟫ + ⟪u₁, v₀⟫ - ⟪u₁, v₁⟫ = ⟪u₀, v₀ + v₁⟫ + ⟪u₁, v₀ - v₁⟫ := by
    rw [inner_add_right, inner_sub_right]; ring
  have h1 : |⟪u₀, v₀ + v₁⟫| ≤ ‖v₀ + v₁‖ := by
    have := abs_real_inner_le_norm u₀ (v₀ + v₁); rwa [hu₀, one_mul] at this
  have h2 : |⟪u₁, v₀ - v₁⟫| ≤ ‖v₀ - v₁‖ := by
    have := abs_real_inner_le_norm u₁ (v₀ - v₁); rwa [hu₁, one_mul] at this
  have par : ‖v₀ + v₁‖ ^ 2 + ‖v₀ - v₁‖ ^ 2 = 4 := by
    rw [norm_add_sq_real, norm_sub_sq_real, hv₀, hv₁]; ring
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hab : ‖v₀ + v₁‖ + ‖v₀ - v₁‖ ≤ 2 * √2 := by
    nlinarith [sq_nonneg (‖v₀ + v₁‖ - ‖v₀ - v₁‖), norm_nonneg (v₀ + v₁), norm_nonneg (v₀ - v₁),
      Real.sqrt_nonneg 2]
  rw [e]
  calc |⟪u₀, v₀ + v₁⟫ + ⟪u₁, v₀ - v₁⟫| ≤ |⟪u₀, v₀ + v₁⟫| + |⟪u₁, v₀ - v₁⟫| := abs_add_le _ _
    _ ≤ ‖v₀ + v₁‖ + ‖v₀ - v₁‖ := add_le_add h1 h2
    _ ≤ 2 * √2 := hab

/-- **T2.** -/
theorem pr_box_is_not_a_rotation (u₀ u₁ v₀ v₁ : V) (hu₀ : ‖u₀‖ = 1) (hu₁ : ‖u₁‖ = 1) (hv₀ : ‖v₀‖ = 1)
    (hv₁ : ‖v₁‖ = 1) : ⟪u₀, v₀⟫ + ⟪u₀, v₁⟫ + ⟪u₁, v₀⟫ - ⟪u₁, v₁⟫ ≠ 4 := by
  intro h
  have := rotation_correlations_tsirelson u₀ u₁ v₀ v₁ hu₀ hu₁ hv₀ hv₁
  rw [h, abs_of_pos (by norm_num : (0:ℝ) < 4)] at this
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

end TsirelsonVectors
