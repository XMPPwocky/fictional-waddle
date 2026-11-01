import Mathlib

/-!
# Another clock: real boosts MIX state and process, only `i` SWAPS them

In 1+1-D, an event `(t, x)` has interval `t² − x²`. A boost by rapidity `η` acts as
`(t, x) ↦ (t cosh η + x sinh η, t sinh η + x cosh η)`.

* Z1 `boost_preserves_interval`: the interval is invariant.
* Z2 `rest_worldline_is_your_motion`: the other clock's rest worldline `(τ, 0)` (its "object": just being there)
  becomes your motion `x = tanh η · t` (your "morphism").
* Z3 `boost_never_swaps`: no boost sends a timelike vector to a spacelike one. A real clock never fully swaps your
  objects and morphisms.
* Z4 `i_swaps_interval_sign`: `t ↦ i t` flips the sign of `t²` (Wick). Only the imaginary rotation swaps them fully,
  the same `i` as HolomorphicPair Y5.
-/

namespace ClockSwap

open Real

noncomputable def boost (η t x : ℝ) : ℝ × ℝ := (t * cosh η + x * sinh η, t * sinh η + x * cosh η)

/-- **Z1.** -/
theorem boost_preserves_interval (η t x : ℝ) : (boost η t x).1 ^ 2 - (boost η t x).2 ^ 2 = t ^ 2 - x ^ 2 := by
  simp only [boost]
  have := Real.cosh_sq_sub_sinh_sq η
  linear_combination (t ^ 2 - x ^ 2) * this

/-- **Z2.** -/
theorem rest_worldline_is_your_motion (η τ : ℝ) : (boost η τ 0).2 = tanh η * (boost η τ 0).1 := by
  simp only [boost, Real.tanh_eq_sinh_div_cosh]
  have := (Real.cosh_pos η).ne'
  field_simp
  ring

/-- **Z3.** -/
theorem boost_never_swaps (η t x : ℝ) (h : x ^ 2 < t ^ 2) : (boost η t x).2 ^ 2 < (boost η t x).1 ^ 2 := by
  have := boost_preserves_interval η t x
  linarith

/-- **Z4.** -/
theorem i_swaps_interval_sign (t : ℝ) : (Complex.I * t) ^ 2 = -((t : ℂ) ^ 2) := by
  rw [mul_pow, Complex.I_sq]; ring

end ClockSwap
