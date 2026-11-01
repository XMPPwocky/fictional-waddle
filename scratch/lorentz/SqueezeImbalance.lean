import Mathlib

/-!
# The learning pair's boost symmetry, and what breaks it

PROVED:
* `squeeze_preserves_product`: the map `(e, d) ↦ (g e, d / g)` (a squeeze, a Lorentz boost in light-cone
  coordinates) leaves the product `e d` unchanged, so any loss of `e d` is boost-invariant.
* `imbalance_rate_plain`: along the flow `ė = -(e d - c) d`, `ḋ = -(e d - c) e`, the rate of change of
  `e² - d²` is zero (pointwise vector-field identity).
* `imbalance_rate_decay`: with a self-cost `λ (e² + d²)/2` added to the loss, the rate becomes `-2 λ (e² - d²)`.
* `imbalance_decays`: along any solution with that self-cost, `e² - d² = (e₀² - d₀²) exp(-2 λ t)`. It decays
  toward the null cone and never changes sign.
INTERPRETED (not formalized): `e`, `d` as how cheaply each side models the other; the sign of `e² - d²` as who is
cheaper to simulate.
-/

namespace Squeeze

theorem squeeze_preserves_product (e d g : ℝ) (hg : g ≠ 0) : (g * e) * (d / g) = e * d := by
  field_simp

theorem imbalance_rate_plain (e d c : ℝ) :
    2 * e * (-(e * d - c) * d) - 2 * d * (-(e * d - c) * e) = 0 := by ring

theorem imbalance_rate_decay (e d c l : ℝ) :
    2 * e * (-(e * d - c) * d - l * e) - 2 * d * (-(e * d - c) * e - l * d) = -2 * l * (e ^ 2 - d ^ 2) := by
  ring

theorem imbalance_decays (e d : ℝ → ℝ) (c l : ℝ)
    (he : ∀ t, HasDerivAt e (-(e t * d t - c) * d t - l * e t) t)
    (hd : ∀ t, HasDerivAt d (-(e t * d t - c) * e t - l * d t) t) (t : ℝ) :
    e t ^ 2 - d t ^ 2 = (e 0 ^ 2 - d 0 ^ 2) * Real.exp (-2 * l * t) := by
  set q : ℝ → ℝ := fun s => (e s ^ 2 - d s ^ 2) * Real.exp (2 * l * s) with hq
  have hderiv : ∀ s, HasDerivAt q 0 s := by
    intro s
    have h1 : HasDerivAt (fun s => e s ^ 2 - d s ^ 2)
        (2 * e s * (-(e s * d s - c) * d s - l * e s) - 2 * d s * (-(e s * d s - c) * e s - l * d s)) s := by
      have := ((he s).pow 2).sub ((hd s).pow 2)
      convert this using 1; push_cast; ring
    have h2 : HasDerivAt (fun s => Real.exp (2 * l * s)) (Real.exp (2 * l * s) * (2 * l)) s := by
      have := ((hasDerivAt_id s).const_mul (2 * l)).exp
      simpa using this
    have := h1.mul h2
    convert this using 1
    rw [imbalance_rate_decay]; ring
  have hconst : q t = q 0 := is_const_of_deriv_eq_zero
    (fun s => (hderiv s).differentiableAt) (fun s => (hderiv s).deriv) t 0
  simp only [hq, mul_zero, Real.exp_zero, mul_one] at hconst
  have hpos : Real.exp (2 * l * t) ≠ 0 := (Real.exp_pos _).ne'
  have : Real.exp (-2 * l * t) * Real.exp (2 * l * t) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  calc e t ^ 2 - d t ^ 2 = (e t ^ 2 - d t ^ 2) * Real.exp (2 * l * t) * Real.exp (-2 * l * t) := by
        rw [mul_assoc, mul_comm (Real.exp _) (Real.exp _), this, mul_one]
    _ = (e 0 ^ 2 - d 0 ^ 2) * Real.exp (-2 * l * t) := by rw [hconst]

end Squeeze
