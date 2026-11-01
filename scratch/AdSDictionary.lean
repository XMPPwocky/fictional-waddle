import Mathlib

/-!
# The parts of the AdS/CFT dictionary that are theorems

The correspondence itself is a conjecture. These are its kinematic entries.

* D1 `symmetry_count`: `AdS_{d+1}` has isometry group `SO(d, 2)`, of dimension `(d+2)(d+1)/2`. The conformal group
  of `d`-dimensional spacetime has `d` translations, `d(d−1)/2` Lorentz rotations, 1 dilation and `d` special
  conformal maps, the same number. (Stated as `2·(2d + 1) + d(d − 1) = (d + 1)(d + 2)`.)
* D2 `mass_dimension`: in Poincaré `AdS_{d+1}`, `ds² = (dz² + dx²)/z²`, the radial Klein–Gordon operator
  `z^{d+1} ∂_z (z^{1−d} ∂_z φ)` sends `φ = z^Δ` to `Δ(Δ − d) z^Δ`. A bulk field of mass `m` is dual to a boundary
  operator of dimension `Δ` with `m² = Δ(Δ − d)`.
* D3 `dimension_roots`: `Δ(Δ − d) = m²` iff `Δ = d/2 ± √(d²/4 + m²)`, given the Breitenlohner–Freedman bound
  `m² ≥ −d²/4`.
* D4 `bf_bound_needed`: below the bound, no real `Δ` exists.
-/

namespace AdSDictionary

open Real

/-- **D1.** -/
theorem symmetry_count (d : ℤ) : 2 * (2 * d + 1) + d * (d - 1) = (d + 1) * (d + 2) := by
  ring

/-- **D2.** -/
theorem mass_dimension (d Δ z : ℝ) (hz : 0 < z) :
    z ^ (d + 1) * deriv (fun w => w ^ (1 - d) * deriv (fun v => v ^ Δ) w) z = Δ * (Δ - d) * z ^ Δ := by
  have key : ∀ w : ℝ, 0 < w → w ^ (1 - d) * deriv (fun v => v ^ Δ) w = Δ * w ^ (Δ - d) := by
    intro w hw
    rw [Real.deriv_rpow_const w Δ]
    rw [show w ^ (1 - d) * (Δ * w ^ (Δ - 1)) = Δ * (w ^ (1 - d) * w ^ (Δ - 1)) by ring, ← Real.rpow_add hw]
    congr 2; ring
  have ev : (fun w => w ^ (1 - d) * deriv (fun v => v ^ Δ) w) =ᶠ[nhds z] (fun w => Δ * w ^ (Δ - d)) := by
    filter_upwards [Ioi_mem_nhds hz] with w hw using key w hw
  rw [ev.deriv_eq, deriv_const_mul _ (Real.differentiableAt_rpow_const_of_ne _ hz.ne'),
    Real.deriv_rpow_const z (Δ - d)]
  rw [show z ^ (d + 1) * (Δ * ((Δ - d) * z ^ (Δ - d - 1))) = Δ * (Δ - d) * (z ^ (d + 1) * z ^ (Δ - d - 1)) by ring,
    ← Real.rpow_add hz]
  congr 2; ring

/-- **D3.** -/
theorem dimension_roots (d m2 Δ : ℝ) (hbf : -(d ^ 2 / 4) ≤ m2) :
    Δ * (Δ - d) = m2 ↔ Δ = d / 2 + √(d ^ 2 / 4 + m2) ∨ Δ = d / 2 - √(d ^ 2 / 4 + m2) := by
  have hn : 0 ≤ d ^ 2 / 4 + m2 := by linarith
  have hs := Real.sq_sqrt hn
  constructor
  · intro h
    have : (Δ - d / 2) ^ 2 = (√(d ^ 2 / 4 + m2)) ^ 2 := by rw [hs]; nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h1 | h1
    · left; linarith
    · right; linarith
  · rintro (h | h) <;> subst h <;> nlinarith [hs]

/-- **D4.** -/
theorem bf_bound_needed (d m2 : ℝ) (h : m2 < -(d ^ 2 / 4)) : ¬ ∃ Δ : ℝ, Δ * (Δ - d) = m2 := by
  rintro ⟨Δ, h⟩
  nlinarith [sq_nonneg (Δ - d / 2)]

end AdSDictionary
