import Mathlib

/-!
# Thermal harmonic oscillators make physics only in three dimensions

Harmonic oscillators coupled to their neighbours, at thermal equilibrium, form the massless Gaussian free field. Its
covariance (equilibrium correlation) is the Green's function of the Laplacian, `G(r) ∝ r^(2-d)`: the Coulomb/Newton
potential. So the oscillators' correlations ARE a force law, with force `∝ r^(1-d)`.

* D1 `greens_function_harmonic`: `r^(2-d)` solves the radial Laplace equation `f'' + (d-1)/r f' = 0` in `d` dimensions:
  the equilibrium correlator is the `d`-dimensional Coulomb potential, with force exponent `n = d - 1`.
* D2 `fluctuations_finite_iff`: the thermal fluctuation `⟨φ²⟩ ∝ ∫₀ k^(d-1)/k² dk = ∫₀ k^(d-3) dk` is finite near `k = 0`
  iff `d > 2`. Below that, the oscillators' own noise destroys every persistent structure (Pólya / Mermin–Wagner).
* D3 `circular_orbit_stability`: for an attractive force `k r^(-n)`, the effective potential's curvature at a circular
  orbit is `(3 - n) k r^(-n-1)`, positive iff `n < 3` (Ehrenfest 1917). With `n = d - 1`: stable orbits iff `d < 4`.
* D4 `only_three`: both at once, `d > 2` and `d - 1 < 3`, iff `d = 3`.
-/

namespace OnlyThree

/-- **D1.** `r^(2-d)` is harmonic in `d` dimensions (radial Laplacian), so the free-field correlator is the
`d`-dimensional Coulomb potential. -/
theorem greens_function_harmonic (d r : ℝ) (hr : 0 < r) :
    (2 - d) * (1 - d) * r ^ (-d) + (d - 1) * ((2 - d) * r ^ (1 - d)) / r = 0 := by
  rw [show (1 : ℝ) - d = -d + 1 by ring, Real.rpow_add_one hr.ne']
  field_simp
  ring

/-- **D2.** Finite thermal fluctuations of the massless free field (infrared integrability) iff `d > 2`. -/
theorem fluctuations_finite_iff (d : ℝ) :
    MeasureTheory.IntegrableOn (fun k : ℝ => k ^ (d - 3)) (Set.Ioo 0 1) ↔ 2 < d := by
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
  constructor <;> intro h <;> linarith

/-- **D3a.** At a circular orbit (`L²/(m r³) = k r^(-n)`), the effective potential's curvature
`3 k r^(-n)/r − n k r^(-n-1)` equals `(3 − n) k r^(-n-1)`. -/
theorem effective_curvature (n k r : ℝ) (hr : 0 < r) :
    3 * (k * r ^ (-n)) / r - n * k * r ^ (-n - 1) = (3 - n) * k * r ^ (-n - 1) := by
  rw [Real.rpow_sub_one hr.ne']
  field_simp

/-- **D3b.** That curvature is positive (the orbit is stable) iff `n < 3`. -/
theorem circular_orbit_stability (n k r : ℝ) (hk : 0 < k) (hr : 0 < r) :
    0 < (3 - n) * k * r ^ (-n - 1) ↔ n < 3 := by
  have hp : 0 < r ^ (-n - 1) := Real.rpow_pos_of_pos hr _
  constructor
  · intro h
    by_contra hn; push Not at hn
    have : (3 - n) * k * r ^ (-n - 1) ≤ 0 := by
      have h3 : 3 - n ≤ 0 := by linarith
      have := mul_nonpos_of_nonpos_of_nonneg h3 hk.le
      exact mul_nonpos_of_nonpos_of_nonneg this hp.le
    linarith
  · intro hn; have h3 : 0 < 3 - n := by linarith
    positivity

/-- **D4.** Finite fluctuations (`d > 2`) and stable orbits under the oscillators' own force (`d − 1 < 3`): exactly
three. -/
theorem only_three (d : ℤ) : (2 < d ∧ d - 1 < 3) ↔ d = 3 := by
  omega

end OnlyThree
