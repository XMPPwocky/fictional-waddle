import Mathlib

/-!
# Why gravity and quantum mechanics part at different scales, while electromagnetism and QM do not

For a particle of mass `m`:
* quantum length (reduced Compton wavelength) `λ = ħ / (m c)`, shrinking with `m`;
* gravitational length (Schwarzschild radius) `r_g = 2 G m / c²`, GROWING with `m`, because gravity's charge is the mass
  itself (the equivalence principle);
* electromagnetic length (classical radius) `r_e = k e² / (m c²)`, shrinking with `m` like `λ`, because the
  electromagnetic charge `e` is independent of the mass.

* Q1 `gravity_ratio`: `r_g / λ = 2 G m² / (ħ c)` grows as `m²`: the two lengths cross at one mass (the Planck mass).
* Q2 `gravity_product`: `r_g · λ = 2 G ħ / c³` is independent of `m` (twice the Planck area): one rises exactly as the
  other falls.
* Q3 `em_ratio`: `r_e / λ = k e² / (ħ c)` is independent of `m` (the fine-structure constant): electromagnetism never
  parts from QM by scale.
-/

namespace WhyScalesSplit

theorem gravity_ratio (G ħ c m : ℝ) (hħ : ħ ≠ 0) (hc : c ≠ 0) (hm : m ≠ 0) :
    (2 * G * m / c ^ 2) / (ħ / (m * c)) = 2 * G * m ^ 2 / (ħ * c) := by
  field_simp

theorem gravity_product (G ħ c m : ℝ) (hc : c ≠ 0) (hm : m ≠ 0) :
    (2 * G * m / c ^ 2) * (ħ / (m * c)) = 2 * G * ħ / c ^ 3 := by
  field_simp

theorem em_ratio (k e ħ c m : ℝ) (hħ : ħ ≠ 0) (hc : c ≠ 0) (hm : m ≠ 0) :
    (k * e ^ 2 / (m * c ^ 2)) / (ħ / (m * c)) = k * e ^ 2 / (ħ * c) := by
  field_simp

end WhyScalesSplit
