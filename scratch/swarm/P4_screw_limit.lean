import Mathlib

/-!
# P4: a screw is the flat limit of a 4-D double rotation

This file is a single worked example of the Inönü–Wigner contraction `SO(4) → SE(3)`.

Setup (proved facts are marked **[proved]**, the rest is interpretation):

* A 3-D point `(x, y, z)` is embedded near the "north pole" `(0,0,0,R)` of the 3-sphere of
  radius `R` in `ℝ⁴` as the point `(x, y, z, R)`, i.e. it is placed on the *tangent hyperplane*
  `w = R` at the north pole (we do NOT project to the exact sphere point; this is our choice of
  embedding).  The choice does not matter for the limit: `screw_limit_of_height` **[proved]**
  gives the same screw limit for any height `h R` with `h R / R → 1`, and an `example` at the
  end of the file instantiates it at the exact sphere point `√(R² − x² − y² − z²)`.
* `doubleRot θ φ` rotates the `(x,y)`-plane by `θ` and the `(z,w)`-plane by `φ`.  It is an
  isometry of Euclidean `ℝ⁴` **[proved: `doubleRot_norm`, `doubleRot_isometry`]**.
* With `θ = ω t` and `φ = v t / R`, the first three coordinates of the image of `(x,y,z,R)`
  converge, as `R → ∞`, to the screw motion
  `(x cos ωt − y sin ωt, x sin ωt + y cos ωt, z + v t)` **[proved: `screw_limit`]**, and the fourth
  coordinate stays at height `R + o(1)` **[proved: `height_limit`]**.

Interpretation (not formalised): the `(z,w)`-rotation by the small angle `v t / R` on a sphere of
huge radius looks, near the pole, like a translation by `v t` along `z`; the `(x,y)`-rotation is
untouched.  So the one-parameter subgroup of `SO(4)` contracts to a one-parameter subgroup of
`SE(3)` — a screw.  Chasles's theorem (every proper rigid motion of `ℝ³` is a screw motion) is
cited, not proved, as the reason this example is generic for one-parameter subgroups of `SE(3)`.
-/

open Real Filter Topology

namespace P4ScrewLimit

/-- Euclidean 4-space. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- The embedding of a 3-D point onto the tangent hyperplane `w = R` at the north pole. -/
noncomputable def embed (x y z R : ℝ) : E4 := WithLp.toLp 2 ![x, y, z, R]

/-- The double rotation: angle `θ` in the `(x,y)`-plane, angle `φ` in the `(z,w)`-plane. -/
noncomputable def doubleRot (θ φ : ℝ) (p : E4) : E4 :=
  WithLp.toLp 2 ![cos θ * p 0 - sin θ * p 1, sin θ * p 0 + cos θ * p 1,
    cos φ * p 2 + sin φ * p 3, -sin φ * p 2 + cos φ * p 3]

/-- First three coordinates. -/
def first3 (p : E4) : ℝ × ℝ × ℝ := (p 0, p 1, p 2)

/-- The screw motion with angular speed `ω` and pitch speed `v`, at time `t`. -/
noncomputable def screw (ω v t : ℝ) (q : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (q.1 * cos (ω * t) - q.2.1 * sin (ω * t), q.1 * sin (ω * t) + q.2.1 * cos (ω * t),
    q.2.2 + v * t)

/-- **[proved]** The double rotation preserves the Euclidean norm of `ℝ⁴`. -/
theorem doubleRot_norm (θ φ : ℝ) (p : E4) : ‖doubleRot θ φ p‖ = ‖p‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [doubleRot, Fin.sum_univ_four, Real.norm_eq_abs, sq_abs]
  simp
  linear_combination (p 0 ^ 2 + p 1 ^ 2) * sin_sq_add_cos_sq θ +
    (p 2 ^ 2 + p 3 ^ 2) * sin_sq_add_cos_sq φ

/-- **[proved]** The double rotation is an isometry of Euclidean `ℝ⁴`. -/
theorem doubleRot_isometry (θ φ : ℝ) : Isometry (doubleRot θ φ) := by
  have hsub : ∀ p q : E4, doubleRot θ φ p - doubleRot θ φ q = doubleRot θ φ (p - q) := by
    intro p q
    ext i
    fin_cases i <;> simp [doubleRot] <;> ring
  refine Isometry.of_dist_eq fun p q => ?_
  rw [dist_eq_norm, dist_eq_norm, hsub, doubleRot_norm]

/-- **[proved]** Key scalar limit: `R · sin (c / R) → c` as `R → ∞`. -/
theorem mul_sin_div_tendsto (c : ℝ) :
    Tendsto (fun R : ℝ => R * sin (c / R)) atTop (𝓝 c) := by
  have h0 : Tendsto (fun R : ℝ => c / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h1 : Tendsto (fun R : ℝ => c * sinc (c / R)) atTop (𝓝 (c * sinc 0)) :=
    tendsto_const_nhds.mul ((continuous_sinc.tendsto 0).comp h0)
  rw [sinc_zero, mul_one] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  by_cases hc : c = 0
  · simp [hc]
  · have hcR : c / R ≠ 0 := div_ne_zero hc hR.ne'
    rw [sinc_of_ne_zero hcR]
    field_simp

/-- **[proved]** Main theorem: as `R → ∞`, the first three coordinates of the double rotation
(angles `ω t` and `v t / R`) applied to `(x, y, z, R)` converge to the screw motion. -/
theorem screw_limit (ω v t x y z : ℝ) :
    Tendsto (fun R : ℝ => first3 (doubleRot (ω * t) (v * t / R) (embed x y z R))) atTop
      (𝓝 (screw ω v t (x, y, z))) := by
  have h0 : Tendsto (fun R : ℝ => v * t / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hcos : Tendsto (fun R : ℝ => cos (v * t / R)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using (continuous_cos.tendsto 0).comp h0
  have h3 : Tendsto (fun R : ℝ => cos (v * t / R) * z + sin (v * t / R) * R) atTop
      (𝓝 (z + v * t)) := by
    have := (hcos.mul_const z).add ((mul_sin_div_tendsto (v * t)))
    simpa [one_mul, mul_comm] using this
  simp only [first3, doubleRot, embed, screw]
  refine Tendsto.prodMk_nhds ?_ (Tendsto.prodMk_nhds ?_ ?_)
  · refine tendsto_const_nhds.congr fun R => ?_
    simp
    ring
  · refine tendsto_const_nhds.congr fun R => ?_
    simp
    ring
  · simpa using h3

/-- **[proved]** The fourth coordinate stays at height `R + o(1)`: the image does not leave the
tangent hyperplane in the limit. -/
theorem height_limit (ω v t x y z : ℝ) :
    Tendsto (fun R : ℝ => (doubleRot (ω * t) (v * t / R) (embed x y z R)) 3 - R) atTop
      (𝓝 0) := by
  have h0 : Tendsto (fun R : ℝ => v * t / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hsin : Tendsto (fun R : ℝ => sin (v * t / R)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (continuous_sin.tendsto 0).comp h0
  -- squeeze `R * (cos (c/R) - 1)` between `-c^2/(2R)` and `0`
  have hlow : Tendsto (fun R : ℝ => -((v * t) ^ 2 / 2) / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hc : Tendsto (fun R : ℝ => R * (cos (v * t / R) - 1)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with R hR
      have hb := one_sub_sq_div_two_le_cos (x := v * t / R)
      have : -((v * t) ^ 2 / 2) / R = R * (-( (v * t / R) ^ 2 / 2)) := by
        field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left (by linarith) hR.le
    · filter_upwards [eventually_gt_atTop 0] with R hR
      have := cos_le_one (v * t / R)
      nlinarith
  have := (hsin.mul_const z).neg.add hc
  simp only [neg_zero, zero_mul, add_zero] at this
  refine this.congr' (Eventually.of_forall fun R => ?_)
  simp [doubleRot, embed]
  ring

/-- **[proved]** Going "up": the screw limit holds for *any* height function `h` with
`h R / R → 1`, not only for the tangent-hyperplane embedding `h R = R`.  In particular it covers
the exact sphere point `(x, y, z, √(R² − x² − y² − z²))` on the 3-sphere of radius `R`
(see the `example` below), so the choice of embedding does not affect the limit. -/
theorem screw_limit_of_height (ω v t x y z : ℝ) (h : ℝ → ℝ)
    (hh : Tendsto (fun R : ℝ => h R / R) atTop (𝓝 1)) :
    Tendsto (fun R : ℝ =>
        first3 (doubleRot (ω * t) (v * t / R) (WithLp.toLp 2 ![x, y, z, h R]))) atTop
      (𝓝 (screw ω v t (x, y, z))) := by
  have h0 : Tendsto (fun R : ℝ => v * t / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hcos : Tendsto (fun R : ℝ => cos (v * t / R)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using (continuous_cos.tendsto 0).comp h0
  have h3 : Tendsto (fun R : ℝ => cos (v * t / R) * z + (R * sin (v * t / R)) * (h R / R))
      atTop (𝓝 (1 * z + v * t * 1)) :=
    (hcos.mul_const z).add ((mul_sin_div_tendsto (v * t)).mul hh)
  rw [one_mul, mul_one] at h3
  simp only [first3, doubleRot, screw]
  refine Tendsto.prodMk_nhds ?_ (Tendsto.prodMk_nhds ?_ ?_)
  · refine tendsto_const_nhds.congr fun R => ?_
    simp
    ring
  · refine tendsto_const_nhds.congr fun R => ?_
    simp
    ring
  · refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    simp
    field_simp

/-! ### Concrete instances (sanity checks; no hypotheses beyond the stated ones) -/

/-- The exact sphere embedding satisfies the hypothesis of `screw_limit_of_height`. -/
example (ω v t x y z : ℝ) :
    Tendsto (fun R : ℝ => first3 (doubleRot (ω * t) (v * t / R)
        (WithLp.toLp 2 ![x, y, z, √(R ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2))]))) atTop
      (𝓝 (screw ω v t (x, y, z))) := by
  refine screw_limit_of_height ω v t x y z _ ?_
  set s := x ^ 2 + y ^ 2 + z ^ 2
  have hs : Tendsto (fun R : ℝ => s / R ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  have hq : Tendsto (fun R : ℝ => √(1 - s / R ^ 2)) atTop (𝓝 1) := by
    have := ((continuous_sqrt.tendsto (1 - 0)).comp (tendsto_const_nhds.sub hs))
    simpa [Function.comp_def] using this
  refine hq.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hR2 : (0 : ℝ) ≤ R ^ 2 := by positivity
  rw [show (1 : ℝ) - s / R ^ 2 = (R ^ 2 - s) / R ^ 2 by field_simp, Real.sqrt_div' _ hR2,
    Real.sqrt_sq hR.le]

/-- A pure translation (`ω = 0`): the point `(1, 2, 3)` moving at speed `v = 5` for time `t = 2`
tends to `(1, 2, 13)`. -/
example : Tendsto (fun R : ℝ => first3 (doubleRot (0 * 2) (5 * 2 / R) (embed 1 2 3 R))) atTop
    (𝓝 ((1 : ℝ), (2 : ℝ), (13 : ℝ))) := by
  have hpt : screw 0 5 2 ((1 : ℝ), (2 : ℝ), (3 : ℝ)) = ((1 : ℝ), (2 : ℝ), (13 : ℝ)) := by
    simp [screw]; norm_num
  rw [← hpt]
  exact screw_limit 0 5 2 1 2 3

/-- The isometry statement is not vacuous: the norm of `(1,0,0,0)` is `1` and is preserved. -/
example (θ φ : ℝ) : ‖doubleRot θ φ (embed 1 0 0 0)‖ = 1 := by
  rw [doubleRot_norm, EuclideanSpace.norm_eq]
  simp [embed, Fin.sum_univ_four]

end P4ScrewLimit
