import Mathlib

/-!
# Two clocks of a linear focus: growth rate versus rotation

For real `μ, ω` consider the curve `x(t) = e^{μ t} (cos ω t, sin ω t)` and the matrix
`A = [[μ, -ω], [ω, μ]]`.

PROVED
* `hasDerivAt_x₁`, `hasDerivAt_x₂`: coordinatewise `x₁' = μ x₁ - ω x₂`, `x₂' = ω x₁ + μ x₂`.
* `hasDerivAt_mulVec`: the same statement written as `x' = A *ᵥ x` (each coordinate).
* `norm_eq`: `√(x₁² + x₂²) = e^{μ t}`; `norm_euclidean_eq`: the same for the Euclidean norm
  of `x(t) ∈ EuclideanSpace ℝ (Fin 2)`.
* `norm_const_of_mu_zero` (a): for `μ = 0` the norm is identically `1`.
* `tendsto_norm_zero_of_mu_neg` (b): for `μ < 0` the norm tends to `0` as `t → ∞`
  (stated for both the square-root and the Euclidean norm).
* `Ac_eq_map`: the complex matrix `Ac` is the entrywise image of the real `A`.
* `charpoly_eq` (c): the characteristic polynomial of `A` over `ℂ` is `(X - μ)² + ω²`.
* `charpoly_eval_factor`: `(z - μ)² + ω² = (z - (μ + iω)) (z - (μ - iω))`.
* `isRoot_charpoly_iff`: the roots of the characteristic polynomial are exactly `μ ± iω`.
* `hasEigenvalue_iff`: `z` is an eigenvalue of `A` (as a complex linear endomorphism of
  `Fin 2 → ℂ`) iff `z = μ + iω ∨ z = μ - iω`.
* `mulVec_eigvec_plus`, `mulVec_eigvec_minus`: explicit eigenvectors `(1, -i)` and `(1, i)`.

INTERPRETED
* The real part `μ` of the eigenvalue sets the radial time scale (`|x(t)| = e^{μ t}`); the
  imaginary part `ω` enters only through the angle `ω t` and does not affect the norm.
  For `μ = 0` the motion is a pure rotation with conserved norm.
* Nothing here formalizes any claim about phases failing to round-trip through bits; this
  file only covers the linear algebra and calculus of the normal form `μ ± iω`.
-/

namespace TwoClocksHopfA

open Real Filter Topology Polynomial

/-- First coordinate `e^{μ t} cos (ω t)`. -/
noncomputable def x₁ (μ ω t : ℝ) : ℝ := Real.exp (μ * t) * Real.cos (ω * t)

/-- Second coordinate `e^{μ t} sin (ω t)`. -/
noncomputable def x₂ (μ ω t : ℝ) : ℝ := Real.exp (μ * t) * Real.sin (ω * t)

/-- The real matrix `[[μ, -ω], [ω, μ]]`. -/
def A (μ ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![μ, -ω; ω, μ]

/-- The same matrix with complex entries. -/
noncomputable def Ac (μ ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(μ : ℂ), -(ω : ℂ); (ω : ℂ), (μ : ℂ)]

/-- The curve as a vector `Fin 2 → ℝ`. -/
noncomputable def xv (μ ω t : ℝ) : Fin 2 → ℝ := ![x₁ μ ω t, x₂ μ ω t]

/-- The curve as a point of the Euclidean plane. -/
noncomputable def xe (μ ω t : ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[x₁ μ ω t, x₂ μ ω t]

theorem hasDerivAt_x₁ (μ ω t : ℝ) :
    HasDerivAt (x₁ μ ω) (μ * x₁ μ ω t - ω * x₂ μ ω t) t := by
  have he : HasDerivAt (fun s => Real.exp (μ * s)) (Real.exp (μ * t) * μ) t := by
    simpa using ((hasDerivAt_id t).const_mul μ).exp
  have hc : HasDerivAt (fun s => Real.cos (ω * s)) (-Real.sin (ω * t) * ω) t := by
    simpa using ((hasDerivAt_id t).const_mul ω).cos
  have h := he.mul hc
  unfold x₁ x₂
  convert h using 1
  ring

theorem hasDerivAt_x₂ (μ ω t : ℝ) :
    HasDerivAt (x₂ μ ω) (ω * x₁ μ ω t + μ * x₂ μ ω t) t := by
  have he : HasDerivAt (fun s => Real.exp (μ * s)) (Real.exp (μ * t) * μ) t := by
    simpa using ((hasDerivAt_id t).const_mul μ).exp
  have hs : HasDerivAt (fun s => Real.sin (ω * s)) (Real.cos (ω * t) * ω) t := by
    simpa using ((hasDerivAt_id t).const_mul ω).sin
  have h := he.mul hs
  unfold x₁ x₂
  convert h using 1
  ring

/-- `x' = A x`, coordinate by coordinate. -/
theorem hasDerivAt_mulVec (μ ω t : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => xv μ ω s i) ((A μ ω).mulVec (xv μ ω t) i) t := by
  fin_cases i
  · have h := hasDerivAt_x₁ μ ω t
    simp only [xv, A, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
    convert h using 1
    ring
  · have h := hasDerivAt_x₂ μ ω t
    simp only [xv, A, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.mk_one, Fin.isValue]
    convert h using 1

theorem sq_add_sq_eq (μ ω t : ℝ) :
    x₁ μ ω t ^ 2 + x₂ μ ω t ^ 2 = Real.exp (μ * t) ^ 2 := by
  unfold x₁ x₂
  have := Real.cos_sq_add_sin_sq (ω * t)
  linear_combination Real.exp (μ * t) ^ 2 * this

theorem norm_eq (μ ω t : ℝ) :
    Real.sqrt (x₁ μ ω t ^ 2 + x₂ μ ω t ^ 2) = Real.exp (μ * t) := by
  rw [sq_add_sq_eq, Real.sqrt_sq (Real.exp_pos _).le]

theorem norm_euclidean_eq (μ ω t : ℝ) : ‖xe μ ω t‖ = Real.exp (μ * t) := by
  rw [EuclideanSpace.norm_eq, ← norm_eq μ ω t]
  congr 1
  simp [xe, Fin.sum_univ_two, sq_abs]

/-- (a) For `μ = 0` the norm is constant: a pure rotation. -/
theorem norm_const_of_mu_zero (ω t : ℝ) :
    Real.sqrt (x₁ 0 ω t ^ 2 + x₂ 0 ω t ^ 2) = 1 ∧ ‖xe 0 ω t‖ = 1 := by
  refine ⟨?_, ?_⟩
  · rw [norm_eq]; simp
  · rw [norm_euclidean_eq]; simp

theorem tendsto_exp_mul_of_neg {μ : ℝ} (hμ : μ < 0) :
    Tendsto (fun t => Real.exp (μ * t)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hμ)

/-- (b) For `μ < 0` the norm decays to `0`. -/
theorem tendsto_norm_zero_of_mu_neg {μ : ℝ} (ω : ℝ) (hμ : μ < 0) :
    Tendsto (fun t => Real.sqrt (x₁ μ ω t ^ 2 + x₂ μ ω t ^ 2)) atTop (𝓝 0) ∧
      Tendsto (fun t => ‖xe μ ω t‖) atTop (𝓝 0) := by
  refine ⟨?_, ?_⟩
  · simpa only [norm_eq] using tendsto_exp_mul_of_neg hμ
  · simpa only [norm_euclidean_eq] using tendsto_exp_mul_of_neg hμ

/-- The complex matrix is the image of the real one. -/
theorem Ac_eq_map (μ ω : ℝ) : Ac μ ω = (A μ ω).map (fun r : ℝ => (r : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ac, A]

/-- (c) The characteristic polynomial is `(X - μ)² + ω²`. -/
theorem charpoly_eq (μ ω : ℝ) :
    (Ac μ ω).charpoly = (X - C (μ : ℂ)) ^ 2 + C ((ω : ℂ) ^ 2) := by
  rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Ac, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue]
  simp only [map_add, map_sub, map_mul, map_neg, map_pow]
  ring

theorem charpoly_eval_factor (μ ω : ℝ) (z : ℂ) :
    (z - μ) ^ 2 + (ω : ℂ) ^ 2
      = (z - ((μ : ℂ) + (ω : ℂ) * Complex.I)) * (z - ((μ : ℂ) - (ω : ℂ) * Complex.I)) := by
  linear_combination ((ω : ℂ) ^ 2) * Complex.I_sq

theorem isRoot_charpoly_iff (μ ω : ℝ) (z : ℂ) :
    (Ac μ ω).charpoly.IsRoot z ↔
      z = (μ : ℂ) + (ω : ℂ) * Complex.I ∨ z = (μ : ℂ) - (ω : ℂ) * Complex.I := by
  rw [charpoly_eq, IsRoot.def]
  simp only [eval_add, eval_pow, eval_sub, eval_X, eval_C]
  rw [charpoly_eval_factor, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- (c) The eigenvalues of `A` over `ℂ` are exactly `μ ± iω`. -/
theorem hasEigenvalue_iff (μ ω : ℝ) (z : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' (Ac μ ω)) z ↔
      z = (μ : ℂ) + (ω : ℂ) * Complex.I ∨ z = (μ : ℂ) - (ω : ℂ) * Complex.I := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', isRoot_charpoly_iff]

/-- Eigenvector `(1, -i)` for `μ + iω`. -/
theorem mulVec_eigvec_plus (μ ω : ℝ) :
    (Ac μ ω).mulVec ![1, -Complex.I] = ((μ : ℂ) + (ω : ℂ) * Complex.I) • ![1, -Complex.I] := by
  ext i
  fin_cases i
  · simp [Ac, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [Ac, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination (ω : ℂ) * Complex.I_sq

/-- Eigenvector `(1, i)` for `μ - iω`. -/
theorem mulVec_eigvec_minus (μ ω : ℝ) :
    (Ac μ ω).mulVec ![1, Complex.I] = ((μ : ℂ) - (ω : ℂ) * Complex.I) • ![1, Complex.I] := by
  ext i
  fin_cases i <;>
    simp [Ac, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    first
      | linear_combination (ω : ℂ) * Complex.I_sq
      | linear_combination (-(ω : ℂ)) * Complex.I_sq
      | ring

end TwoClocksHopfA
