import Mathlib

/-!
# TwoClocksHopfB

The linear focus `x' = A x`, `A = [[μ, -ω], [ω, μ]]`, and its solution
`x(t) = e^{μt} (cos ωt, sin ωt)`.

PROVED
* `hasDerivAt_x1`, `hasDerivAt_x2`: coordinatewise
  `x₁' = μ x₁ - ω x₂`, `x₂' = ω x₁ + μ x₂`.
* `hasDerivAt_x`: the vector form `HasDerivAt x (A.mulVec (x t)) t` for `x : ℝ → Fin 2 → ℝ`.
* `norm_eq`: `√(x₁(t)² + x₂(t)²) = e^{μt}` (independent of `ω`).
* `norm_const_of_mu_zero` (a): for `μ = 0` the norm is `1` for all `t`.
* `tendsto_norm_zero_of_mu_neg` (b): for `μ < 0` the norm tends to `0` as `t → ∞`.
* `charpoly_A` (c): the characteristic polynomial of `A` over `ℂ` is `(X - μ)² + ω²`.
* `charpoly_A_root_iff` (c): `z` is a root iff `z = μ + iω ∨ z = μ - iω`.
* `hasEigenvalue_plus`, `hasEigenvalue_minus` (c): `μ ± iω` are eigenvalues of `A`
  (as a linear map on `Fin 2 → ℂ`), with eigenvectors `(1, ∓i)`.

INTERPRETED
* The real part `μ` of the eigenvalue sets the radial (time-scale) behaviour, since the
  norm `e^{μt}` does not depend on `ω`; the imaginary part `ω` enters only the angle.
* `μ = 0` is read as a conserved clock (pure rotation); `μ < 0` as decay to the fixed point.
-/

namespace TwoClocksHopfB

open Real Filter Topology Polynomial

/-- First coordinate `e^{μt} cos ωt`. -/
noncomputable def x1 (μ ω t : ℝ) : ℝ := Real.exp (μ * t) * Real.cos (ω * t)

/-- Second coordinate `e^{μt} sin ωt`. -/
noncomputable def x2 (μ ω t : ℝ) : ℝ := Real.exp (μ * t) * Real.sin (ω * t)

/-- The curve as a vector in `Fin 2 → ℝ`. -/
noncomputable def x (μ ω : ℝ) (t : ℝ) : Fin 2 → ℝ := ![x1 μ ω t, x2 μ ω t]

/-- The real system matrix `[[μ, -ω], [ω, μ]]`. -/
def A (μ ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![μ, -ω; ω, μ]

/-- The same matrix over `ℂ`. -/
noncomputable def Ac (μ ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(μ : ℂ), -(ω : ℂ); (ω : ℂ), (μ : ℂ)]

theorem hasDerivAt_x1 (μ ω t : ℝ) :
    HasDerivAt (x1 μ ω) (μ * x1 μ ω t - ω * x2 μ ω t) t := by
  have h1 : HasDerivAt (fun s => Real.exp (μ * s)) (Real.exp (μ * t) * μ) t := by
    have := ((hasDerivAt_id t).const_mul μ).exp
    simpa using this
  have h2 : HasDerivAt (fun s => Real.cos (ω * s)) (-Real.sin (ω * t) * ω) t := by
    have := ((hasDerivAt_id t).const_mul ω).cos
    simpa using this
  have := h1.mul h2
  unfold x1 x2
  convert this using 1
  ring

theorem hasDerivAt_x2 (μ ω t : ℝ) :
    HasDerivAt (x2 μ ω) (ω * x1 μ ω t + μ * x2 μ ω t) t := by
  have h1 : HasDerivAt (fun s => Real.exp (μ * s)) (Real.exp (μ * t) * μ) t := by
    have := ((hasDerivAt_id t).const_mul μ).exp
    simpa using this
  have h2 : HasDerivAt (fun s => Real.sin (ω * s)) (Real.cos (ω * t) * ω) t := by
    have := ((hasDerivAt_id t).const_mul ω).sin
    simpa using this
  have := h1.mul h2
  unfold x1 x2
  convert this using 1
  ring

/-- Vector form: `x' = A x`. -/
theorem hasDerivAt_x (μ ω t : ℝ) :
    HasDerivAt (x μ ω) ((A μ ω).mulVec (x μ ω t)) t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · have := hasDerivAt_x1 μ ω t
    simp only [x, A, Fin.zero_eta, Matrix.cons_val_zero, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one] at this ⊢
    convert this using 1
    ring
  · have := hasDerivAt_x2 μ ω t
    simp only [x, A, Fin.mk_one, Matrix.cons_val_zero, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one] at this ⊢
    convert this using 1

/-- The Euclidean norm is `e^{μt}`; it does not depend on `ω`. -/
theorem norm_eq (μ ω t : ℝ) :
    Real.sqrt (x1 μ ω t ^ 2 + x2 μ ω t ^ 2) = Real.exp (μ * t) := by
  have : x1 μ ω t ^ 2 + x2 μ ω t ^ 2 = Real.exp (μ * t) ^ 2 := by
    unfold x1 x2
    have := Real.sin_sq_add_cos_sq (ω * t)
    linear_combination (Real.exp (μ * t)) ^ 2 * this
  rw [this, Real.sqrt_sq (Real.exp_pos _).le]

/-- (a) For `μ = 0` the norm is constant, equal to `1`. -/
theorem norm_const_of_mu_zero (ω t : ℝ) :
    Real.sqrt (x1 0 ω t ^ 2 + x2 0 ω t ^ 2) = 1 := by
  rw [norm_eq]; simp

/-- (a') For `μ = 0` the norm takes the same value at any two times. -/
theorem norm_conserved_of_mu_zero (ω s t : ℝ) :
    Real.sqrt (x1 0 ω s ^ 2 + x2 0 ω s ^ 2) = Real.sqrt (x1 0 ω t ^ 2 + x2 0 ω t ^ 2) := by
  rw [norm_const_of_mu_zero, norm_const_of_mu_zero]

/-- (b) For `μ < 0` the norm tends to `0`. -/
theorem tendsto_norm_zero_of_mu_neg {μ : ℝ} (hμ : μ < 0) (ω : ℝ) :
    Tendsto (fun t => Real.sqrt (x1 μ ω t ^ 2 + x2 μ ω t ^ 2)) atTop (𝓝 0) := by
  simp_rw [norm_eq]
  have : Tendsto (fun t => μ * t) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg hμ
  exact Real.tendsto_exp_atBot.comp this

/-- (b') For `μ < 0` both coordinates tend to `0`. -/
theorem tendsto_coords_zero_of_mu_neg {μ : ℝ} (hμ : μ < 0) (ω : ℝ) :
    Tendsto (x1 μ ω) atTop (𝓝 0) ∧ Tendsto (x2 μ ω) atTop (𝓝 0) := by
  have he : Tendsto (fun t => Real.exp (μ * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hμ)
  have hb : ∀ t, |x1 μ ω t| ≤ Real.exp (μ * t) ∧ |x2 μ ω t| ≤ Real.exp (μ * t) := by
    intro t
    unfold x1 x2
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact ⟨mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _),
      mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sin_le_one _)⟩
  refine ⟨?_, ?_⟩
  · exact squeeze_zero_norm (fun t => by simpa using (hb t).1) he
  · exact squeeze_zero_norm (fun t => by simpa using (hb t).2) he

/-- (c) Characteristic polynomial `(X - μ)² + ω²`. -/
theorem charpoly_A (μ ω : ℝ) :
    (Ac μ ω).charpoly = (X - C (μ : ℂ)) ^ 2 + C ((ω : ℂ) ^ 2) := by
  rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Ac, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  simp only [map_add, map_sub, map_mul, map_neg, map_pow]
  ring

/-- (c) The roots of the characteristic polynomial are exactly `μ ± iω`. -/
theorem charpoly_A_root_iff (μ ω : ℝ) (z : ℂ) :
    (Ac μ ω).charpoly.eval z = 0 ↔
      z = (μ : ℂ) + (ω : ℂ) * Complex.I ∨ z = (μ : ℂ) - (ω : ℂ) * Complex.I := by
  rw [charpoly_A]
  simp only [eval_add, eval_pow, eval_sub, eval_X, eval_C]
  have key : (z - μ) ^ 2 + (ω : ℂ) ^ 2 =
      (z - ((μ : ℂ) + ω * Complex.I)) * (z - ((μ : ℂ) - ω * Complex.I)) := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [key, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- (c) `μ + iω` is an eigenvalue, eigenvector `(1, -i)`. -/
theorem hasEigenvalue_plus (μ ω : ℝ) :
    Module.End.HasEigenvalue (Matrix.toLin' (Ac μ ω)) ((μ : ℂ) + (ω : ℂ) * Complex.I) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := ![1, -Complex.I])
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    ext i
    fin_cases i
    · simp [Ac, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [Ac, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring_nf
      simp [Complex.I_sq]
  · intro h
    have := congrFun h 0
    simp at this

/-- (c) `μ - iω` is an eigenvalue, eigenvector `(1, i)`. -/
theorem hasEigenvalue_minus (μ ω : ℝ) :
    Module.End.HasEigenvalue (Matrix.toLin' (Ac μ ω)) ((μ : ℂ) - (ω : ℂ) * Complex.I) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := ![1, Complex.I])
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    ext i
    fin_cases i
    · simp [Ac, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · simp [Ac, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring_nf
      simp [Complex.I_sq]
  · intro h
    have := congrFun h 0
    simp at this

end TwoClocksHopfB
