import Mathlib

/-!
# `det (exp A) = exp (trace A)`

For every square matrix `A` over an `RCLike` field `𝕂` (in particular `ℝ` and `ℂ`), indexed by
a finite type with decidable equality, `(NormedSpace.exp A).det = NormedSpace.exp A.trace`.

Route: the map `det` is differentiable at `1` with derivative `trace` (from
`Matrix.det_one_add_smul`); hence `u ↦ det (exp (u • A))` has derivative `trace A * det (exp (t • A))`
(using `exp ((t + h) • A) = exp (t • A) * exp (h • A)`); then
`det (exp (u • A)) * exp (-(u * trace A))` has zero derivative and equals `1` at `u = 0`.
-/

open NormedSpace Matrix Polynomial

noncomputable section

namespace DetExp

variable {m 𝕂 : Type*} [Fintype m] [DecidableEq m] [RCLike 𝕂]

section
open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false in
theorem differentiable_det : Differentiable 𝕂 (fun M : Matrix m m 𝕂 => M.det) := by
  simp only [Matrix.det_apply]
  refine Differentiable.fun_sum fun σ _ => ?_
  refine Differentiable.const_smul ?_ _
  have hent : ∀ i j : m, Differentiable 𝕂 (fun M : Matrix m m 𝕂 => M i j) := fun i j =>
    (LinearMap.toContinuousLinearMap
    (⟨⟨fun M : Matrix m m 𝕂 => M i j, fun _ _ => rfl⟩, fun _ _ => rfl⟩ :
      Matrix m m 𝕂 →ₗ[𝕂] 𝕂)).differentiable
  fun_prop

set_option backward.isDefEq.respectTransparency false in
/-- `det` has derivative `trace` at `1`. -/
theorem hasFDerivAt_det_one :
    ∃ L : Matrix m m 𝕂 →L[𝕂] 𝕂, HasFDerivAt (fun M : Matrix m m 𝕂 => M.det) L 1 ∧
      ∀ M, L M = M.trace := by
  refine ⟨fderiv 𝕂 (fun M : Matrix m m 𝕂 => M.det) 1, (differentiable_det 1).hasFDerivAt, fun M => ?_⟩
  have h1 : HasDerivAt (fun r : 𝕂 => (1 + r • M).det) (M.trace) 0 := by
    have hp := Polynomial.hasDerivAt
      (((1 + (X : 𝕂[X]) • M.map C).det).divX.divX * X ^ 2 + (C M.trace * X + 1)) (0 : 𝕂)
    convert hp using 1
    · ext r
      have := Matrix.det_one_add_smul r M
      simp only [this]
      simp
      ring
    · simp [Polynomial.derivative_mul]
  have h2 : HasDerivAt (fun r : 𝕂 => (1 : Matrix m m 𝕂) + r • M) M 0 := by
    simpa using ((hasDerivAt_id (0 : 𝕂)).smul_const M).const_add 1
  have h3 := ((differentiable_det (m := m) (𝕂 := 𝕂)) (1 + (0 : 𝕂) • M)).hasFDerivAt.comp_hasDerivAt
    (0 : 𝕂) h2
  have h4 : (fderiv 𝕂 (fun M : Matrix m m 𝕂 => M.det) 1) M = M.trace := by
    have h1' : HasDerivAt ((fun M : Matrix m m 𝕂 => M.det) ∘ fun r : 𝕂 => (1 : Matrix m m 𝕂) + r • M)
        M.trace 0 := h1
    have := h3.unique (by simpa using h1')
    simpa using this
  exact h4

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_det_exp_smul_zero (A : Matrix m m 𝕂) :
    HasDerivAt (fun u : 𝕂 => (exp (u • A)).det) A.trace 0 := by
  obtain ⟨L, hL, hLM⟩ := hasFDerivAt_det_one (m := m) (𝕂 := 𝕂)
  have h := hasDerivAt_exp_smul_const' (𝕂 := 𝕂) A (0 : 𝕂)
  simp only [zero_smul, exp_zero, mul_one] at h
  have hL' : HasFDerivAt (fun M : Matrix m m 𝕂 => M.det) L (exp ((0 : 𝕂) • A)) := by
    simpa using hL
  have h2 := hL'.comp_hasDerivAt (0 : 𝕂) h
  rw [hLM] at h2
  simpa [Function.comp_def] using h2

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_det_exp_smul (A : Matrix m m 𝕂) (t : 𝕂) :
    HasDerivAt (fun u : 𝕂 => (exp (u • A)).det) (A.trace * (exp (t • A)).det) t := by
  have h0 := hasDerivAt_det_exp_smul_zero A
  have h1 : HasDerivAt (fun u : 𝕂 => (exp ((u - t) • A)).det) A.trace t := by
    have := HasDerivAt.comp_sub_const t t (f := fun u : 𝕂 => (exp (u • A)).det) (by simpa using h0)
    simpa using this
  have h2 := h1.const_mul (exp (t • A)).det
  convert h2 using 1
  · ext u
    have : u • A = t • A + (u - t) • A := by rw [← add_smul]; simp
    rw [this, NormedSpace.exp_add_of_commute ((Commute.refl A).smul_left t |>.smul_right (u - t)), Matrix.det_mul]
  · ring

end

set_option backward.isDefEq.respectTransparency false in
/-- Jacobi's formula for the flow: `det (exp (t • A)) = exp (t * trace A)`. -/
theorem det_exp_smul (A : Matrix m m 𝕂) (t : 𝕂) :
    (exp (t • A)).det = exp (t * A.trace) := by
  set g : 𝕂 → 𝕂 := fun u => (exp (u • A)).det * exp (-(u * A.trace)) with hg
  have hd : ∀ u, HasDerivAt g 0 u := by
    intro u
    have h1 := hasDerivAt_det_exp_smul A u
    have h2 : HasDerivAt (fun u : 𝕂 => exp (-(u * A.trace)))
        (-A.trace * exp (u • (-A.trace))) u := by
      have := hasDerivAt_exp_smul_const' (𝕂 := 𝕂) (-A.trace) u
      simpa [smul_eq_mul] using this
    have h3 := h1.mul h2
    convert h3 using 1
    simp only [smul_eq_mul]
    rw [show u * -A.trace = -(u * A.trace) by ring]
    ring
  have hc := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t 0
  simp only [hg, zero_smul, exp_zero, Matrix.det_one, zero_mul, neg_zero, mul_one] at hc
  calc (exp (t • A)).det = (exp (t • A)).det * exp (-(t * A.trace)) * exp (t * A.trace) := by
        rw [mul_assoc, ← NormedSpace.exp_add_of_commute (Commute.all _ _)]; simp
    _ = exp (t * A.trace) := by rw [hc, one_mul]

/-- Jacobi's formula: `det (exp A) = exp (trace A)` over `ℝ` or `ℂ` (any `RCLike` field). -/
theorem det_exp (A : Matrix m m 𝕂) : (exp A).det = exp A.trace := by
  simpa using det_exp_smul A 1

theorem det_exp_real {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℝ) :
    (exp A).det = Real.exp A.trace := by
  rw [det_exp, Real.exp_eq_exp_ℝ]

theorem det_exp_complex {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) :
    (exp A).det = Complex.exp A.trace := by
  rw [det_exp, Complex.exp_eq_exp_ℂ]

end DetExp
