import Mathlib

/-!
# `det (exp A) = exp (trace A)` (derivative route; the eigenvalue route is blocked, see report)

The two lemmas `differentiable_det` and `hasFDerivAt_det_one` are as in `DetExp_ode_1.lean`.

For every square matrix `A` over an `RCLike` field `𝕂` (in particular `ℝ` and `ℂ`), indexed by
a finite type with decidable equality, `(NormedSpace.exp A).det = NormedSpace.exp A.trace`.

Route: the map `det` is differentiable at `1` with derivative `trace` (from
`Matrix.det_one_add_smul`); hence `u ↦ det (exp (u • A))` has derivative `trace A * det (exp (t • A))`
(using `exp ((t + h) • A) = exp (t • A) * exp (h • A)`); then
`det (exp (u • A)) * exp (-(u * trace A))` has zero derivative and equals `1` at `u = 0`.
-/

open NormedSpace Matrix Polynomial

noncomputable section

namespace DetExpEigen3

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
theorem hasDerivAt_det_exp_smul (A : Matrix m m 𝕂) (t : 𝕂) :
    HasDerivAt (fun u : 𝕂 => (exp (u • A)).det) (A.trace * (exp (t • A)).det) t := by
  obtain ⟨L, hL, hLM⟩ := hasFDerivAt_det_one (m := m) (𝕂 := 𝕂)
  have he : HasDerivAt (fun u : 𝕂 => exp (u • A)) (A * exp ((0 : 𝕂) • A)) 0 :=
    hasDerivAt_exp_smul_const' A 0
  simp only [zero_smul, NormedSpace.exp_zero, mul_one] at he
  have hg0 : HasDerivAt (fun h : 𝕂 => (exp (h • A)).det) A.trace 0 := by
    have hL' : HasFDerivAt (fun M : Matrix m m 𝕂 => M.det) L (exp ((0 : 𝕂) • A)) := by
      simpa using hL
    have h := hL'.comp_hasDerivAt (0 : 𝕂) he
    rw [hLM A] at h
    exact h
  have hg : HasDerivAt (fun s : 𝕂 => (exp ((s - t) • A)).det) A.trace t := by
    have := HasDerivAt.comp_sub_const t t (f := fun h : 𝕂 => (exp (h • A)).det) (by simpa using hg0)
    simpa using this
  have := hg.const_mul (exp (t • A)).det
  have hfun : (fun u : 𝕂 => (exp (u • A)).det) =
      fun s => (exp (t • A)).det * (exp ((s - t) • A)).det := by
    funext s
    rw [← Matrix.det_mul, ← NormedSpace.exp_add_of_commute (((Commute.refl A).smul_left _).smul_right _)]
    congr 2
    rw [← add_smul]; congr 1; ring
  rw [hfun]
  convert this using 1
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Jacobi's formula for the matrix exponential over `RCLike` fields. -/
theorem det_exp (A : Matrix m m 𝕂) : (exp A).det = exp A.trace := by
  set φ : 𝕂 → 𝕂 := fun u => (exp (u • A)).det * exp (u • (-A.trace)) with hφ
  have hd : ∀ u, HasDerivAt φ 0 u := by
    intro u
    have h1 := hasDerivAt_det_exp_smul A u
    have h2 := hasDerivAt_exp_smul_const' (𝕂 := 𝕂) (-A.trace) u
    have := h1.mul h2
    convert this using 1
    simp only [smul_eq_mul]
    ring
  have hc := is_const_of_deriv_eq_zero (f := φ) (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) 1 0
  simp only [hφ, zero_smul, NormedSpace.exp_zero, mul_one, one_smul, Matrix.det_one] at hc
  have h3 : exp (-A.trace) * exp A.trace = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.all _ _)]; simp [NormedSpace.exp_zero]
  calc (exp A).det = (exp A).det * (exp (-A.trace) * exp A.trace) := by rw [h3, mul_one]
    _ = exp A.trace := by rw [← mul_assoc, hc, one_mul]

end

theorem det_exp_complex (A : Matrix m m ℂ) : (exp A).det = Complex.exp A.trace := by
  rw [Complex.exp_eq_exp_ℂ]; exact det_exp A

theorem det_exp_real (A : Matrix m m ℝ) : (exp A).det = Real.exp A.trace := by
  rw [Real.exp_eq_exp_ℝ]; exact det_exp A

end DetExpEigen3

