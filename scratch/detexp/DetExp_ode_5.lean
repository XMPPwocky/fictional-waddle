import Mathlib

/-!
# Jacobi's formula for the matrix exponential

For a square matrix `A` over `𝕂` with `[RCLike 𝕂]` (so in particular `ℝ` and `ℂ`), and any
finite index type `m` with decidable equality,
`(NormedSpace.exp A).det = NormedSpace.exp A.trace`
(`Matrix.DetExpODE.det_exp`). This is the TODO in
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`.

Route (ODE):
* `hasDerivAt_det_of_entries`: if every entry of a curve `c : 𝕂 → Matrix m m 𝕂` has a
  derivative at `x`, then `s ↦ (c s).det` has an explicit derivative at `x` that depends only on
  `c x` and the entry derivatives (Leibniz expansion of `det`).
* Applying this to `s ↦ exp (s • A)` and to `s ↦ 1 + s • A` (both equal to `1` at `0` with
  derivative `A`) and comparing with `Matrix.derivative_det_one_add_X_smul` for the second curve
  shows that `s ↦ (exp (s • A)).det` has derivative `A.trace` at `0`.
* `det (exp ((t + s) • A)) = det (exp (t • A)) * det (exp (s • A))`, so the derivative at `t`
  is `A.trace * det (exp (t • A))`.
* `s ↦ det (exp (s • A)) * exp (s • -A.trace)` has derivative zero, hence is constant `1`.
-/

open NormedSpace Matrix Equiv Finset

noncomputable section

namespace Matrix.DetExpODE

variable {m 𝕂 : Type*} [Fintype m] [DecidableEq m] [RCLike 𝕂]

/-- `M ↦ M i j` as a `𝕂`-linear map. -/
def entryLinearMap (i j : m) : Matrix m m 𝕂 →ₗ[𝕂] 𝕂 where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Derivative of the determinant along a curve whose entries are differentiable. -/
theorem hasDerivAt_det_of_entries (c : 𝕂 → Matrix m m 𝕂) (D : Matrix m m 𝕂) (x : 𝕂)
    (hc : ∀ i j, HasDerivAt (fun s => c s i j) (D i j) x) :
    HasDerivAt (fun s => (c s).det)
      (∑ σ : Perm m, (Perm.sign σ : 𝕂) * ∑ i, (∏ j ∈ univ.erase i, c x (σ j) j) * D (σ i) i) x := by
  simp_rw [det_apply']
  apply HasDerivAt.fun_sum
  intro σ _
  apply HasDerivAt.const_mul
  have := HasDerivAt.fun_finsetProd (u := univ) (f := fun i s => c s (σ i) i)
    (f' := fun i => D (σ i) i) (x := x) (fun i _ => hc (σ i) i)
  simpa [smul_eq_mul] using this

set_option backward.isDefEq.respectTransparency false in
/-- Entry `(i, j)` of `exp (u • A)` has derivative `(A * exp (t • A)) i j` at `t`. -/
theorem hasDerivAt_exp_smul_apply (A : Matrix m m 𝕂) (i j : m) (t : 𝕂) :
    HasDerivAt (fun u : 𝕂 => exp (u • A) i j) ((A * exp (t • A)) i j) t := by
  open scoped Norms.Operator in
  have h := hasDerivAt_exp_smul_const' (𝕂 := 𝕂) A t
  open scoped Norms.Operator in
  have hL := (LinearMap.toContinuousLinearMap (entryLinearMap (𝕂 := 𝕂) i j)).hasFDerivAt
    (x := exp (t • A))
  exact hL.comp_hasDerivAt t h

/-- `det (1 + s • A)` has derivative `A.trace` at `s = 0`. -/
theorem hasDerivAt_det_one_add_smul (A : Matrix m m 𝕂) :
    HasDerivAt (fun s : 𝕂 => (1 + s • A).det) A.trace 0 := by
  have h := Polynomial.hasDerivAt (det (1 + (Polynomial.X : Polynomial 𝕂) • A.map Polynomial.C)) 0
  rw [derivative_det_one_add_X_smul] at h
  convert h using 1
  funext s
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij] <;> ring

/-- `det (exp (s • A))` has derivative `A.trace` at `s = 0`. -/
theorem hasDerivAt_det_exp_smul_zero (A : Matrix m m 𝕂) :
    HasDerivAt (fun s : 𝕂 => (exp (s • A)).det) A.trace 0 := by
  have h1 := hasDerivAt_det_of_entries (fun s : 𝕂 => exp (s • A)) A 0
    (fun i j => by simpa using hasDerivAt_exp_smul_apply A i j 0)
  have h2 := hasDerivAt_det_of_entries (fun s : 𝕂 => 1 + s • A) A 0
    (fun i j => by
      simpa using ((hasDerivAt_id (0 : 𝕂)).mul_const (A i j)).const_add ((1 : Matrix m m 𝕂) i j))
  have e1 : exp ((0 : 𝕂) • A) = 1 := by simp
  have e2 : (1 : Matrix m m 𝕂) + (0 : 𝕂) • A = 1 := by simp
  simp only [e1] at h1
  simp only [e2] at h2
  rwa [h2.unique (hasDerivAt_det_one_add_smul A)] at h1

/-- `det (exp ((t + s) • A)) = det (exp (t • A)) * det (exp (s • A))`. -/
theorem det_exp_add_smul (A : Matrix m m 𝕂) (t s : 𝕂) :
    (exp ((t + s) • A)).det = (exp (t • A)).det * (exp (s • A)).det := by
  rw [add_smul, Matrix.exp_add_of_commute _ _ ((Commute.refl A).smul_left t |>.smul_right s),
    det_mul]

/-- `d/ds det (exp (s • A)) = A.trace * det (exp (s • A))`. -/
theorem hasDerivAt_det_exp_smul (A : Matrix m m 𝕂) (t : 𝕂) :
    HasDerivAt (fun s : 𝕂 => (exp (s • A)).det) (A.trace * (exp (t • A)).det) t := by
  have h0 := hasDerivAt_det_exp_smul_zero A
  rw [← sub_self t] at h0
  have h := (h0.comp_sub_const t t).const_mul (exp (t • A)).det
  rw [mul_comm] at h
  convert h using 1
  funext s
  rw [← det_exp_add_smul, add_sub_cancel]

/-- `det (exp (t • A)) = exp (t • A.trace)` for every `t : 𝕂`. -/
theorem det_exp_smul (A : Matrix m m 𝕂) (t : 𝕂) :
    (exp (t • A)).det = exp (t • A.trace) := by
  set τ := A.trace
  set g : 𝕂 → 𝕂 := fun u => (exp (u • A)).det * exp (u • -τ) with hg
  have hd : ∀ u, HasDerivAt g 0 u := by
    intro u
    have h1 := hasDerivAt_det_exp_smul A u
    have h2 := hasDerivAt_exp_smul_const (𝕂 := 𝕂) (-τ) u
    convert h1.mul h2 using 1
    ring
  have hc := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t 0
  simp only [hg, zero_smul, exp_zero, det_one, mul_one] at hc
  rw [smul_neg, NormedSpace.exp_neg, mul_inv_eq_one₀ (NormedSpace.isUnit_exp _).ne_zero] at hc
  exact hc

/-- Jacobi's formula: `det (exp A) = exp (trace A)`, over any `RCLike` field. -/
theorem det_exp (A : Matrix m m 𝕂) : (exp A).det = exp A.trace := by
  simpa using det_exp_smul A 1

/-- Jacobi's formula over `ℝ`. -/
theorem det_exp_real (A : Matrix m m ℝ) : (exp A).det = Real.exp A.trace := by
  rw [Real.exp_eq_exp_ℝ]; exact det_exp A

/-- Jacobi's formula over `ℂ`. -/
theorem det_exp_complex (A : Matrix m m ℂ) : (exp A).det = Complex.exp A.trace := by
  rw [Complex.exp_eq_exp_ℂ]; exact det_exp A

end Matrix.DetExpODE
