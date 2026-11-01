import Mathlib

/-!
# Jacobi's formula `det (exp A) = exp (trace A)`

For a square matrix `A` over `𝕂` with `[RCLike 𝕂]` (so `ℝ` or `ℂ`), indexed by a `Fintype` with
`DecidableEq`, we prove `(NormedSpace.exp A).det = NormedSpace.exp A.trace`.

Route (ODE / uniqueness):
* `det` is differentiable, and its derivative at `1` sends `M` to `trace M`; the second fact is
  read off from the polynomial identity `Matrix.derivative_det_one_add_X_smul`.
* With `f t = det (exp (t • A))`, the chain rule gives `f' 0 = trace A`; the semigroup identity
  `exp ((t + s) • A) = exp (t • A) * exp (s • A)` then gives `f' t = trace A * f t` for all `t`.
* `g t = f t * exp (t • (-trace A))` has derivative `0` everywhere, so `g 1 = g 0 = 1`.

The norm on matrices used inside the proofs is the `L∞` operator norm
(`open scoped Matrix.Norms.Operator`), as in `Mathlib/Analysis/Normed/Algebra/MatrixExponential`.
The statements themselves do not depend on a choice of norm.
-/

open NormedSpace Matrix Polynomial

noncomputable section

namespace DetExpOde

variable {m 𝕂 : Type*} [Fintype m] [DecidableEq m] [RCLike 𝕂]

/-- The entry `M i j` as a `𝕂`-linear map. -/
def entryLin (i j : m) : Matrix m m 𝕂 →ₗ[𝕂] 𝕂 where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `det (1 + s • M)` is the evaluation at `s` of the polynomial `det (1 + X • M.map C)`. -/
theorem det_one_add_smul_eq_eval (M : Matrix m m 𝕂) (s : 𝕂) :
    (1 + s • M).det = (det (1 + (X : 𝕂[X]) • M.map C)).eval s := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h; simp; ring
  · simp [Matrix.one_apply_ne h]; ring

/-- `s ↦ det (1 + s • M)` has derivative `trace M` at `0`. -/
theorem hasDerivAt_det_one_add_smul (M : Matrix m m 𝕂) :
    HasDerivAt (fun s : 𝕂 => (1 + s • M).det) M.trace 0 := by
  have h := Polynomial.hasDerivAt (det (1 + (X : 𝕂[X]) • M.map C)) (0 : 𝕂)
  rw [Matrix.derivative_det_one_add_X_smul] at h
  simpa only [det_one_add_smul_eq_eval] using h

section Operator

open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false in
/-- The determinant is differentiable (with the operator norm on matrices). -/
theorem differentiable_det : Differentiable 𝕂 (fun M : Matrix m m 𝕂 => M.det) := by
  have hdet : (fun M : Matrix m m 𝕂 => M.det) =
      fun M => ∑ σ : Equiv.Perm m, ((Equiv.Perm.sign σ : ℤ) : 𝕂) * ∏ i, M (σ i) i := by
    funext M
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [hdet]
  refine Differentiable.fun_sum fun σ _ => ?_
  refine Differentiable.const_mul ?_ _
  intro M
  exact (HasFDerivAt.finsetProd (u := Finset.univ) (x := M)
    (g := fun i (N : Matrix m m 𝕂) => N (σ i) i) fun i _ =>
      (LinearMap.toContinuousLinearMap (entryLin (𝕂 := 𝕂) (σ i) i)).hasFDerivAt).differentiableAt

set_option backward.isDefEq.respectTransparency false in
/-- The derivative of `det` at `1` is the trace. -/
theorem fderiv_det_one_apply (M : Matrix m m 𝕂) :
    fderiv 𝕂 (fun M : Matrix m m 𝕂 => M.det) 1 M = M.trace := by
  have hL : HasFDerivAt (fun M : Matrix m m 𝕂 => M.det)
      (fderiv 𝕂 (fun M : Matrix m m 𝕂 => M.det) 1) (1 + (0 : 𝕂) • M) := by
    rw [zero_smul, add_zero]
    exact (differentiable_det (m := m) (𝕂 := 𝕂) 1).hasFDerivAt
  have hline : HasDerivAt (fun s : 𝕂 => 1 + s • M) ((1 : 𝕂) • M) 0 :=
    ((hasDerivAt_id (0 : 𝕂)).smul_const M).const_add 1
  have h := hL.comp_hasDerivAt (0 : 𝕂) hline
  rw [one_smul] at h
  exact h.unique (hasDerivAt_det_one_add_smul M)

set_option backward.isDefEq.respectTransparency false in
/-- `s ↦ det (exp (s • A))` has derivative `trace A` at `0`. -/
theorem hasDerivAt_det_exp_smul_zero (A : Matrix m m 𝕂) :
    HasDerivAt (fun s : 𝕂 => (exp (s • A)).det) A.trace 0 := by
  have hE := hasDerivAt_exp_smul_const' (𝕂 := 𝕂) A 0
  have hL : HasFDerivAt (fun M : Matrix m m 𝕂 => M.det)
      (fderiv 𝕂 (fun M : Matrix m m 𝕂 => M.det) 1) (exp ((0 : 𝕂) • A)) := by
    rw [zero_smul, exp_zero]
    exact (differentiable_det (m := m) (𝕂 := 𝕂) 1).hasFDerivAt
  have h := hL.comp_hasDerivAt (0 : 𝕂) hE
  rw [zero_smul, exp_zero, mul_one, fderiv_det_one_apply] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Semigroup identity `exp ((t + s) • A) = exp (t • A) * exp (s • A)`. -/
theorem exp_add_smul (A : Matrix m m 𝕂) (t s : 𝕂) :
    exp ((t + s) • A) = exp (t • A) * exp (s • A) := by
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl A).smul_left t).smul_right s)

end Operator

/-- Liouville's equation: `d/dt det (exp (t • A)) = trace A * det (exp (t • A))`. -/
theorem hasDerivAt_det_exp_smul (A : Matrix m m 𝕂) (t : 𝕂) :
    HasDerivAt (fun s : 𝕂 => (exp (s • A)).det) (A.trace * (exp (t • A)).det) t := by
  have h0 := hasDerivAt_det_exp_smul_zero A
  rw [← sub_self t] at h0
  have h1 := (h0.comp_sub_const t t).const_mul (exp (t • A)).det
  have heq : (fun s : 𝕂 => (exp (t • A)).det * (exp ((s - t) • A)).det) =
      fun s => (exp (s • A)).det := by
    funext s
    rw [← Matrix.det_mul, ← exp_add_smul, add_sub_cancel]
  rw [heq, mul_comm] at h1
  exact h1

/-- Jacobi's formula along the ray: `det (exp (t • A)) = exp (t • trace A)`. -/
theorem det_exp_smul (A : Matrix m m 𝕂) (t : 𝕂) :
    (exp (t • A)).det = exp (t • A.trace) := by
  set g : 𝕂 → 𝕂 := fun u => (exp (u • A)).det * exp (u • (-A.trace)) with hg
  have hd : ∀ u, HasDerivAt g 0 u := by
    intro u
    have h1 := hasDerivAt_det_exp_smul A u
    have h2 := hasDerivAt_exp_smul_const' (𝕂 := 𝕂) (-A.trace) u
    convert h1.mul h2 using 1
    ring
  have hc := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t 0
  simp only [hg, zero_smul, exp_zero, Matrix.det_one, mul_one] at hc
  have hinv : exp (t • A.trace) * exp (t • (-A.trace)) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.all _ _), smul_neg, add_neg_cancel, exp_zero]
  calc (exp (t • A)).det
      = (exp (t • A)).det * exp (t • (-A.trace)) * exp (t • A.trace) := by
        rw [mul_assoc, mul_comm (exp (t • (-A.trace))), hinv, mul_one]
    _ = exp (t • A.trace) := by rw [hc, one_mul]

/-- **Jacobi's formula** for the matrix exponential: `det (exp A) = exp (trace A)`,
for square matrices over `ℝ` or `ℂ` (any `RCLike` field). -/
theorem det_exp (A : Matrix m m 𝕂) : (exp A).det = exp A.trace := by
  simpa using det_exp_smul A 1

/-- Real case, stated with `Real.exp`. -/
theorem det_exp_real (A : Matrix m m ℝ) : (exp A).det = Real.exp A.trace := by
  rw [Real.exp_eq_exp_ℝ]
  exact det_exp A

/-- Complex case, stated with `Complex.exp`. -/
theorem det_exp_complex (A : Matrix m m ℂ) : (exp A).det = Complex.exp A.trace := by
  rw [Complex.exp_eq_exp_ℂ]
  exact det_exp A

end DetExpOde
