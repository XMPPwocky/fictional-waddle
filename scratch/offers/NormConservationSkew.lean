import Mathlib

/-!
# Norm conservation iff skew-symmetric generator

Setting: `A : Matrix (Fin n) (Fin n) ℝ`, trajectory `x t = exp (t • A) *ᵥ x0` with
`NormedSpace.exp`. The Euclidean norm of `v : Fin n → ℝ` is `euclNorm v`, the norm of `v` viewed
in `EuclideanSpace ℝ (Fin n)`; its square is `v ⬝ᵥ v` (`euclNorm_sq`).

PROVED
* `hasDerivAt_traj`: `t ↦ exp (t • A) *ᵥ x0` has derivative `A *ᵥ (exp (t • A) *ᵥ x0)`.
* `hasDerivAt_normSq_traj` (part a): `t ↦ |x t|^2` (written `x t ⬝ᵥ x t`) has derivative
  `2 * (x t ⬝ᵥ (A *ᵥ x t))` at every `t`.
* `hasDerivAt_euclNorm_sq_traj` (part a, norm form): the same with `euclNorm (x t) ^ 2`.
* `quadForm_zero_iff_skew` : `(∀ x, x ⬝ᵥ (A *ᵥ x) = 0) ↔ Aᵀ = -A`.
* `skew_iff_norm_preserving` : `Aᵀ = -A ↔ ∀ t x, euclNorm (exp (t • A) *ᵥ x) = euclNorm x`.
* `quadForm_zero_iff_norm_preserving` : `(∀ x, x ⬝ᵥ (A *ᵥ x) = 0) ↔ ∀ t x, ...` (so (i), (ii),
  (iii) of part (b) are pairwise equivalent; `tfae_skew` packages this as `List.TFAE`).
* `Aex_not_skew` (part c): `Aex = !![0, -1/2; 2, 0]` satisfies `Aexᵀ ≠ -Aex`.
* `Aex_eq_conj` : `Aex = S * J * S⁻¹` with `S = diag(1,2)`, `J = !![0,-1;1,0]`.
* `Aex_bounded` : `∀ t x, euclNorm (exp (t • Aex) *ᵥ x) ≤ 2 * euclNorm x`.
* `Aex_opNorm_bounded` : `∀ t, ‖toEuclideanCLM (exp (t • Aex))‖ ≤ 2`, i.e. the supremum over `t`
  of the Euclidean operator norm of `exp (t • Aex)` is finite (at most 2).
* `Aex_not_norm_preserving` : the flow of `Aex` does not preserve the Euclidean norm.
* `bounded_not_imp_skew` : the statement "if `sup_t ‖exp (t • A)‖ < ∞` then `Aᵀ = -A`" is false
  for `n = 2`.

INTERPRETED (not formalized)
* "sup over t of the operator norm is finite" is formalized as the existence of a uniform bound
  (`≤ 2`) on `‖toEuclideanCLM (exp (t • A))‖` for all real `t`.
-/

open NormedSpace Matrix

noncomputable section

namespace NormConservationSkew

variable {n : ℕ}

/-- Euclidean norm of a real vector indexed by `Fin n`. -/
def euclNorm (v : Fin n → ℝ) : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖

theorem euclNorm_sq (v : Fin n → ℝ) : euclNorm v ^ 2 = v ⬝ᵥ v := by
  rw [euclNorm, EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

theorem euclNorm_nonneg (v : Fin n → ℝ) : 0 ≤ euclNorm v := norm_nonneg _

theorem euclNorm_eq_sqrt (v : Fin n → ℝ) : euclNorm v = Real.sqrt (v ⬝ᵥ v) := by
  rw [← euclNorm_sq, Real.sqrt_sq (euclNorm_nonneg v)]

set_option backward.isDefEq.respectTransparency false in
/-- Entry `(i, j)` of `exp (u • A)` has derivative `(A * exp (t • A)) i j` at `t`. -/
theorem hasDerivAt_exp_smul_apply (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => exp (u • A) i j) ((A * exp (t • A)) i j) t := by
  open scoped Norms.Operator in
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t
  open scoped Norms.Operator in
  have hL := (LinearMap.toContinuousLinearMap (entryLinearMap ℝ ℝ i j)).hasFDerivAt
    (x := exp (t • A))
  exact hL.comp_hasDerivAt t h

/-- The trajectory `t ↦ exp (t • A) *ᵥ x0` solves `x' = A x`. -/
theorem hasDerivAt_traj (A : Matrix (Fin n) (Fin n) ℝ) (x0 : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => exp (u • A) *ᵥ x0) (A *ᵥ (exp (t • A) *ᵥ x0)) t := by
  rw [hasDerivAt_pi]
  intro i
  have h : HasDerivAt (fun u : ℝ => ∑ j, exp (u • A) i j * x0 j)
      (∑ j, (A * exp (t • A)) i j * x0 j) t :=
    HasDerivAt.fun_sum fun j _ => (hasDerivAt_exp_smul_apply A i j t).mul_const (x0 j)
  rw [mulVec_mulVec]
  exact h

/-- Part (a): `d/dt |x t|^2 = 2 ⟨x t, A x t⟩`. -/
theorem hasDerivAt_normSq_traj (A : Matrix (Fin n) (Fin n) ℝ) (x0 : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => (exp (u • A) *ᵥ x0) ⬝ᵥ (exp (u • A) *ᵥ x0))
      (2 * ((exp (t • A) *ᵥ x0) ⬝ᵥ (A *ᵥ (exp (t • A) *ᵥ x0)))) t := by
  have hx := hasDerivAt_traj A x0 t
  rw [hasDerivAt_pi] at hx
  have h : HasDerivAt (fun u : ℝ => ∑ i, (exp (u • A) *ᵥ x0) i * (exp (u • A) *ᵥ x0) i)
      (∑ i, ((A *ᵥ (exp (t • A) *ᵥ x0)) i * (exp (t • A) *ᵥ x0) i
        + (exp (t • A) *ᵥ x0) i * (A *ᵥ (exp (t • A) *ᵥ x0)) i)) t :=
    HasDerivAt.fun_sum fun i _ => (hx i).mul (hx i)
  convert h using 1
  · rfl
  · unfold dotProduct
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- Part (a), stated with the Euclidean norm. -/
theorem hasDerivAt_euclNorm_sq_traj (A : Matrix (Fin n) (Fin n) ℝ) (x0 : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => euclNorm (exp (u • A) *ᵥ x0) ^ 2)
      (2 * ((exp (t • A) *ᵥ x0) ⬝ᵥ (A *ᵥ (exp (t • A) *ᵥ x0)))) t := by
  simp only [euclNorm_sq]
  exact hasDerivAt_normSq_traj A x0 t

/-- (i) ↔ (ii). -/
theorem quadForm_zero_iff_skew (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) = 0) ↔ Aᵀ = -A := by
  constructor
  · intro h
    have hij : ∀ i j, Pi.single i (1 : ℝ) ⬝ᵥ (A *ᵥ Pi.single j 1) = A i j := by
      intro i j
      simp [mulVec_single]
    have hd : ∀ i, A i i = 0 := fun i => by rw [← hij]; exact h _
    ext i j
    have h2 := h (Pi.single i 1 + Pi.single j 1)
    simp only [mulVec_add, add_dotProduct, dotProduct_add, hij, hd] at h2
    simp only [transpose_apply, Matrix.neg_apply]
    linarith
  · intro h x
    have h1 : x ⬝ᵥ (A *ᵥ x) = (Aᵀ *ᵥ x) ⬝ᵥ x := by
      rw [dotProduct_mulVec, mulVec_transpose]
    rw [h, neg_mulVec, neg_dotProduct, dotProduct_comm (A *ᵥ x) x] at h1
    linarith

/-- (i) → (iii). -/
theorem norm_preserving_of_quadForm_zero (A : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) = 0) (t : ℝ) (x : Fin n → ℝ) :
    euclNorm (exp (t • A) *ᵥ x) = euclNorm x := by
  have hc : ∀ s : ℝ, HasDerivAt (fun u : ℝ => euclNorm (exp (u • A) *ᵥ x) ^ 2) 0 s := by
    intro s
    have := hasDerivAt_euclNorm_sq_traj A x s
    rwa [h, mul_zero] at this
  have hconst := is_const_of_deriv_eq_zero (fun s => (hc s).differentiableAt)
    (fun s => (hc s).deriv) t 0
  simp only [zero_smul, exp_zero, one_mulVec] at hconst
  exact (sq_eq_sq₀ (euclNorm_nonneg _) (euclNorm_nonneg _)).mp hconst

/-- (iii) → (i). -/
theorem quadForm_zero_of_norm_preserving (A : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ (t : ℝ) (x : Fin n → ℝ), euclNorm (exp (t • A) *ᵥ x) = euclNorm x)
    (x : Fin n → ℝ) : x ⬝ᵥ (A *ᵥ x) = 0 := by
  have hd := hasDerivAt_euclNorm_sq_traj A x 0
  have hfun : (fun u : ℝ => euclNorm (exp (u • A) *ᵥ x) ^ 2) = fun _ => euclNorm x ^ 2 := by
    funext u; rw [h]
  rw [hfun] at hd
  have h0 := hd.unique (hasDerivAt_const (0 : ℝ) (euclNorm x ^ 2))
  simp only [zero_smul, exp_zero, one_mulVec] at h0
  linarith

/-- (i) ↔ (iii). -/
theorem quadForm_zero_iff_norm_preserving (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) = 0) ↔
      ∀ (t : ℝ) (x : Fin n → ℝ), euclNorm (exp (t • A) *ᵥ x) = euclNorm x :=
  ⟨norm_preserving_of_quadForm_zero A, quadForm_zero_of_norm_preserving A⟩

/-- (ii) ↔ (iii). -/
theorem skew_iff_norm_preserving (A : Matrix (Fin n) (Fin n) ℝ) :
    Aᵀ = -A ↔ ∀ (t : ℝ) (x : Fin n → ℝ), euclNorm (exp (t • A) *ᵥ x) = euclNorm x :=
  (quadForm_zero_iff_skew A).symm.trans (quadForm_zero_iff_norm_preserving A)

/-- Part (b): the three conditions are equivalent. -/
theorem tfae_skew (A : Matrix (Fin n) (Fin n) ℝ) :
    List.TFAE [∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) = 0, Aᵀ = -A,
      ∀ (t : ℝ) (x : Fin n → ℝ), euclNorm (exp (t • A) *ᵥ x) = euclNorm x] := by
  tfae_have 1 ↔ 2 := quadForm_zero_iff_skew A
  tfae_have 1 ↔ 3 := quadForm_zero_iff_norm_preserving A
  tfae_finish

/-! ### Part (c): a bounded flow whose generator is not skew-symmetric -/

/-- `S = diag(1, 2)`. -/
def S : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 2]

/-- `S⁻¹ = diag(1, 1/2)`. -/
def Sinv : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1 / 2]

/-- The rotation generator `J`. -/
def J : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The example generator `Aex = S J S⁻¹`. -/
def Aex : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1 / 2; 2, 0]

theorem Sinv_mul_S : Sinv * S = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Sinv, S]

theorem S_mul_Sinv : S * Sinv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Sinv, S]

theorem S_inv : S⁻¹ = Sinv := Matrix.inv_eq_left_inv Sinv_mul_S

theorem isUnit_S : IsUnit S := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [S, Matrix.det_fin_two]

theorem Aex_eq_conj : Aex = S * J * S⁻¹ := by
  rw [S_inv]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Aex, S, J, Sinv, Matrix.mul_apply, Fin.sum_univ_two]

theorem Aex_not_skew : Aexᵀ ≠ -Aex := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [Aex] at this
  norm_num at this

theorem J_skew : Jᵀ = -J := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J]

theorem euclNorm_S_mulVec_le (v : Fin 2 → ℝ) : euclNorm (S *ᵥ v) ≤ 2 * euclNorm v := by
  rw [← abs_of_nonneg (euclNorm_nonneg (S *ᵥ v)),
    ← abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (euclNorm_nonneg v))]
  apply sq_le_sq.mp
  rw [mul_pow, euclNorm_sq, euclNorm_sq]
  simp [S, dotProduct, Fin.sum_univ_two, mulVec]
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

theorem euclNorm_Sinv_mulVec_le (v : Fin 2 → ℝ) : euclNorm (Sinv *ᵥ v) ≤ euclNorm v := by
  rw [← abs_of_nonneg (euclNorm_nonneg (Sinv *ᵥ v)), ← abs_of_nonneg (euclNorm_nonneg v)]
  apply sq_le_sq.mp
  rw [euclNorm_sq, euclNorm_sq]
  simp [Sinv, dotProduct, Fin.sum_univ_two, mulVec]
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

theorem exp_smul_Aex (t : ℝ) : exp (t • Aex) = S * exp (t • J) * Sinv := by
  rw [Aex_eq_conj, ← S_inv, ← Matrix.exp_conj _ _ isUnit_S]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem Aex_bounded (t : ℝ) (x : Fin 2 → ℝ) :
    euclNorm (exp (t • Aex) *ᵥ x) ≤ 2 * euclNorm x := by
  rw [exp_smul_Aex, ← mulVec_mulVec, ← mulVec_mulVec]
  calc euclNorm (S *ᵥ (exp (t • J) *ᵥ (Sinv *ᵥ x)))
      ≤ 2 * euclNorm (exp (t • J) *ᵥ (Sinv *ᵥ x)) := euclNorm_S_mulVec_le _
    _ = 2 * euclNorm (Sinv *ᵥ x) := by
        rw [(skew_iff_norm_preserving J).mp J_skew t]
    _ ≤ 2 * euclNorm x := by
        have := euclNorm_Sinv_mulVec_le x
        linarith

theorem Aex_opNorm_bounded (t : ℝ) : ‖toEuclideanCLM (𝕜 := ℝ) (exp (t • Aex))‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  obtain ⟨w, rfl⟩ : ∃ w : Fin 2 → ℝ, v = WithLp.toLp 2 w := ⟨WithLp.ofLp v, rfl⟩
  rw [toEuclideanCLM_toLp]
  exact Aex_bounded t w

theorem Aex_not_norm_preserving :
    ¬ ∀ (t : ℝ) (x : Fin 2 → ℝ), euclNorm (exp (t • Aex) *ᵥ x) = euclNorm x := fun h =>
  Aex_not_skew ((skew_iff_norm_preserving Aex).mpr h)

/-- The slogan "bounded flow implies skew-symmetric generator" fails for `n = 2`. -/
theorem bounded_not_imp_skew :
    ¬ ∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      (∃ C : ℝ, ∀ t : ℝ, ‖toEuclideanCLM (𝕜 := ℝ) (exp (t • A))‖ ≤ C) → Aᵀ = -A :=
  fun h => Aex_not_skew (h Aex ⟨2, Aex_opNorm_bounded⟩)

end NormConservationSkew
