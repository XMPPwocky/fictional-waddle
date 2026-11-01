import Mathlib

/-!
# Imaginary-time descent shrinks the norm; real-time rotation preserves it

Throughout, `H : Matrix (Fin n) (Fin n) ℂ`, vectors are `Fin n → ℂ`, and
`nsq v = ∑ i, ‖v i‖ ^ 2` is the squared Euclidean norm; `nsq_eq_norm_sq` identifies it with
`‖WithLp.toLp 2 v‖ ^ 2` in `EuclideanSpace ℂ (Fin n)`. (The default norm on `Fin n → ℂ` is the
sup norm, for which the contraction statement is false in general, so the Euclidean norm is used.)
The matrix exponential is `NormedSpace.exp`; sections (c) and (d) use Mathlib's local
`linftyOp` normed-algebra instances on matrices only to access the exponential's calculus lemmas
(the exponential itself does not depend on the choice of norm).

PROVED
* `hasDerivAt_nsq`: if `ψ` has derivative `ψ'` at `t`, then `s ↦ nsq (ψ s)` has derivative
  `2 Re ⟨ψ t, ψ'⟩` at `t`.
* `nsq_eq_re_dotProduct`: `nsq v = Re ⟨v, v⟩`.
* `inner_mulVec_star_eq`, `inner_mulVec_im_eq_zero`: for Hermitian `H`, `⟨x, H x⟩` is real.
* `imag_time_hasDerivAt` (a): if `ψ' = -H ψ` and `H` is positive semidefinite, then
  `d/dt nsq (ψ t) = -2 Re ⟨ψ t, H ψ t⟩` and this is `≤ 0`.
* `imag_time_antitone` (a): under the same hypotheses `t ↦ nsq (ψ t)` is antitone.
* `imag_time_const_iff` (a): for `a < b`, `nsq ∘ ψ` is constant on `[a, b]` iff
  `H *ᵥ ψ t = 0` for every `t ∈ [a, b]`.
* `real_time_hasDerivAt` (b): if `ψ' = -i H ψ` with `H` Hermitian (no PSD needed), then
  `d/dt nsq (ψ t) = 0`.
* `real_time_nsq_const`, `real_time_norm_const` (b): then `nsq (ψ s) = nsq (ψ t)` and
  the Euclidean norms `‖ψ s‖ = ‖ψ t‖` agree for all `s t`.
* `hasDerivAt_exp_mulVec`: `d/dt (exp (t A) *ᵥ v) = A *ᵥ (exp (t A) *ᵥ v)`.
* `exp_neg_smul_contraction`, `exp_neg_smul_norm_le` (c): for `H` PSD and `t ≥ 0`,
  `nsq (exp (-t H) *ᵥ v) ≤ nsq v`, equivalently `‖exp (-t H) *ᵥ v‖ ≤ ‖v‖` (Euclidean).
* `exp_neg_I_smul_mem_unitary` (c): for `H` Hermitian and real `t`, `exp (-(i t) H)` is unitary.
* `nsq_unitary_mulVec`, `unitary_norm_mulVec`: unitary matrices preserve the Euclidean norm.
* `exp_nat_eq_pow`: `exp (-(i m) H) = exp (-i H) ^ m` for natural `m`.
* `recurrence` (d, Bocchieri–Loinger): for `H` Hermitian, any `v`, `ε > 0` and `T`, there is a
  real `t > T` (in fact a natural number) with `‖exp (-(i t) H) *ᵥ v - v‖ < ε` (Euclidean).
  The proof uses compactness of the orbit `U ^ m v` (`U = exp (-i H)`) instead of
  simultaneous Dirichlet approximation of the eigenvalue phases.
-/

namespace ImaginaryTimeContraction

open Matrix NormedSpace
open scoped ComplexOrder

variable {n : ℕ}

/-- Squared Euclidean norm of a complex vector. -/
noncomputable def nsq (v : Fin n → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

theorem nsq_eq_norm_sq (v : Fin n → ℂ) :
    nsq v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  rfl

theorem nsq_eq_re_dotProduct (v : Fin n → ℂ) : nsq v = (star v ⬝ᵥ v).re := by
  simp only [nsq, dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

theorem hasDerivAt_nsq {ψ : ℝ → Fin n → ℂ} {ψ' : Fin n → ℂ} {t : ℝ} (h : HasDerivAt ψ ψ' t) :
    HasDerivAt (fun s => nsq (ψ s)) (2 * (star (ψ t) ⬝ᵥ ψ').re) t := by
  have hi : ∀ i, HasDerivAt (fun s => ‖ψ s i‖ ^ 2) (2 * inner ℝ (ψ t i) (ψ' i)) t :=
    fun i => (hasDerivAt_pi.1 h i).norm_sq
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
  have hf : (fun s => nsq (ψ s)) = fun y => ∑ i, ‖ψ y i‖ ^ 2 := rfl
  rw [hf]
  convert hs using 1
  rw [← Finset.mul_sum]
  congr 1
  simp only [dotProduct, Complex.re_sum, Complex.inner, Pi.star_apply, Complex.star_def,
    mul_comm]

theorem inner_mulVec_star_eq {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (x : Fin n → ℂ) : star (star x ⬝ᵥ (H *ᵥ x)) = star x ⬝ᵥ (H *ᵥ x) := by
  rw [← star_dotProduct_star, star_star, star_mulVec, hH.eq, ← dotProduct_mulVec]

theorem inner_mulVec_im_eq_zero {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (x : Fin n → ℂ) : (star x ⬝ᵥ (H *ᵥ x)).im = 0 :=
  Complex.conj_eq_iff_im.1 (inner_mulVec_star_eq hH x)

/-! ## (a) imaginary time -/

theorem imag_time_hasDerivAt {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosSemidef)
    {ψ : ℝ → Fin n → ℂ} (hψ : ∀ t, HasDerivAt ψ (-(H *ᵥ ψ t)) t) (t : ℝ) :
    HasDerivAt (fun s => nsq (ψ s)) (-2 * (star (ψ t) ⬝ᵥ (H *ᵥ ψ t)).re) t ∧
      -2 * (star (ψ t) ⬝ᵥ (H *ᵥ ψ t)).re ≤ 0 := by
  refine ⟨?_, ?_⟩
  · convert hasDerivAt_nsq (hψ t) using 1
    rw [dotProduct_neg, Complex.neg_re]; ring
  · have h0 := hH.dotProduct_mulVec_nonneg (ψ t)
    have := (Complex.le_def.1 h0).1
    simp only [Complex.zero_re] at this
    linarith

theorem imag_time_antitone {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosSemidef)
    {ψ : ℝ → Fin n → ℂ} (hψ : ∀ t, HasDerivAt ψ (-(H *ᵥ ψ t)) t) :
    Antitone fun t => nsq (ψ t) :=
  antitone_of_hasDerivAt_nonpos (fun t => (imag_time_hasDerivAt hH hψ t).1)
    fun t => (imag_time_hasDerivAt hH hψ t).2

theorem imag_time_const_iff {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosSemidef)
    {ψ : ℝ → Fin n → ℂ} (hψ : ∀ t, HasDerivAt ψ (-(H *ᵥ ψ t)) t) {a b : ℝ} (hab : a < b) :
    (∀ t ∈ Set.Icc a b, nsq (ψ t) = nsq (ψ a)) ↔ ∀ t ∈ Set.Icc a b, H *ᵥ ψ t = 0 := by
  constructor
  · intro hc t ht
    have h1 : HasDerivWithinAt (fun s => nsq (ψ s)) 0 (Set.Icc a b) t :=
      (hasDerivWithinAt_const t (Set.Icc a b) (nsq (ψ a))).congr (fun s hs => hc s hs) (hc t ht)
    have h2 := ((imag_time_hasDerivAt hH hψ t).1).hasDerivWithinAt (s := Set.Icc a b)
    have he := (uniqueDiffOn_Icc hab t ht).eq_deriv _ h1 h2
    have hre : (star (ψ t) ⬝ᵥ (H *ᵥ ψ t)).re = 0 := by linarith
    have him := inner_mulVec_im_eq_zero hH.isHermitian (ψ t)
    have hz : star (ψ t) ⬝ᵥ (H *ᵥ ψ t) = 0 := Complex.ext hre him
    exact hH.dotProduct_mulVec_zero_iff.1 hz
  · intro hz
    have hd : ∀ t ∈ Set.Icc a b, HasDerivAt (fun s => nsq (ψ s)) 0 t := by
      intro t ht
      have := (imag_time_hasDerivAt hH hψ t).1
      rwa [hz t ht, dotProduct_zero, Complex.zero_re, mul_zero] at this
    have hcont : ContinuousOn (fun s => nsq (ψ s)) (Set.Icc a b) := fun t _ =>
      ((imag_time_hasDerivAt hH hψ t).1).continuousAt.continuousWithinAt
    exact constant_of_has_deriv_right_zero hcont fun t ht =>
      (hd t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt

/-! ## (b) real time -/

theorem real_time_hasDerivAt {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    {ψ : ℝ → Fin n → ℂ} (hψ : ∀ t, HasDerivAt ψ (-(Complex.I • (H *ᵥ ψ t))) t) (t : ℝ) :
    HasDerivAt (fun s => nsq (ψ s)) 0 t := by
  convert hasDerivAt_nsq (hψ t) using 1
  rw [dotProduct_neg, dotProduct_smul, smul_eq_mul, Complex.neg_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, inner_mulVec_im_eq_zero hH]
  ring

theorem real_time_nsq_const {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    {ψ : ℝ → Fin n → ℂ} (hψ : ∀ t, HasDerivAt ψ (-(Complex.I • (H *ᵥ ψ t))) t) (s t : ℝ) :
    nsq (ψ s) = nsq (ψ t) :=
  is_const_of_deriv_eq_zero (fun x => (real_time_hasDerivAt hH hψ x).differentiableAt)
    (fun x => (real_time_hasDerivAt hH hψ x).deriv) s t

theorem real_time_norm_const {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    {ψ : ℝ → Fin n → ℂ} (hψ : ∀ t, HasDerivAt ψ (-(Complex.I • (H *ᵥ ψ t))) t) (s t : ℝ) :
    ‖(WithLp.toLp 2 (ψ s) : EuclideanSpace ℂ (Fin n))‖ =
      ‖(WithLp.toLp 2 (ψ t) : EuclideanSpace ℂ (Fin n))‖ := by
  have h := real_time_nsq_const hH hψ s t
  rw [nsq_eq_norm_sq, nsq_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-! ## (c) the propagators -/

section propagators

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The linear map `M ↦ M *ᵥ v`. -/
def mulVecRight (v : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin n → ℂ) where
  toFun M := M *ᵥ v
  map_add' M N := add_mulVec M N v
  map_smul' c M := by
    ext i
    simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem hasDerivAt_exp_mulVec (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • A) *ᵥ v) (A *ᵥ (exp (t • A) *ᵥ v)) t := by
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t
  have hL := (LinearMap.toContinuousLinearMap (mulVecRight v)).hasFDerivAt.comp_hasDerivAt t h
  convert hL using 1
  · rfl
  · change A *ᵥ (exp (t • A) *ᵥ v) = (A * exp (t • A)) *ᵥ v
    rw [mulVec_mulVec]

theorem exp_neg_smul_contraction {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosSemidef)
    (v : Fin n → ℂ) {t : ℝ} (ht : 0 ≤ t) : nsq (exp ((-t) • H) *ᵥ v) ≤ nsq v := by
  have hψ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => exp (s • (-H)) *ᵥ v)
      (-(H *ᵥ (exp (s • (-H)) *ᵥ v))) s := fun s => by
    simpa [neg_mulVec] using hasDerivAt_exp_mulVec (-H) v s
  have h := imag_time_antitone hH hψ ht
  simp only [zero_smul, exp_zero, one_mulVec] at h
  simpa [smul_neg, neg_smul] using h

theorem exp_neg_smul_norm_le {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosSemidef)
    (v : Fin n → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖(WithLp.toLp 2 (exp ((-t) • H) *ᵥ v) : EuclideanSpace ℂ (Fin n))‖ ≤
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ := by
  have h := exp_neg_smul_contraction hH v ht
  rw [nsq_eq_norm_sq, nsq_eq_norm_sq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem exp_neg_I_smul_mem_unitary {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (t : ℝ) : exp ((-(Complex.I * t)) • H) ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
  set X : Matrix (Fin n) (Fin n) ℂ := (-(Complex.I * t)) • H with hX
  have hstar : star X = -X := by
    rw [hX, star_eq_conjTranspose, conjTranspose_smul, hH.eq, ← neg_smul]
    congr 1
    simp
  have hs : star (exp X) = exp (-X) := by
    rw [star_eq_conjTranspose, ← exp_conjTranspose, ← star_eq_conjTranspose, hstar]
  rw [Unitary.mem_iff, hs]
  constructor
  · rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
      exp_zero]
  · rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl X)), add_neg_cancel,
      exp_zero]

end propagators

theorem nsq_unitary_mulVec {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) (x : Fin n → ℂ) : nsq (U *ᵥ x) = nsq x := by
  rw [nsq_eq_re_dotProduct, nsq_eq_re_dotProduct, star_mulVec, ← dotProduct_mulVec,
    mulVec_mulVec, ← star_eq_conjTranspose, (Unitary.mem_iff.1 hU).1, one_mulVec]

theorem unitary_norm_mulVec {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) (x : Fin n → ℂ) :
    ‖(WithLp.toLp 2 (U *ᵥ x) : EuclideanSpace ℂ (Fin n))‖ =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖ := by
  have h := nsq_unitary_mulVec hU x
  rw [nsq_eq_norm_sq, nsq_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-! ## (d) recurrence -/

section recurrence

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_nat_eq_pow (H : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    exp ((-(Complex.I * ((m : ℝ) : ℂ))) • H) = exp ((-Complex.I) • H) ^ m := by
  rw [← Matrix.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 2
  push_cast
  ring

theorem recurrence {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (v : Fin n → ℂ)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    ∃ t : ℝ, T < t ∧
      ‖(WithLp.toLp 2 (exp ((-(Complex.I * t)) • H) *ᵥ v - v) : EuclideanSpace ℂ (Fin n))‖
        < ε := by
  set U := exp ((-Complex.I) • H) with hUdef
  have hU : U ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
    have h1 := exp_neg_I_smul_mem_unitary hH 1
    have h2 : (-(Complex.I * ((1 : ℝ) : ℂ))) • H = (-Complex.I) • H := by simp
    rwa [h2, ← hUdef] at h1
  have hUm : ∀ m : ℕ, U ^ m ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
    fun m => pow_mem hU m
  let e : ℕ → EuclideanSpace ℂ (Fin n) := fun m => WithLp.toLp 2 (U ^ m *ᵥ v)
  have he : ∀ m, e m ∈ Metric.closedBall (0 : EuclideanSpace ℂ (Fin n))
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ := fun m => by
    simp only [Metric.mem_closedBall, dist_zero_right, e, unitary_norm_mulVec (hUm m) v,
      le_refl]
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall _ _).tendsto_subseq he
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq ε hε
  set k := max N (φ N + ⌈T⌉₊ + 1) with hk
  have hkN : N ≤ k := le_max_left _ _
  have hφk : φ N + ⌈T⌉₊ + 1 ≤ φ k := (le_max_right _ _).trans (hφ.id_le k)
  obtain ⟨d, hd⟩ : ∃ d, φ k = φ N + d := ⟨φ k - φ N, by omega⟩
  refine ⟨(d : ℝ), ?_, ?_⟩
  · have h1 : ⌈T⌉₊ + 1 ≤ d := by omega
    have h2 : (⌈T⌉₊ : ℝ) + 1 ≤ d := by exact_mod_cast h1
    linarith [Nat.le_ceil T]
  · have hdist := hN k hkN
    rw [exp_nat_eq_pow, ← hUdef]
    have : dist (e (φ k)) (e (φ N)) =
        ‖(WithLp.toLp 2 (U ^ d *ᵥ v - v) : EuclideanSpace ℂ (Fin n))‖ := by
      simp only [e]
      rw [dist_eq_norm, ← WithLp.toLp_sub, hd, pow_add, ← mulVec_mulVec, ← mulVec_sub,
        unitary_norm_mulVec (hUm _)]
    rw [← this]
    exact hdist

end recurrence

end ImaginaryTimeContraction
