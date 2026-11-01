import Mathlib

/-!
# `det (exp A) = exp (trace A)` over `ℂ` and `ℝ`

For every square matrix `A` over `ℂ` or over `ℝ`, indexed by a finite type with decidable
equality, `(NormedSpace.exp A).det = NormedSpace.exp A.trace`. This closes the TODO in
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` for these two fields.

## Route

The density route (identity on diagonalizable matrices, then density of diagonalizable
matrices, then continuity) is replaced by its algebraic substitute, the Jordan–Chevalley
decomposition `Module.End.exists_isNilpotent_isSemisimple`, which avoids the density step
(no Zariski-density lemma for the discriminant and no Schur triangularization is available
in Mathlib). The identity is proved on:

* semisimple matrices over `ℂ` (`good_of_isSemisimple`): over an algebraically closed field a
  semisimple endomorphism has an eigenbasis (`IsSemisimple.iSup_eigenspace_eq_top`), so the
  matrix is `P * diagonal d * P⁻¹`, and `exp_conj`, `exp_diagonal`, `det_conj`, `trace_conj`
  reduce the claim to `∏ exp (d i) = exp (∑ d i)`;
* nilpotent matrices (`good_of_isNilpotent`): the trace is `0`, and `exp N = 1 + N'` with `N'`
  nilpotent, whose determinant is `1` because the characteristic polynomial of a nilpotent
  matrix is `X ^ card`;
* commuting sums (`good_add_of_commute`), via `exp_add_of_commute`.

The real case follows from the complex case by applying `Complex.ofReal` entrywise.
-/

open NormedSpace Matrix Polynomial

noncomputable section

namespace DetExpDensity

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The identity to be proved, as a predicate on complex matrices. -/
def Good (A : Matrix m m ℂ) : Prop := (exp A).det = exp A.trace

/-- The identity is stable under sums of commuting matrices. -/
theorem good_add_of_commute {A B : Matrix m m ℂ} (h : Commute A B) (hA : Good A) (hB : Good B) :
    Good (A + B) := by
  unfold Good at *
  rw [Matrix.exp_add_of_commute A B h, det_mul, hA, hB, trace_add, ← Complex.exp_eq_exp_ℂ,
    Complex.exp_add]

/-- The identity for a matrix with an eigenbasis `b` and eigenvalues `d`. -/
theorem good_of_eigenbasis (A : Matrix m m ℂ) (b : Module.Basis m ℂ (m → ℂ)) (d : m → ℂ)
    (hb : ∀ j, A *ᵥ b j = d j • b j) : Good A := by
  set P : Matrix m m ℂ := (Pi.basisFun ℂ m).toMatrix b with hPdef
  have hP : ∀ i j, P i j = b j i := by
    intro i j
    simp [hPdef, Module.Basis.toMatrix_apply]
  have hPu : IsUnit P := by
    let _ := Module.Basis.invertibleToMatrix (Pi.basisFun ℂ m) b
    exact isUnit_of_invertible P
  have hAP : A * P = P * diagonal d := by
    ext i j
    rw [mul_diagonal]
    have := congrFun (hb j) i
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [mul_apply, hP]
    rw [this, mul_comm]
  have hA : A = P * diagonal d * P⁻¹ := by
    rw [← hAP, Matrix.mul_nonsing_inv_cancel_right _ _ ((isUnit_iff_isUnit_det _).mp hPu)]
  unfold Good
  rw [hA, Matrix.exp_conj _ _ hPu, det_conj hPu, trace_conj hPu, exp_diagonal, det_diagonal,
    trace_diagonal, ← Complex.exp_eq_exp_ℂ, Complex.exp_sum, Pi.exp_def]
  simp [Complex.exp_eq_exp_ℂ]

/-- The identity for a matrix whose associated endomorphism is semisimple. -/
theorem good_of_isSemisimple (A : Matrix m m ℂ) (hA : Module.End.IsSemisimple (toLin' A)) :
    Good A := by
  set f := toLin' A with hf
  have hint : DirectSum.IsInternal (Module.End.eigenspace f) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨Module.End.eigenspaces_iSupIndep f, hA.iSup_eigenspace_eq_top⟩
  let v : ∀ μ : ℂ, Module.Basis (Fin (Module.finrank ℂ (Module.End.eigenspace f μ))) ℂ
      (Module.End.eigenspace f μ) :=
    fun μ => Module.finBasis ℂ _
  let b₀ := hint.collectedBasis v
  have : Finite (Σ μ : ℂ, Fin (Module.finrank ℂ (Module.End.eigenspace f μ))) :=
    Module.Finite.finite_basis b₀
  let _ : Fintype (Σ μ : ℂ, Fin (Module.finrank ℂ (Module.End.eigenspace f μ))) :=
    Fintype.ofFinite _
  have hcard : Fintype.card (Σ μ : ℂ, Fin (Module.finrank ℂ (Module.End.eigenspace f μ))) =
      Fintype.card m := by
    rw [← Module.finrank_eq_card_basis b₀, Module.finrank_fintype_fun_eq_card]
  let e := Fintype.equivOfCardEq hcard
  let b := b₀.reindex e
  refine good_of_eigenbasis A b (fun j => (e.symm j).1) fun j => ?_
  have hmem := hint.collectedBasis_mem v (e.symm j)
  rw [Module.End.mem_eigenspace_iff] at hmem
  simpa [b, b₀, Module.Basis.reindex_apply, hf, toLin'_apply] using hmem

/-- The determinant of `1 + N` is `1` when `N` is nilpotent. -/
theorem det_one_add_of_isNilpotent {N : Matrix m m ℂ} (hN : IsNilpotent N) : (1 + N).det = 1 := by
  have h1 : N.charpoly = X ^ Fintype.card m :=
    sub_eq_zero.mp (isNilpotent_charpoly_sub_pow_of_isNilpotent hN).eq_zero
  have h2 := eval_charpoly N (-1)
  have h3 : scalar m (-1) - N = -(1 + N) := by
    rw [map_neg, map_one, neg_add, sub_eq_add_neg]
  rw [h1, h3, det_neg, eval_pow, eval_X] at h2
  have h4 : ((-1 : ℂ) ^ Fintype.card m) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ h4 (h2.symm.trans (mul_one _).symm)

/-- `exp N - 1` is nilpotent when `N` is nilpotent. -/
theorem exp_sub_one_isNilpotent {N : Matrix m m ℂ} (hN : IsNilpotent N) :
    IsNilpotent (exp N - 1) := by
  obtain ⟨k, hk⟩ := hN
  have hsum : exp N = ∑ i ∈ Finset.range (k + 1), ((i.factorial : ℚ)⁻¹ : ℚ) • N ^ i := by
    rw [exp_eq_tsum_rat]
    exact tsum_eq_sum fun i hi => by
      simp only [Finset.mem_range, not_lt] at hi
      rw [pow_eq_zero_of_le (by omega : k ≤ i) hk, smul_zero]
  rw [hsum, Finset.sum_range_succ', pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    add_sub_cancel_right]
  have hmul : ∑ i ∈ Finset.range k, (((i + 1).factorial : ℚ)⁻¹ : ℚ) • N ^ (i + 1) =
      N * ∑ i ∈ Finset.range k, (((i + 1).factorial : ℚ)⁻¹ : ℚ) • N ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ', mul_smul_comm]
  rw [hmul]
  refine Commute.isNilpotent_mul_right ?_ ⟨k, hk⟩
  refine Commute.sum_right _ _ _ fun i _ => ?_
  exact (Commute.pow_right (Commute.refl N) i).smul_right _

/-- The identity for nilpotent matrices. -/
theorem good_of_isNilpotent {N : Matrix m m ℂ} (hN : IsNilpotent N) : Good N := by
  unfold Good
  have ht : N.trace = 0 := (isNilpotent_trace_of_isNilpotent hN).eq_zero
  rw [ht, NormedSpace.exp_zero]
  have := det_one_add_of_isNilpotent (exp_sub_one_isNilpotent hN)
  rwa [add_sub_cancel] at this

/-- The identity for every complex matrix, via the Jordan–Chevalley decomposition. -/
theorem good (A : Matrix m m ℂ) : Good A := by
  obtain ⟨n, hn, s, hs, hnil, hss, hf⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := toLin' A)
  have hc : Commute n s :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs
      (Algebra.commute_of_mem_adjoin_singleton_of_commute hn (Commute.refl _)).symm
  have hA : A = LinearMap.toMatrix' n + LinearMap.toMatrix' s := by
    rw [← map_add, ← hf, LinearMap.toMatrix'_toLin']
  rw [hA]
  refine good_add_of_commute (hc.map LinearMap.toMatrixAlgEquiv') ?_ ?_
  · exact good_of_isNilpotent (hnil.map LinearMap.toMatrixAlgEquiv')
  · refine good_of_isSemisimple _ ?_
    rwa [toLin'_toMatrix']

/-- Jacobi's formula over `ℂ`: `det (exp A) = exp (trace A)`. -/
theorem det_exp_complex (A : Matrix m m ℂ) : (exp A).det = exp A.trace := good A

section Real

open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false in
/-- Entrywise `Complex.ofReal` commutes with the matrix exponential. -/
theorem exp_map_ofReal (A : Matrix m m ℝ) :
    exp (A.map Complex.ofReal) = (exp A).map Complex.ofReal := by
  have h := map_exp (Complex.ofRealHom.mapMatrix : Matrix m m ℝ →+* Matrix m m ℂ)
    (Continuous.matrix_map continuous_id Complex.continuous_ofReal) A
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  exact h.symm

end Real

/-- Jacobi's formula over `ℝ`: `det (exp A) = exp (trace A)`. -/
theorem det_exp_real (A : Matrix m m ℝ) : (exp A).det = exp A.trace := by
  apply Complex.ofReal_injective
  have h := det_exp_complex (A.map Complex.ofReal)
  rw [exp_map_ofReal] at h
  have hdet : ((exp A).det : ℂ) = ((exp A).map Complex.ofReal).det := by
    have := RingHom.map_det Complex.ofRealHom (exp A)
    rw [RingHom.mapMatrix_apply] at this
    exact this
  have htr : (A.trace : ℂ) = (A.map Complex.ofReal).trace :=
    AddMonoidHom.map_trace Complex.ofRealHom A
  rw [hdet, h, ← htr, ← Complex.exp_eq_exp_ℂ, ← Real.exp_eq_exp_ℝ, Complex.ofReal_exp]

end DetExpDensity
