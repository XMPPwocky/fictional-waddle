import Mathlib

/-!
# `det (exp A) = exp (trace A)` via generalized eigenspaces

Every `exp` below is `NormedSpace.exp`.

Main results:
* `DetExpEigen7.det_exp_complex`: for `A : Matrix m m ℂ`, `(exp A).det = exp A.trace`.
* `DetExpEigen7.det_exp_real`: for `A : Matrix m m ℝ`, `(exp A).det = exp A.trace`.
* `DetExpEigen7.det_exp_complex'`, `DetExpEigen7.det_exp_real'`: the same with `Complex.exp`
  and `Real.exp` on the right-hand side.

Route (over `ℂ`): `ℂ^m` is the internal direct sum of the generalized eigenspaces of
`toLin' A` (`Module.End.iSup_maxGenEigenspace_eq_top`), only finitely many of which are nonzero.
In a basis adapted to this decomposition the matrix of `A` is block diagonal
(`LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal'`), and each block is
`μ • 1 + N` with `N` nilpotent (`isNilpotent_restrict_maxGenEigenspace_sub_algebraMap`).
For such a block, `exp (μ • 1 + N) = (exp μ • 1) * exp N`, `det (exp N) = 1` because `exp N - 1`
is nilpotent, and `trace N = 0`. `exp`, `det` and `trace` are compatible with block-diagonal
matrices, and `exp` commutes with the (continuous) algebra equivalence `Matrix.toLin'` followed by
`LinearMap.toMatrix` in the adapted basis. The real case follows by mapping `ℝ → ℂ`.

Helper lemmas proved on the way: `det_blockDiagonal'` (determinant of a block diagonal matrix
with blocks of varying size), `det_one_add_of_isNilpotent`, `det_exp_of_isNilpotent`.
-/

open NormedSpace Matrix

noncomputable section

namespace DetExpEigen7

/-! ### Determinant of a block-diagonal matrix with blocks of varying size -/

/-- The fibre of `Sigma.fst` over `a` is `κ a` (helper). -/
def sigmaFiberEquiv {α : Type*} (κ : α → Type*) (a : α) : {p : Σ i, κ i // p.1 = a} ≃ κ a where
  toFun p := cast (congrArg κ p.2) p.1.2
  invFun k := ⟨⟨a, k⟩, rfl⟩
  left_inv p := by
    rcases p with ⟨⟨i, k⟩, hp⟩
    dsimp only at hp
    subst hp
    rfl
  right_inv _ := rfl

/-- The diagonal square block of `blockDiagonal' d` at `a` is `d a` up to reindexing (helper). -/
theorem toSquareBlock_blockDiagonal' {α : Type*} [DecidableEq α] {κ : α → Type*} {R : Type*}
    [CommRing R] (d : ∀ a, Matrix (κ a) (κ a) R) (a : α) :
    (blockDiagonal' d).toSquareBlock Sigma.fst a =
      (d a).submatrix (sigmaFiberEquiv κ a) (sigmaFiberEquiv κ a) := by
  ext ⟨⟨i, k⟩, hi⟩ ⟨⟨j, l⟩, hj⟩
  dsimp only at hi hj
  subst hi
  subst hj
  simp [toSquareBlock_def, sigmaFiberEquiv, Matrix.blockDiagonal'_apply_eq]

/-- The determinant of a block-diagonal matrix (blocks of varying size) is the product of the
determinants of the blocks. -/
theorem det_blockDiagonal' {α : Type*} [Fintype α] [DecidableEq α] {κ : α → Type*}
    [∀ a, Fintype (κ a)] [∀ a, DecidableEq (κ a)] {R : Type*} [CommRing R]
    (d : ∀ a, Matrix (κ a) (κ a) R) : (blockDiagonal' d).det = ∏ a, (d a).det := by
  let _ : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  rw [(blockTriangular_blockDiagonal' d).det_fintype]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [toSquareBlock_blockDiagonal', det_submatrix_equiv_self]

/-! ### Nilpotent matrices -/

section Nilpotent

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `det (1 + X) = 1` for a nilpotent matrix `X` over a field. -/
theorem det_one_add_of_isNilpotent {K : Type*} [Field K] {X : Matrix n n K}
    (hX : IsNilpotent X) : (1 + X).det = 1 := by
  have h1 : X.charpoly = Polynomial.X ^ Fintype.card n :=
    sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hX).eq_zero
  have h2 := Matrix.eval_charpoly X (-1)
  rw [h1, Polynomial.eval_pow, Polynomial.eval_X] at h2
  have h3 : Matrix.scalar n (-1 : K) - X = -(1 + X) := by
    rw [map_neg, map_one, neg_add, sub_eq_add_neg]
  rw [h3, det_neg] at h2
  have h4 : ((-1 : K) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  exact mul_left_cancel₀ h4 (h2.symm.trans (mul_one _).symm)

/-- For a nilpotent matrix over `ℂ`, `NormedSpace.exp` agrees with the algebraic (finite-sum)
exponential `IsNilpotent.exp` (helper). -/
theorem exp_eq_isNilpotent_exp {N : Matrix n n ℂ} (hN : IsNilpotent N) :
    exp N = IsNilpotent.exp N := by
  obtain ⟨k, hk⟩ := hN
  rw [IsNilpotent.exp_eq_sum hk, exp_eq_tsum_rat]
  exact tsum_eq_sum fun i hi => by
    rw [pow_eq_zero_of_le (by simpa using hi) hk, smul_zero]

/-- The exponential of a nilpotent matrix over `ℂ` has determinant `1`. -/
theorem det_exp_of_isNilpotent {N : Matrix n n ℂ} (hN : IsNilpotent N) : (exp N).det = 1 := by
  have h := IsNilpotent.isNilpotent_exp_sub_one hN
  have h' : IsNilpotent.exp N = 1 + (IsNilpotent.exp N - 1) := by abel
  rw [exp_eq_isNilpotent_exp hN, h', det_one_add_of_isNilpotent h]

end Nilpotent

/-! ### One generalized eigenspace block: `μ • 1 + nilpotent` -/

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
/-- Jacobi's formula for a matrix of the form `diagonal (fun _ => μ) + N` with `N` nilpotent
(helper). -/
theorem det_exp_diagonal_add {κ : Type*} [Fintype κ] [DecidableEq κ] (μ : ℂ)
    {N : Matrix κ κ ℂ} (hN : IsNilpotent N) :
    (exp (diagonal (fun _ => μ) + N)).det = exp (diagonal (fun _ => μ) + N).trace := by
  have hc : Commute (diagonal (fun _ : κ => μ)) N := by
    rw [← smul_one_eq_diagonal]
    exact (Commute.one_left N).smul_left μ
  have h1 : exp (diagonal (fun _ : κ => μ) + N) = exp (diagonal (fun _ => μ)) * exp N :=
    Matrix.exp_add_of_commute _ _ hc
  have h2 : exp (diagonal (fun _ : κ => μ)) = diagonal (fun _ => exp μ) := by
    rw [exp_diagonal, Pi.exp_def]
  have h3 : N.trace = 0 := (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero
  rw [h1, h2, det_mul, det_diagonal, det_exp_of_isNilpotent hN, trace_add, trace_diagonal, h3,
    add_zero, Finset.prod_const, Finset.sum_const, Finset.card_univ, NormedSpace.exp_nsmul,
    mul_one]

/-! ### Main theorem over `ℂ` -/

variable {m : Type*} [Fintype m] [DecidableEq m]

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
/-- Jacobi's formula over `ℂ`: the determinant of the matrix exponential is the exponential of the
trace. Both `exp`s are `NormedSpace.exp`. -/
theorem det_exp_complex (A : Matrix m m ℂ) : (exp A).det = exp A.trace := by
  classical
  let f : Module.End ℂ (m → ℂ) := Matrix.toLin' A
  have hind : iSupIndep f.maxGenEigenspace := f.independent_maxGenEigenspace
  have hds : DirectSum.IsInternal f.maxGenEigenspace :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind
      (Module.End.iSup_maxGenEigenspace_eq_top f)
  have h_fin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  let _ : Fintype {μ // f.maxGenEigenspace μ ≠ ⊥} := h_fin.fintype
  have h : DirectSum.IsInternal (fun μ : {μ // f.maxGenEigenspace μ ≠ ⊥} => f.maxGenEigenspace μ) :=
    DirectSum.isInternal_ne_bot_iff.mpr hds
  let κ : {μ // f.maxGenEigenspace μ ≠ ⊥} → Type _ := fun μ => Module.Free.ChooseBasisIndex ℂ (f.maxGenEigenspace μ)
  let b : ∀ μ : {μ // f.maxGenEigenspace μ ≠ ⊥}, Module.Basis (κ μ) ℂ (f.maxGenEigenspace μ) :=
    fun μ => Module.Free.chooseBasis ℂ (f.maxGenEigenspace μ)
  let c : Module.Basis (Σ μ : {μ // f.maxGenEigenspace μ ≠ ⊥}, κ μ) ℂ (m → ℂ) := h.collectedBasis b
  have hmaps : ∀ μ : {μ // f.maxGenEigenspace μ ≠ ⊥}, Set.MapsTo f (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    fun μ => f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ
  let d : ∀ μ : {μ // f.maxGenEigenspace μ ≠ ⊥}, Matrix (κ μ) (κ μ) ℂ :=
    fun μ => LinearMap.toMatrix (b μ) (b μ) (f.restrict (hmaps μ))
  have hB : LinearMap.toMatrix c c (Matrix.toLin' A) = Matrix.blockDiagonal' d :=
    LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal' h h b b hmaps
  -- each block is `diagonal (fun _ => μ) + nilpotent`
  have hd : ∀ μ : {μ // f.maxGenEigenspace μ ≠ ⊥}, ∃ Nμ : Matrix (κ μ) (κ μ) ℂ,
      IsNilpotent Nμ ∧ d μ = diagonal (fun _ => (μ : ℂ)) + Nμ := by
    intro μ
    have hmaps' := f.mapsTo_maxGenEigenspace_of_comm
      (Algebra.mul_sub_algebraMap_commutes f (μ : ℂ)) (μ : ℂ)
    refine ⟨LinearMap.toMatrix (b μ) (b μ)
      ((f - algebraMap ℂ (Module.End ℂ (m → ℂ)) (μ : ℂ)).restrict hmaps'), ?_, ?_⟩
    · exact (LinearMap.isNilpotent_toMatrix_iff _ _).mpr
        (f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (μ : ℂ))
    · have hsplit : f.restrict (hmaps μ) =
          (f - algebraMap ℂ (Module.End ℂ (m → ℂ)) (μ : ℂ)).restrict hmaps' +
            algebraMap ℂ (Module.End ℂ (f.maxGenEigenspace μ)) (μ : ℂ) := by
        refine LinearMap.ext fun x => Subtype.ext ?_
        simp [LinearMap.restrict_apply]
      show LinearMap.toMatrix (b μ) (b μ) (f.restrict (hmaps μ)) = _
      rw [hsplit, map_add, LinearMap.toMatrix_algebraMap, Matrix.scalar_apply, add_comm]
  -- transport along the algebra equivalence `X ↦ toMatrix c c (toLin' X)`
  let φ : Matrix m m ℂ ≃ₐ[ℂ] Matrix (Σ μ : {μ // f.maxGenEigenspace μ ≠ ⊥}, κ μ) (Σ μ : {μ // f.maxGenEigenspace μ ≠ ⊥}, κ μ) ℂ :=
    Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv c)
  have hφ : ∀ X : Matrix m m ℂ, φ X = LinearMap.toMatrix c c (Matrix.toLin' X) := fun _ => rfl
  have hφc : Continuous φ := φ.toLinearMap.continuous_of_finiteDimensional
  have hφexp : φ (exp A) = exp (φ A) := NormedSpace.map_exp φ hφc A
  have hdet : (exp A).det = (φ (exp A)).det := by
    rw [hφ, LinearMap.det_toMatrix, LinearMap.det_toLin']
  have htr : A.trace = (φ A).trace := (Matrix.trace_map φ A).symm
  rw [hdet, hφexp, htr, hφ, hB, Matrix.exp_blockDiagonal', det_blockDiagonal',
    trace_blockDiagonal', NormedSpace.exp_sum]
  refine Finset.prod_congr rfl fun μ _ => ?_
  rw [Pi.coe_exp]
  obtain ⟨Nμ, hNμ, hdμ⟩ := hd μ
  rw [hdμ]
  exact det_exp_diagonal_add _ hNμ

/-- Jacobi's formula over `ℂ` with `Complex.exp` on the right-hand side. -/
theorem det_exp_complex' (A : Matrix m m ℂ) : (exp A).det = Complex.exp A.trace := by
  rw [Complex.exp_eq_exp_ℂ]
  exact det_exp_complex A

/-! ### The real case, by mapping `ℝ → ℂ` -/

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
/-- Jacobi's formula over `ℝ`: the determinant of the matrix exponential is the exponential of the
trace. Both `exp`s are `NormedSpace.exp`. -/
theorem det_exp_real (A : Matrix m m ℝ) : (exp A).det = exp A.trace := by
  apply Complex.ofReal_injective
  have hcont : Continuous Complex.ofRealHom.mapMatrix :=
    continuous_id.matrix_map (m := m) (n := m) Complex.continuous_ofReal
  have h1 : Complex.ofRealHom (exp A).det = (exp (Complex.ofRealHom.mapMatrix A)).det := by
    rw [RingHom.map_det, NormedSpace.map_exp _ hcont]
  have h2 : (Complex.ofRealHom.mapMatrix A).trace = Complex.ofRealHom A.trace :=
    (AddMonoidHom.map_trace Complex.ofRealHom A).symm
  have h3 : Complex.ofRealHom (exp A.trace) = exp (Complex.ofRealHom A.trace) :=
    NormedSpace.map_exp _ Complex.continuous_ofReal _
  show Complex.ofRealHom (exp A).det = Complex.ofRealHom (exp A.trace)
  rw [h1, det_exp_complex, h2, h3]

/-- Jacobi's formula over `ℝ` with `Real.exp` on the right-hand side. -/
theorem det_exp_real' (A : Matrix m m ℝ) : (exp A).det = Real.exp A.trace := by
  rw [Real.exp_eq_exp_ℝ]
  exact det_exp_real A

end DetExpEigen7

end
