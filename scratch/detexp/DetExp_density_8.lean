import Mathlib

/-!
# `det (exp A) = exp (trace A)` by a density argument

For every square matrix `A` over `ℂ` or over `ℝ`, indexed by a finite type with decidable
equality, `(NormedSpace.exp A).det = NormedSpace.exp A.trace`.

Route (complex case):
1. If `A.charpoly` is separable, it has `Fintype.card m` distinct roots; the corresponding
   eigenvectors are linearly independent, so `A = P * diagonal λ * P⁻¹` with `P` invertible, and
   the identity follows from `Matrix.exp_conj`, `Matrix.exp_diagonal` and `NormedSpace.exp_sum`.
2. Separability of `M.charpoly` is equivalent to the nonvanishing of the resultant of
   `M.charpoly` and its derivative (sizes `n`, `n - 1`, `n = Fintype.card m`).
3. For fixed `A` and `E = diagonal (0, 1, …, n - 1)`, this resultant evaluated at
   `A + t • (E - A)` is a polynomial `Q` in `t`, with `Q(1) ≠ 0`. Hence `Q` has finitely many
   roots, and the set of `t` with `A + t • (E - A)` separable is dense in `ℂ`.
4. Both sides are continuous in `t`, agree on that dense set, hence agree at `t = 0`.

The real case follows by mapping entries along `Complex.ofRealHom` (`NormedSpace.map_exp`).
-/

open NormedSpace Matrix Polynomial

noncomputable section

namespace DetExpDensity8

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ### Diagonal and diagonalizable matrices -/

theorem det_exp_diagonal (d : m → ℂ) : (exp (diagonal d)).det = exp (diagonal d).trace := by
  rw [exp_diagonal, det_diagonal, trace_diagonal, exp_sum]
  exact Finset.prod_congr rfl fun i _ => Pi.coe_exp d i

theorem det_exp_conj (P D : Matrix m m ℂ) (hP : IsUnit P) :
    (exp (P * D * P⁻¹)).det = (exp D).det := by
  rw [Matrix.exp_conj P D hP, det_conj hP]

/-- If the characteristic polynomial of `A` is separable, then `det (exp A) = exp (trace A)`. -/
theorem det_exp_of_separable (A : Matrix m m ℂ) (hA : A.charpoly.Separable) :
    (exp A).det = exp A.trace := by
  have hne : A.charpoly ≠ 0 := A.charpoly_monic.ne_zero
  have hnd : A.charpoly.roots.Nodup := nodup_roots hA
  have hcard : A.charpoly.roots.toFinset.card = Fintype.card m := by
    rw [Multiset.toFinset_card_of_nodup hnd,
      splits_iff_card_roots.mp (IsAlgClosed.splits _), charpoly_natDegree_eq_dim]
  let e : m ≃ A.charpoly.roots.toFinset :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, hcard])
  let μ : m → ℂ := fun i => (e i : ℂ)
  have hμ : Function.Injective μ := fun i j h => e.injective (Subtype.ext h)
  have hev : ∀ i, Module.End.HasEigenvalue A.toLin' (μ i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, spectrum_toLin',
      mem_spectrum_iff_isRoot_charpoly, ← mem_roots hne, ← Multiset.mem_toFinset]
    exact (e i).2
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' A.toLin' μ hμ v hv
  let P : Matrix m m ℂ := Matrix.of fun j i => v i j
  have hP : IsUnit P := linearIndependent_col_iff_isUnit.mp hli
  have hAP : A * P = P * diagonal μ := by
    ext j i
    have h := congrFun ((hv i).apply_eq_smul) j
    rw [toLin'_apply] at h
    rw [mul_diagonal, mul_comm]
    simpa [P, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  have hconj : A = P * diagonal μ * P⁻¹ := by
    rw [← hAP, Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det P).mp hP),
      Matrix.mul_one]
  rw [hconj, det_exp_conj P _ hP, trace_conj hP, det_exp_diagonal]

/-! ### Separability as nonvanishing of a resultant -/

/-- The resultant of `M.charpoly` and its derivative, with sizes `n` and `n - 1`. -/
def charRes {R : Type*} [CommRing R] (M : Matrix m m R) : R :=
  resultant M.charpoly (derivative M.charpoly) (Fintype.card m) (Fintype.card m - 1)

theorem charRes_ne_zero_iff (M : Matrix m m ℂ) : charRes M ≠ 0 ↔ M.charpoly.Separable := by
  have h1 : M.charpoly.natDegree = Fintype.card m := charpoly_natDegree_eq_dim M
  have hne : M.charpoly ≠ 0 := M.charpoly_monic.ne_zero
  rw [charRes, ← h1, ← natDegree_derivative, Ne, resultant_eq_zero_iff, Separable]
  simp [hne]

theorem charRes_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix m m R) :
    charRes (M.map f) = f (charRes M) := by
  rw [charRes, charRes, charpoly_map, derivative_map, resultant_map_map]

/-! ### Density -/

/-- A matrix with distinct diagonal entries `0, 1, …, n - 1`. -/
def distinctDiag : Matrix m m ℂ :=
  diagonal fun i => ((Fintype.equivFin m i : ℕ) : ℂ)

theorem charRes_distinctDiag_ne_zero : charRes (distinctDiag : Matrix m m ℂ) ≠ 0 := by
  rw [charRes_ne_zero_iff, distinctDiag, charpoly_diagonal, separable_prod_X_sub_C_iff]
  intro i j h
  exact (Fintype.equivFin m).injective (Fin.ext (Nat.cast_injective h))

/-- The matrix `A + X • (E - A)` with polynomial entries. -/
def lineMat (A E : Matrix m m ℂ) : Matrix m m ℂ[X] :=
  A.map C + (X : ℂ[X]) • (E - A).map C

omit [Fintype m] [DecidableEq m] in
theorem lineMat_map_eval (A E : Matrix m m ℂ) (t : ℂ) :
    (lineMat A E).map (evalRingHom t) = A + t • (E - A) := by
  ext i j
  simp [lineMat]

theorem eval_charRes_lineMat (A E : Matrix m m ℂ) (t : ℂ) :
    (charRes (lineMat A E)).eval t = charRes (A + t • (E - A)) := by
  rw [← lineMat_map_eval, charRes_map, coe_evalRingHom]

/-- For every `A`, the set of `t` with `A + t • (E - A)` having separable characteristic
polynomial is dense, where `E = distinctDiag`. -/
theorem dense_separable_line (A : Matrix m m ℂ) :
    Dense {t : ℂ | (A + t • (distinctDiag - A)).charpoly.Separable} := by
  set Q := charRes (lineMat A distinctDiag) with hQ
  have hQ1 : Q.eval 1 ≠ 0 := by
    rw [hQ, eval_charRes_lineMat, one_smul, add_sub_cancel]
    exact charRes_distinctDiag_ne_zero
  have hQ0 : Q ≠ 0 := fun h => hQ1 (by rw [h, eval_zero])
  have hfin : {t : ℂ | Q.IsRoot t}.Countable := (finite_setOfPred_isRoot hQ0).countable
  have hd := hfin.dense_compl ℂ
  convert hd using 1
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, IsRoot.def, hQ, eval_charRes_lineMat,
    ← charRes_ne_zero_iff]

/-! ### Main theorems -/

section
open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false in
theorem continuous_exp_matrix {𝕂 : Type*} [RCLike 𝕂] :
    Continuous (fun M : Matrix m m 𝕂 => exp M) :=
  exp_continuous

end

/-- Jacobi's formula over `ℂ`: `det (exp A) = exp (trace A)`. -/
theorem det_exp_complex (A : Matrix m m ℂ) : (exp A).det = exp A.trace := by
  let L : ℂ → Matrix m m ℂ := fun t => A + t • (distinctDiag - A)
  have hL : Continuous L := continuous_const.add (continuous_id.smul continuous_const)
  have hf : Continuous fun t => (exp (L t)).det :=
    (continuous_exp_matrix.comp hL).matrix_det
  have hg : Continuous fun t => exp (L t).trace := by
    rw [← Complex.exp_eq_exp_ℂ]
    exact Complex.continuous_exp.comp hL.matrix_trace
  have heq := Continuous.ext_on (dense_separable_line A) hf hg
    (fun t ht => det_exp_of_separable (L t) ht)
  simpa [L] using congrFun heq 0

/-- Jacobi's formula over `ℝ`: `det (exp A) = exp (trace A)`. -/
theorem det_exp_real (A : Matrix m m ℝ) : (exp A).det = exp A.trace := by
  apply Complex.ofReal_injective
  have hc : Continuous (Complex.ofRealHom.mapMatrix : Matrix m m ℝ → Matrix m m ℂ) :=
    continuous_id.matrix_map Complex.continuous_ofReal
  have hmap : Complex.ofRealHom.mapMatrix (exp A) = exp (Complex.ofRealHom.mapMatrix A) := by
    open scoped Matrix.Norms.Operator in
    exact map_exp _ hc A
  have htr : ((A.trace : ℝ) : ℂ) = (Complex.ofRealHom.mapMatrix A).trace :=
    AddMonoidHom.map_trace Complex.ofRealHom A
  calc (((exp A).det : ℝ) : ℂ) = Complex.ofRealHom (exp A).det := rfl
    _ = (Complex.ofRealHom.mapMatrix (exp A)).det := RingHom.map_det _ _
    _ = exp (Complex.ofRealHom.mapMatrix A).trace := by rw [hmap, det_exp_complex]
    _ = ((exp A.trace : ℝ) : ℂ) := by
      rw [← htr, ← Real.exp_eq_exp_ℝ, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

/-- `det (exp A) = Complex.exp (trace A)`. -/
theorem det_exp_complex' (A : Matrix m m ℂ) : (exp A).det = Complex.exp A.trace := by
  rw [Complex.exp_eq_exp_ℂ, det_exp_complex]

/-- `det (exp A) = Real.exp (trace A)`. -/
theorem det_exp_real' (A : Matrix m m ℝ) : (exp A).det = Real.exp A.trace := by
  rw [Real.exp_eq_exp_ℝ, det_exp_real]

end DetExpDensity8
