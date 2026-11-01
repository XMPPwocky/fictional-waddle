import Mathlib

/-!
# Invertible linear maps on `n` bits are even permutations (for `n ≠ 2`)

Notation: `V n = Fin n → ZMod 2`.

## PROVED

* `LinearLayerSignB.transvection_mulVec`: `transvection i j c *ᵥ x = x + Function.update 0 i (c * x j)`.
* `LinearLayerSignB.sign_transvectionPerm`: for `n ≠ 2` and every `TransvectionStruct (Fin n) (ZMod 2)`,
  the permutation `x ↦ t.toMatrix *ᵥ x` of `V n` has sign `1`.
* `LinearLayerSignB.sign_toPermHom`: for `n ≠ 2` and every unit `U` of `Matrix (Fin n) (Fin n) (ZMod 2)`
  (an invertible matrix), the permutation `x ↦ U *ᵥ x` of `V n` has sign `1`.
* `LinearLayerSignB.sign_linearEquiv_eq_one`: for `n ≠ 2` and every `A : V n ≃ₗ[ZMod 2] V n`,
  `Equiv.Perm.sign A.toEquiv = 1`.
* `LinearLayerSignB.sign_linearEquiv_eq_one_of_three_le`: the same under `3 ≤ n` (the requested form).
* `LinearLayerSignB.sign_eq_one_of_apply_eq_mulVec`: for `n ≠ 2`, every matrix `M` over `ZMod 2` and every
  permutation `σ` of `V n` with `σ x = M *ᵥ x` for all `x`, `sign σ = 1` (no separate invertibility
  hypothesis: bijectivity of `σ` supplies it).
* `LinearLayerSignB.swap2_toEquiv`, `LinearLayerSignB.sign_swap2`: on `V 2`, the linear equivalence
  `x ↦ x ∘ swap 0 1` (swap the two coordinates) equals the transposition `![0,1] ↔ ![1,0]` and
  has sign `-1`.
* `LinearLayerSignB.all_linear_even_iff`: `(∀ A : V n ≃ₗ[ZMod 2] V n, sign A.toEquiv = 1) ↔ n ≠ 2`.
* `LinearLayerSignB.card_coord_zero`: `2 * #{x : V n | x j = 0} = 2 ^ n`.
* `LinearLayerSignB.sign_of_eq_prod`: for `n ≠ 2`, a unit whose matrix is a product of transvection
  matrices induces a permutation of sign `1`.
* Instances showing hypotheses satisfiable: `example`s at `n = 3`, and `sign_transvection_three`
  (the transvection `x ↦ x + x 1 • e 0` on 3 bits).

## CITED / INTERPRETED (not proved here)

* The decomposition of a square matrix over a field as
  (product of transvections) * diagonal * (product of transvections) is Mathlib's
  `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`; it is used, not re-proved.
* Reading: a block cipher's linear layer over GF(2) on `n ≥ 3` bits is an even permutation of the
  state space, so any odd permutation must come from a nonlinear component. This reading is an
  interpretation; only the statements above are proved.
* For `n = 0, 1` the result holds trivially (there are no transvections and `GL_n(F_2)` is trivial);
  `n = 2` is the unique exception, as `all_linear_even_iff` states.
-/

namespace LinearLayerSignB

open Matrix Equiv

/-- Bit vectors of length `n`. -/
abbrev V (n : ℕ) := Fin n → ZMod 2

/-- The permutation of `V n` induced by an invertible matrix acting by `mulVec`. -/
def toPerm {n : ℕ} (U : (Matrix (Fin n) (Fin n) (ZMod 2))ˣ) : Perm (V n) where
  toFun x := (U : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x
  invFun x := ((U⁻¹ : (Matrix (Fin n) (Fin n) (ZMod 2))ˣ) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x
  left_inv x := by simp [Matrix.mulVec_mulVec]
  right_inv x := by simp [Matrix.mulVec_mulVec]

/-- `toPerm` as a group homomorphism. -/
def toPermHom (n : ℕ) : (Matrix (Fin n) (Fin n) (ZMod 2))ˣ →* Perm (V n) where
  toFun := toPerm
  map_one' := by ext x i; simp [toPerm]
  map_mul' U W := by ext x i; simp [toPerm, Matrix.mulVec_mulVec]

theorem toPermHom_apply {n : ℕ} (U : (Matrix (Fin n) (Fin n) (ZMod 2))ˣ) (x : V n) :
    toPermHom n U x = (U : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x := rfl

theorem z2_add_self (a : ZMod 2) : a + a = 0 := by fin_cases a <;> rfl

theorem z2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem z2_eq_one_of_ne_zero (a : ZMod 2) (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

theorem transvection_mulVec {n : ℕ} (i j : Fin n) (c : ZMod 2) (x : V n) :
    transvection i j c *ᵥ x = x + Function.update (0 : V n) i (c * x j) := by
  simp [transvection, Matrix.add_mulVec, Matrix.single_mulVec]

/-- The unit of the matrix ring given by a transvection. -/
def tUnit {n : ℕ} (t : TransvectionStruct (Fin n) (ZMod 2)) : (Matrix (Fin n) (Fin n) (ZMod 2))ˣ :=
  ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩

/-- Number of bit vectors with a given coordinate equal to zero. -/
theorem card_coord_zero {n : ℕ} (j : Fin n) :
    2 * Fintype.card {x : V n // x j = 0} = 2 ^ n := by
  have hbij : Fintype.card {x : V n // x j = 0} = Fintype.card {x : V n // ¬ x j = 0} := by
    apply Fintype.card_congr
    refine
      { toFun := fun x => ⟨x.1 + Function.update (0 : V n) j 1, by simp [x.2]⟩
        invFun := fun x => ⟨x.1 + Function.update (0 : V n) j 1, by
          have := z2_eq_one_of_ne_zero _ x.2
          simp [this, z2_add_self]⟩
        left_inv := fun x => by
          ext i
          simp [add_assoc, z2_add_self]
        right_inv := fun x => by
          ext i
          simp [add_assoc, z2_add_self] }
  have hc := Fintype.card_subtype_compl (fun x : V n => x j = 0)
  have hle := Fintype.card_subtype_le (fun x : V n => x j = 0)
  have hV : Fintype.card (V n) = 2 ^ n := by simp
  omega

theorem sign_transvectionPerm {n : ℕ} (hn : n ≠ 2) (t : TransvectionStruct (Fin n) (ZMod 2)) :
    Perm.sign (toPermHom n (tUnit t)) = 1 := by
  obtain ⟨i, j, hij, c⟩ := t
  have hn3 : 3 ≤ n := by
    have h1 := i.2; have h2 := j.2
    have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    omega
  set σ := toPermHom n (tUnit ⟨i, j, hij, c⟩) with hσdef
  have hσ : ∀ x, σ x = x + Function.update (0 : V n) i (c * x j) := by
    intro x
    rw [hσdef, toPermHom_apply]
    exact transvection_mulVec i j c x
  rcases z2_cases c with rfl | rfl
  · have : σ = 1 := by
      ext x k
      simp [hσ]
    rw [this, map_one]
  · have hsq : σ ^ 2 = 1 := by
      ext x k
      rw [pow_two, Perm.mul_apply, hσ, hσ]
      have hj : (x + Function.update (0 : V n) i ((1 : ZMod 2) * x j)) j = x j := by
        simp [Function.update_of_ne (Ne.symm hij)]
      rw [hj]
      simp only [Pi.add_apply, add_assoc, z2_add_self, add_zero, Perm.one_apply]
    have hfix : Fintype.card (Function.fixedPoints σ) = Fintype.card {x : V n // x j = 0} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro x
      rw [Function.mem_fixedPoints, Function.IsFixedPt, hσ]
      constructor
      · intro h
        have := congrFun h i
        simpa using this
      · intro h
        simp [h]
    rw [Perm.sign_of_pow_two_eq_one hsq, hfix]
    have hc := card_coord_zero j
    have hV : Fintype.card (V n) = 2 ^ n := by simp
    rw [hV]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h8 : 2 ^ (m + 3) = 8 * 2 ^ m := by ring
    rw [h8] at hc ⊢
    have : (8 * 2 ^ m - Fintype.card {x : V (m + 3) // x j = 0}) / 2 = 2 * 2 ^ m := by omega
    rw [this, pow_mul]
    simp

theorem sign_of_eq_prod {n : ℕ} (hn : n ≠ 2) (L : List (TransvectionStruct (Fin n) (ZMod 2))) :
    ∀ U : (Matrix (Fin n) (Fin n) (ZMod 2))ˣ,
      (U : Matrix (Fin n) (Fin n) (ZMod 2)) = (L.map TransvectionStruct.toMatrix).prod →
      Perm.sign (toPermHom n U) = 1 := by
  induction L with
  | nil =>
    intro U hU
    have : U = 1 := Units.ext (by simpa using hU)
    simp [this]
  | cons t L ih =>
    intro U hU
    have hU' : (((tUnit t)⁻¹ * U : (Matrix (Fin n) (Fin n) (ZMod 2))ˣ) :
        Matrix (Fin n) (Fin n) (ZMod 2)) = (L.map TransvectionStruct.toMatrix).prod := by
      rw [Units.val_mul, hU, List.map_cons, List.prod_cons, ← Matrix.mul_assoc]
      change t.inv.toMatrix * t.toMatrix * _ = _
      rw [t.inv_mul, Matrix.one_mul]
    have hsplit : U = tUnit t * ((tUnit t)⁻¹ * U) := by group
    rw [hsplit, map_mul, Perm.sign_mul, sign_transvectionPerm hn, ih _ hU', one_mul]

/-- Every invertible matrix over `ZMod 2` of size `n ≠ 2` induces an even permutation. -/
theorem sign_toPermHom {n : ℕ} (hn : n ≠ 2) (U : (Matrix (Fin n) (Fin n) (ZMod 2))ˣ) :
    Perm.sign (toPermHom n U) = 1 := by
  obtain ⟨L, L', D, hM⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec
      (U : Matrix (Fin n) (Fin n) (ZMod 2))
  have hdet : (U : Matrix (Fin n) (Fin n) (ZMod 2)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp U.isUnit).ne_zero
  rw [hM, Matrix.det_mul, Matrix.det_mul, TransvectionStruct.det_toMatrix_prod,
    TransvectionStruct.det_toMatrix_prod, Matrix.det_diagonal, one_mul, mul_one] at hdet
  have hD : D = fun _ => 1 := by
    funext k
    exact z2_eq_one_of_ne_zero _ (Finset.prod_ne_zero_iff.mp hdet k (Finset.mem_univ k))
  have hprod : (U : Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((L ++ L').map TransvectionStruct.toMatrix).prod := by
    rw [hM, hD, Matrix.diagonal_one, Matrix.mul_one, List.map_append, List.prod_append]
  exact sign_of_eq_prod hn _ U hprod

/-- The unit of the matrix ring given by a linear automorphism. -/
def unitOfLinearEquiv {n : ℕ} (A : V n ≃ₗ[ZMod 2] V n) : (Matrix (Fin n) (Fin n) (ZMod 2))ˣ where
  val := LinearMap.toMatrix' (A : V n →ₗ[ZMod 2] V n)
  inv := LinearMap.toMatrix' (A.symm : V n →ₗ[ZMod 2] V n)
  val_inv := by rw [← LinearMap.toMatrix'_comp]; simp
  inv_val := by rw [← LinearMap.toMatrix'_comp]; simp

theorem toEquiv_eq_toPermHom {n : ℕ} (A : V n ≃ₗ[ZMod 2] V n) :
    A.toEquiv = toPermHom n (unitOfLinearEquiv A) := by
  ext x
  rw [toPermHom_apply]
  simp [unitOfLinearEquiv]

/-- Main theorem: for `n ≠ 2`, every invertible linear map on `n` bits is an even permutation. -/
theorem sign_linearEquiv_eq_one {n : ℕ} (hn : n ≠ 2) (A : V n ≃ₗ[ZMod 2] V n) :
    Perm.sign A.toEquiv = 1 := by
  rw [toEquiv_eq_toPermHom]
  exact sign_toPermHom hn _

/-- The requested form, with `3 ≤ n`. -/
theorem sign_linearEquiv_eq_one_of_three_le {n : ℕ} (hn : 3 ≤ n) (A : V n ≃ₗ[ZMod 2] V n) :
    Perm.sign A.toEquiv = 1 :=
  sign_linearEquiv_eq_one (by omega) A

/-- Matrix form: any permutation of `V n` that agrees with `x ↦ M *ᵥ x` is even, for `n ≠ 2`. -/
theorem sign_eq_one_of_apply_eq_mulVec {n : ℕ} (hn : n ≠ 2) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (σ : Perm (V n)) (hσ : ∀ x, σ x = M *ᵥ x) : Perm.sign σ = 1 := by
  have hbij : Function.Bijective (Matrix.toLin' M) := by
    have : ⇑(Matrix.toLin' M) = ⇑σ := by funext x; simp [hσ]
    rw [this]; exact σ.bijective
  have key := sign_linearEquiv_eq_one hn (LinearEquiv.ofBijective (Matrix.toLin' M) hbij)
  have heq : (LinearEquiv.ofBijective (Matrix.toLin' M) hbij).toEquiv = σ := by
    ext x; simp [hσ]
  rwa [heq] at key

/-- On 2 bits: swapping the two coordinates. -/
def swap2 : V 2 ≃ₗ[ZMod 2] V 2 := LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (Equiv.swap 0 1)

theorem swap2_toEquiv : swap2.toEquiv = Equiv.swap (![0, 1] : V 2) ![1, 0] := by
  apply Equiv.ext
  intro x
  funext k
  have hx : x = ![x 0, x 1] := by funext t; fin_cases t <;> rfl
  rw [hx]
  generalize x 0 = a
  generalize x 1 = b
  fin_cases a <;> fin_cases b <;> fin_cases k <;> decide

theorem sign_swap2 : Perm.sign swap2.toEquiv = -1 := by
  rw [swap2_toEquiv]
  exact Perm.sign_swap (by decide)

theorem all_linear_even_iff (n : ℕ) :
    (∀ A : V n ≃ₗ[ZMod 2] V n, Perm.sign A.toEquiv = 1) ↔ n ≠ 2 := by
  constructor
  · rintro h rfl
    have := h swap2
    rw [sign_swap2] at this
    exact absurd this (by decide)
  · intro hn A
    exact sign_linearEquiv_eq_one hn A

/-! Satisfiability of hypotheses. -/

example : (3 : ℕ) ≠ 2 := by decide
example : (3 : ℕ) ≤ 3 := le_refl 3

/-- A concrete nontrivial transvection on 3 bits is even. -/
theorem sign_transvection_three :
    Perm.sign (toPermHom 3 (tUnit ⟨0, 1, by decide, 1⟩)) = 1 :=
  sign_transvectionPerm (by decide) _

example : Perm.sign (LinearEquiv.refl (ZMod 2) (V 3)).toEquiv = 1 :=
  sign_linearEquiv_eq_one_of_three_le (le_refl 3) _

example : ∃ (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (σ : Perm (V 3)), ∀ x, σ x = M *ᵥ x :=
  ⟨1, 1, fun x => by simp⟩

example : ((1 : (Matrix (Fin 3) (Fin 3) (ZMod 2))ˣ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    (([] : List (TransvectionStruct (Fin 3) (ZMod 2))).map TransvectionStruct.toMatrix).prod := by
  simp

example : Perm.sign (toPermHom 3 1) = 1 := sign_of_eq_prod (by decide) [] 1 (by simp)

end LinearLayerSignB

#print axioms LinearLayerSignB.toPermHom_apply
#print axioms LinearLayerSignB.z2_add_self
#print axioms LinearLayerSignB.z2_cases
#print axioms LinearLayerSignB.z2_eq_one_of_ne_zero
#print axioms LinearLayerSignB.transvection_mulVec
#print axioms LinearLayerSignB.card_coord_zero
#print axioms LinearLayerSignB.sign_transvectionPerm
#print axioms LinearLayerSignB.sign_of_eq_prod
#print axioms LinearLayerSignB.sign_toPermHom
#print axioms LinearLayerSignB.toEquiv_eq_toPermHom
#print axioms LinearLayerSignB.sign_linearEquiv_eq_one
#print axioms LinearLayerSignB.sign_linearEquiv_eq_one_of_three_le
#print axioms LinearLayerSignB.sign_eq_one_of_apply_eq_mulVec
#print axioms LinearLayerSignB.swap2_toEquiv
#print axioms LinearLayerSignB.sign_swap2
#print axioms LinearLayerSignB.all_linear_even_iff
#print axioms LinearLayerSignB.sign_transvection_three
