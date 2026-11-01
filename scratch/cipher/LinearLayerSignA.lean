import Mathlib

/-!
# Invertible linear maps on `n ≠ 2` bits are even permutations

Setting: `V n = Fin n → ZMod 2`. For a linear equivalence `A : V n ≃ₗ[ZMod 2] V n`,
`A.toEquiv : Equiv.Perm (V n)` is the induced permutation of the `2^n` bit vectors.

## PROVED (exactly what the Lean statements say)

* `sign_linearEquiv_eq_one`: for every `n ≠ 2` and every `A : V n ≃ₗ[ZMod 2] V n`,
  `Equiv.Perm.sign A.toEquiv = 1`.
* `sign_linearEquiv_eq_one_of_three_le`: the same under the hypothesis `3 ≤ n`.
* `sign_unitPerm_eq_one`: for `3 ≤ n` and every unit `U` of `Matrix (Fin n) (Fin n) (ZMod 2)`,
  the permutation `x ↦ U *ᵥ x` of `V n` has sign `1`.
* `sign_eq_one_of_mulVec`: for `n ≠ 2`, a matrix `M` over `ZMod 2` with `M.det ≠ 0`, and any
  permutation `σ` of `V n` with `σ x = M *ᵥ x` for all `x`, `sign σ = 1`.
* `sign_tvPerm`: for `n ≠ 2`, `i ≠ j`, `c : ZMod 2`, the transvection
  `x ↦ x + Pi.single i (c * x j)` has sign `1`.
* `tv_commutator` / `tvPerm_eq_commutator`: for pairwise distinct `i, j, k`,
  `T_ij(c) = T_ik(c) * T_kj(1) * T_ik(c) * T_kj(1)` as permutations of `V n`
  (characteristic 2, each `T` is an involution).
* `transvection_mulVec`: `Matrix.transvection i j c *ᵥ x = x + Pi.single i (c * x j)`.
* `swap2_toEquiv`, `sign_swap2`: on `V 2`, the coordinate swap
  `LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (Equiv.swap 0 1)` equals the single transposition
  `Equiv.swap ![0, 1] ![1, 0]` and has sign `-1`.
* `all_even_iff`: `(∀ A : V n ≃ₗ[ZMod 2] V n, sign A.toEquiv = 1) ↔ n ≠ 2`.

Proof route: Mathlib's `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`
writes the matrix of `A` as (transvections) * diagonal * (transvections); over `ZMod 2` a
diagonal matrix with nonzero determinant is `1`; for `n ≥ 3` every transvection is a product
`a * b * a * b` of permutations, whose sign is `sign a ^ 2 * sign b ^ 2 = 1`; for `n ≤ 1` there
are no transvections. Sign is multiplicative.

## CITED / INTERPRETED (not proved here)

* Reading: an invertible linear layer of a bit-level cipher on `n ≥ 3` bits, viewed as a
  permutation of the `2^n` states, is always even, so composing such layers can never produce
  an odd permutation; any odd permutation must come from a nonlinear component.
* Known background (not used in the proof): `GL(n, 2)` is perfect for `n ≥ 3`, which gives the
  same conclusion abstractly; a transvection with `c = 1` moves `2^(n-1)` points in `2^(n-2)`
  disjoint transpositions.
-/

namespace LinearLayerSignA

open Matrix Matrix.Pivot Equiv

/-- Bit vectors of length `n`. -/
abbrev V (n : ℕ) := Fin n → ZMod 2

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma zmod2_eq_one_of_ne_zero (a : ZMod 2) (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

/-- The elementary transvection `x ↦ x + (c * x j) • e_i`. -/
def tv {n : ℕ} (i j : Fin n) (c : ZMod 2) (x : V n) : V n := x + Pi.single i (c * x j)

lemma tv_tv {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : ZMod 2) (x : V n) :
    tv i j c (tv i j c x) = x := by
  have hj : (tv i j c x) j = x j := by
    simp [tv, Ne.symm hij]
  rw [tv, hj, tv, add_assoc, ← Pi.single_add, zmod2_add_self, Pi.single_zero, add_zero]

/-- The transvection as a permutation of `V n` (it is an involution). -/
def tvPerm {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : ZMod 2) : Perm (V n) where
  toFun := tv i j c
  invFun := tv i j c
  left_inv := tv_tv hij c
  right_inv := tv_tv hij c

@[simp] lemma tvPerm_apply {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : ZMod 2) (x : V n) :
    tvPerm i j hij c x = tv i j c x := rfl

/-- The transvection matrix acts on vectors by `tv`. -/
lemma transvection_mulVec {n : ℕ} (i j : Fin n) (c : ZMod 2) (x : V n) :
    transvection i j c *ᵥ x = tv i j c x := by
  rw [transvection, add_mulVec, one_mulVec, single_mulVec, tv]
  rfl

/-- Commutator identity in characteristic 2: for distinct `i, j, k`,
`T_ij(c) = T_ik(c) T_kj(1) T_ik(c) T_kj(1)`. -/
lemma tv_commutator {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (c : ZMod 2) (x : V n) :
    tv i j c x = tv i k c (tv k j 1 (tv i k c (tv k j 1 x))) := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  funext l
  by_cases hli : l = i
  · subst hli
    simp [tv, hki, Ne.symm hij, Ne.symm hki, Ne.symm hkj]
    linear_combination (-(c * x j) - c * x k) * h2
  · by_cases hlk : l = k
    · subst hlk
      simp [tv, hki, Ne.symm hij, Ne.symm hkj]
      linear_combination (-(x j)) * h2
    · simp [tv, hli, hlk, Ne.symm hij, Ne.symm hkj]

lemma tvPerm_eq_commutator {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (c : ZMod 2) :
    tvPerm i j hij c =
      tvPerm i k (Ne.symm hki) c * tvPerm k j hkj 1 * tvPerm i k (Ne.symm hki) c *
        tvPerm k j hkj 1 := by
  ext x : 1
  simp only [Perm.mul_apply, tvPerm_apply]
  exact tv_commutator hij hki hkj c x

/-- For `n ≠ 2`, every transvection of `V n` is an even permutation. For `n ≥ 3` it is a
commutator of two permutations; for `n ≤ 1` there are no pairs `i ≠ j`. -/
theorem sign_tvPerm {n : ℕ} (hn : n ≠ 2) (i j : Fin n) (hij : i ≠ j) (c : ZMod 2) :
    Perm.sign (tvPerm i j hij c) = 1 := by
  rcases Nat.lt_or_ge n 3 with h | h
  · exfalso
    have : n ≤ 1 := by omega
    have hsub : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr this
    exact hij (Subsingleton.elim i j)
  · have hcard : (({i, j} : Finset (Fin n))).card < (Finset.univ : Finset (Fin n)).card := by
      calc (({i, j} : Finset (Fin n))).card ≤ 2 := Finset.card_le_two
        _ < n := by omega
        _ = _ := by simp
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [tvPerm_eq_commutator hij hk.1 hk.2 c]
    simp only [Perm.sign_mul]
    set a := Perm.sign (tvPerm i k (Ne.symm hk.1) c)
    set b := Perm.sign (tvPerm k j hk.2 1)
    calc a * b * a * b = (a * a) * (b * b) := by
          rw [mul_assoc a b a, mul_comm b a, ← mul_assoc, mul_assoc]
      _ = 1 := by rw [Int.units_mul_self, Int.units_mul_self, one_mul]

/-- The permutation induced by a Mathlib `TransvectionStruct`. -/
def tsPerm {n : ℕ} (t : TransvectionStruct (Fin n) (ZMod 2)) : Perm (V n) :=
  tvPerm t.i t.j t.hij t.c

lemma tsPerm_apply {n : ℕ} (t : TransvectionStruct (Fin n) (ZMod 2)) (x : V n) :
    tsPerm t x = t.toMatrix *ᵥ x := by
  rw [TransvectionStruct.toMatrix, transvection_mulVec]
  rfl

lemma listProd_apply {n : ℕ} (L : List (TransvectionStruct (Fin n) (ZMod 2))) (x : V n) :
    (L.map tsPerm).prod x = (L.map TransvectionStruct.toMatrix).prod *ᵥ x := by
  induction L generalizing x with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.prod_cons, Perm.mul_apply, ih, tsPerm_apply, mulVec_mulVec]

lemma sign_listProd {n : ℕ} (hn : n ≠ 2) (L : List (TransvectionStruct (Fin n) (ZMod 2))) :
    Perm.sign (L.map tsPerm).prod = 1 := by
  induction L with
  | nil => simp
  | cons t L ih =>
    rw [List.map_cons, List.prod_cons, Perm.sign_mul, ih, mul_one]
    exact sign_tvPerm hn _ _ _ _

/-- Core statement (matrix form): if `n ≠ 2`, `M` is a square matrix over `ZMod 2` with nonzero
determinant, and `σ` is a permutation of `V n` with `σ x = M *ᵥ x` for all `x`, then
`sign σ = 1`. -/
theorem sign_eq_one_of_mulVec {n : ℕ} (hn : n ≠ 2) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hM : M.det ≠ 0) (σ : Perm (V n)) (hσ : ∀ x, σ x = M *ᵥ x) : Perm.sign σ = 1 := by
  obtain ⟨L, L', D, hLD⟩ := exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hdet : M.det = ∏ i, D i := by
    rw [hLD, det_mul, det_mul, TransvectionStruct.det_toMatrix_prod,
      TransvectionStruct.det_toMatrix_prod, det_diagonal, one_mul, mul_one]
  have hD : D = fun _ => 1 := by
    funext i
    apply zmod2_eq_one_of_ne_zero
    rw [hdet] at hM
    exact (Finset.prod_ne_zero_iff.mp hM) i (Finset.mem_univ i)
  have hM' : M = (L.map TransvectionStruct.toMatrix).prod *
      (L'.map TransvectionStruct.toMatrix).prod := by
    rw [hLD, hD, diagonal_one, Matrix.mul_one]
  have hσ' : σ = (L.map tsPerm).prod * (L'.map tsPerm).prod := by
    ext x : 1
    rw [hσ, Perm.mul_apply, listProd_apply, listProd_apply, mulVec_mulVec, hM']
  rw [hσ', Perm.sign_mul, sign_listProd hn, sign_listProd hn, mul_one]

/-- Main theorem (linear-equivalence form): for `n ≠ 2` (in particular every `n ≥ 3`), every
invertible `ZMod 2`-linear map of `Fin n → ZMod 2` induces an even permutation. -/
theorem sign_linearEquiv_eq_one {n : ℕ} (hn : n ≠ 2) (A : V n ≃ₗ[ZMod 2] V n) :
    Perm.sign A.toEquiv = 1 := by
  set M := LinearMap.toMatrix' (A : V n →ₗ[ZMod 2] V n)
  have hinv : LinearMap.toMatrix' (A.symm : V n →ₗ[ZMod 2] V n) * M = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (A.symm : V n →ₗ[ZMod 2] V n) ∘ₗ (A : V n →ₗ[ZMod 2] V n) = LinearMap.id := by
      ext x : 1
      simp
    rw [this, LinearMap.toMatrix'_id]
  have hM : M.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hinv
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  exact sign_eq_one_of_mulVec hn M hM A.toEquiv
    (fun x => (LinearMap.toMatrix'_mulVec (A : V n →ₗ[ZMod 2] V n) x).symm)

/-- The requested form: `n ≥ 3`. -/
theorem sign_linearEquiv_eq_one_of_three_le {n : ℕ} (hn : 3 ≤ n) (A : V n ≃ₗ[ZMod 2] V n) :
    Perm.sign A.toEquiv = 1 :=
  sign_linearEquiv_eq_one (by omega) A

/-- The permutation of `V n` induced by an invertible matrix acting by `mulVec`. -/
def unitPerm {n : ℕ} (U : (Matrix (Fin n) (Fin n) (ZMod 2))ˣ) : Perm (V n) where
  toFun x := U.val *ᵥ x
  invFun x := U.inv *ᵥ x
  left_inv x := by simp [mulVec_mulVec]
  right_inv x := by simp [mulVec_mulVec]

/-- Matrix form: for `n ≥ 3`, every invertible matrix over `ZMod 2` acting by `mulVec`
induces an even permutation of `Fin n → ZMod 2`. -/
theorem sign_unitPerm_eq_one {n : ℕ} (hn : 3 ≤ n) (U : (Matrix (Fin n) (Fin n) (ZMod 2))ˣ) :
    Perm.sign (unitPerm U) = 1 := by
  have hM : U.val.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det U.val_inv
    rw [det_mul, h, zero_mul, det_one] at this
    exact zero_ne_one this
  exact sign_eq_one_of_mulVec (by omega) U.val hM (unitPerm U) (fun _ => rfl)

/-! ### The case `n = 2` -/

/-- Swapping the two coordinates of a 2-bit vector. -/
def swap2 : V 2 ≃ₗ[ZMod 2] V 2 := LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (Equiv.swap 0 1)

lemma swap2_toEquiv : swap2.toEquiv = Equiv.swap ![0, 1] ![1, 0] := by
  ext x : 1
  revert x
  decide

/-- On 2 bits the coordinate swap is the single transposition `01 ↔ 10`, so it is odd. -/
theorem sign_swap2 : Perm.sign swap2.toEquiv = -1 := by
  rw [swap2_toEquiv, Perm.sign_swap]
  decide

/-- Exact characterization: all invertible linear maps on `n` bits are even iff `n ≠ 2`. -/
theorem all_even_iff (n : ℕ) :
    (∀ A : V n ≃ₗ[ZMod 2] V n, Perm.sign A.toEquiv = 1) ↔ n ≠ 2 := by
  constructor
  · rintro h rfl
    have := h swap2
    rw [sign_swap2] at this
    exact absurd this (by decide)
  · exact fun hn A => sign_linearEquiv_eq_one hn A

/-! ### Explicit instances for the hypotheses -/

example : 3 ≤ 3 ∧ Perm.sign (LinearEquiv.refl (ZMod 2) (V 3)).toEquiv = 1 :=
  ⟨le_rfl, sign_linearEquiv_eq_one_of_three_le le_rfl _⟩

/-- A non-identity instance: the coordinate permutation `0 → 1 → 2 → 0` on 3 bits. -/
example : Perm.sign (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
    (finRotate 3)).toEquiv = 1 :=
  sign_linearEquiv_eq_one_of_three_le le_rfl _

example : (3 : ℕ) ≠ 2 ∧ (Matrix.det (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 0) ∧
    ∀ x : V 3, (1 : Perm (V 3)) x = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x :=
  ⟨by decide, by simp, fun x => by simp⟩

example : Perm.sign (unitPerm (1 : (Matrix (Fin 3) (Fin 3) (ZMod 2))ˣ)) = 1 :=
  sign_unitPerm_eq_one le_rfl 1

example : Perm.sign (tvPerm (0 : Fin 3) 1 (by decide) 1) = 1 :=
  sign_tvPerm (by decide) _ _ _ _

/-- Distinct indices `i = 0, j = 1, k = 2` in `Fin 3` satisfy the hypotheses of `tv_commutator`
and `tvPerm_eq_commutator` (and `0 ≠ 1` those of `tv_tv`). -/
example : (0 : Fin 3) ≠ 1 ∧ (2 : Fin 3) ≠ 0 ∧ (2 : Fin 3) ≠ 1 ∧
    tvPerm (0 : Fin 3) 1 (by decide) 1 =
      tvPerm 0 2 (by decide) 1 * tvPerm 2 1 (by decide) 1 * tvPerm 0 2 (by decide) 1 *
        tvPerm 2 1 (by decide) 1 :=
  ⟨by decide, by decide, by decide, tvPerm_eq_commutator (by decide) (by decide) (by decide) 1⟩

end LinearLayerSignA

#print axioms LinearLayerSignA.zmod2_add_self
#print axioms LinearLayerSignA.zmod2_eq_one_of_ne_zero
#print axioms LinearLayerSignA.tvPerm_apply
#print axioms LinearLayerSignA.tv_tv
#print axioms LinearLayerSignA.transvection_mulVec
#print axioms LinearLayerSignA.tv_commutator
#print axioms LinearLayerSignA.tvPerm_eq_commutator
#print axioms LinearLayerSignA.sign_tvPerm
#print axioms LinearLayerSignA.tsPerm_apply
#print axioms LinearLayerSignA.listProd_apply
#print axioms LinearLayerSignA.sign_listProd
#print axioms LinearLayerSignA.sign_eq_one_of_mulVec
#print axioms LinearLayerSignA.sign_linearEquiv_eq_one
#print axioms LinearLayerSignA.sign_linearEquiv_eq_one_of_three_le
#print axioms LinearLayerSignA.sign_unitPerm_eq_one
#print axioms LinearLayerSignA.swap2_toEquiv
#print axioms LinearLayerSignA.sign_swap2
#print axioms LinearLayerSignA.all_even_iff
