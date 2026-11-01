import Mathlib

/-!
# A13 — Jacobi inverse problem: boundary moments determine the chain

## What is proved (all sorry-free)

* `jac2_inverse`, `jacobi2_inverse` (n = 2): a real `2 × 2` symmetric matrix with
  positive off-diagonal is determined by `(J^k)₀₀`, `k = 1, 2, 3`.
  Explicit moments: `m₁ = a`, `m₂ = a² + b²`, `m₃ = a³ + 2ab² + b²c`.
* `jac3_inverse`, `jacobi3_inverse` (n = 3): a real `3 × 3` Jacobi matrix (symmetric,
  tridiagonal, positive super-diagonal) is determined by `(J^k)₀₀`, `k = 1, …, 5`.
  `jac3_inverse` is by explicit moment polynomials (peeling `a₁, b₁, a₂, b₂, a₃` in
  turn); `jacobi3_inverse` is derived from the general theorem.
* `jacobi_inverse` (general size `n + 1`, moments `k ≤ 2n + 1`): the same statement for
  every size, via the Krylov matrix and Cholesky uniqueness (`cholesky_unique`).
* Sharpness: `jac2_two_moments_insufficient` (moments `k ≤ 2` do not suffice for
  `2 × 2`), `jac3_four_moments_insufficient` (moments `k ≤ 4` do not suffice for
  `3 × 3`), `jac2_sign_ambiguity` (the sign of the off-diagonal is invisible to all
  moments, so the positivity hypothesis is needed for uniqueness).
* Added in adversarial review: `isJacobi_jac3` (the `IsJacobi` hypothesis is satisfiable:
  `jac3` with positive off-diagonals is Jacobi), `jac3_free_moments` and
  `jacobi3_eq_free_chain` (concrete instance: a `3 × 3` Jacobi matrix with moments
  `0, 1, 0, 2, 0` is the free chain `jac3 0 0 0 1 1`), and the generalisation
  `lanczos_intertwiner_trivial`: if `U` is orthogonal, `U e₀ = e₀` and `U J' = J U` for
  Jacobi `J, J'` (any size), then `U = 1` and `J = J'`.

## Interpretation (not formalised)

This is the finite-dimensional uniqueness half of the discrete Gelfand–Levitan /
inverse spectral problem for Jacobi matrices, equivalently uniqueness of the Lanczos
recursion: the "boundary response" `m_k = ⟨e₀, J^k e₀⟩` (the moments of the spectral
measure of `e₀`, i.e. the Weyl function seen from site 0) determines the "bulk"
operator `J` on the whole chain. Existence / reconstruction (that every admissible
moment sequence comes from some Jacobi matrix) and stability are NOT proved here.
-/

open Matrix

namespace A13

/-- A Jacobi matrix (as a predicate on a real square matrix indexed by `Fin m`):
symmetric, tridiagonal, strictly positive super-diagonal. -/
def IsJacobi {m : ℕ} (J : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  J.IsSymm ∧ (∀ i j : Fin m, (i : ℕ) + 1 < j → J i j = 0) ∧
    (∀ i j : Fin m, (j : ℕ) = i + 1 → 0 < J i j)

/-- Explicit `2 × 2` Jacobi matrix `[[a, b], [b, c]]`. -/
def jac2 (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, c]

/-- Explicit `3 × 3` Jacobi matrix with diagonal `a₁ a₂ a₃` and off-diagonal `b₁ b₂`. -/
def jac3 (a₁ a₂ a₃ b₁ b₂ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a₁, b₁, 0; b₁, a₂, b₂; 0, b₂, a₃]

/-! ## n = 2 -/

theorem jac2_moment_one (a b c : ℝ) : ((jac2 a b c) ^ 1) 0 0 = a := by
  simp [jac2]
theorem jac2_moment_two (a b c : ℝ) : ((jac2 a b c) ^ 2) 0 0 = a ^ 2 + b ^ 2 := by
  simp [jac2, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
theorem jac2_moment_three (a b c : ℝ) :
    ((jac2 a b c) ^ 3) 0 0 = a ^ 3 + 2 * a * b ^ 2 + b ^ 2 * c := by
  simp [jac2, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]; ring

/-- n = 2, explicit parameters: moments 1..3 determine `(a, b, c)` when `b, b' > 0`. -/
theorem jac2_inverse (a b c a' b' c' : ℝ) (hb : 0 < b) (hb' : 0 < b')
    (h1 : ((jac2 a b c) ^ 1) 0 0 = ((jac2 a' b' c') ^ 1) 0 0)
    (h2 : ((jac2 a b c) ^ 2) 0 0 = ((jac2 a' b' c') ^ 2) 0 0)
    (h3 : ((jac2 a b c) ^ 3) 0 0 = ((jac2 a' b' c') ^ 3) 0 0) :
    jac2 a b c = jac2 a' b' c' := by
  rw [jac2_moment_one, jac2_moment_one] at h1
  rw [jac2_moment_two, jac2_moment_two] at h2
  rw [jac2_moment_three, jac2_moment_three] at h3
  subst h1
  have hbb : b = b' := by
    have : b ^ 2 = b' ^ 2 := by linarith
    exact (pow_left_inj₀ hb.le hb'.le two_ne_zero).mp this
  subst hbb
  have hc : b ^ 2 * (c - c') = 0 := by linear_combination h3
  have hc' : c = c' := by
    rcases mul_eq_zero.mp hc with h | h
    · exact absurd h (by positivity)
    · linarith
  rw [hc']

/-- n = 2, matrix form: any symmetric `2 × 2` real matrix with positive off-diagonal. -/
theorem jacobi2_inverse (J J' : Matrix (Fin 2) (Fin 2) ℝ)
    (hJ : J.IsSymm) (hJ' : J'.IsSymm) (hb : 0 < J 0 1) (hb' : 0 < J' 0 1)
    (h : ∀ k ∈ ({1, 2, 3} : Finset ℕ), (J ^ k) 0 0 = (J' ^ k) 0 0) :
    J = J' := by
  have e : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, M.IsSymm → M = jac2 (M 0 0) (M 0 1) (M 1 1) := by
    intro M hM
    have h10 : M 1 0 = M 0 1 := by
      have := congrFun (congrFun hM 0) 1
      simpa [Matrix.transpose_apply] using this
    ext i j; fin_cases i <;> fin_cases j <;> simp [jac2, h10]
  rw [e J hJ, e J' hJ'] at h ⊢
  exact jac2_inverse _ _ _ _ _ _ hb hb' (h 1 (by simp)) (h 2 (by simp)) (h 3 (by simp))

/-- Sharpness (moment count): moments `k = 0, 1, 2` do not determine a `2 × 2` Jacobi matrix. -/
theorem jac2_two_moments_insufficient :
    ∃ c c' : ℝ, c ≠ c' ∧ ∀ k ≤ 2, ((jac2 0 1 c) ^ k) 0 0 = ((jac2 0 1 c') ^ k) 0 0 := by
  refine ⟨0, 1, by norm_num, ?_⟩
  intro k hk
  interval_cases k
  · simp
  · simp [jac2]
  · rw [jac2_moment_two, jac2_moment_two]

/-- Sharpness (sign): without positivity, `b` and `-b` give identical moments of every
order (conjugation by `diag(1, -1)`). -/
theorem jac2_sign_ambiguity (a b c : ℝ) (k : ℕ) :
    ((jac2 a b c) ^ k) 0 0 = ((jac2 a (-b) c) ^ k) 0 0 := by
  set D : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1] with hD
  have hDD : D * D = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hD, Matrix.mul_apply, Fin.sum_univ_two]
  have hconj : jac2 a (-b) c = D * jac2 a b c * D := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hD, jac2, Matrix.mul_apply, Fin.sum_univ_two]
  have hpow : ∀ m : ℕ, (D * jac2 a b c * D) ^ m = D * (jac2 a b c) ^ m * D := by
    intro m
    induction m with
    | zero => simp [hDD]
    | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      calc D * jac2 a b c ^ m * D * (D * jac2 a b c * D)
          = D * jac2 a b c ^ m * (D * D) * jac2 a b c * D := by simp only [Matrix.mul_assoc]
        _ = D * (jac2 a b c ^ m * jac2 a b c) * D := by rw [hDD]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hconj, hpow]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hD]
  simp

/-! ## n = 3 -/

/-- n = 3, explicit parameters: moments 1..5 determine `(a₁, a₂, a₃, b₁, b₂)`. -/
theorem jac3_inverse (a₁ a₂ a₃ b₁ b₂ a₁' a₂' a₃' b₁' b₂' : ℝ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₁' : 0 < b₁') (hb₂' : 0 < b₂')
    (h : ∀ k ∈ Finset.Icc 1 5,
      ((jac3 a₁ a₂ a₃ b₁ b₂) ^ k) 0 0 = ((jac3 a₁' a₂' a₃' b₁' b₂') ^ k) 0 0) :
    jac3 a₁ a₂ a₃ b₁ b₂ = jac3 a₁' a₂' a₃' b₁' b₂' := by
  have h1 := h 1 (by simp)
  have h2 := h 2 (by simp)
  have h3 := h 3 (by simp)
  have h4 := h 4 (by simp)
  have h5 := h 5 (by simp)
  simp [jac3, pow_succ, Matrix.mul_apply, Fin.sum_univ_three] at h1 h2 h3 h4 h5
  subst h1
  have e1 : b₁ = b₁' := by
    have : b₁ ^ 2 = b₁' ^ 2 := by linear_combination h2
    exact (pow_left_inj₀ hb₁.le hb₁'.le two_ne_zero).mp this
  subst e1
  have e2 : a₂ = a₂' := by
    have : b₁ ^ 2 * (a₂ - a₂') = 0 := by linear_combination h3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by positivity)
    · linarith
  subst e2
  have e3 : b₂ = b₂' := by
    have : b₁ ^ 2 * (b₂ ^ 2 - b₂' ^ 2) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by positivity)
    · exact (pow_left_inj₀ hb₂.le hb₂'.le two_ne_zero).mp (by linarith)
  subst e3
  have e4 : a₃ = a₃' := by
    have : (b₁ ^ 2 * b₂ ^ 2) * (a₃ - a₃') = 0 := by linear_combination h5
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by positivity)
    · linarith
  rw [e4]

/-- Sharpness (moment count): moments `k ≤ 4` do not determine a `3 × 3` Jacobi matrix
(`a₃` first appears in `m₅`, with coefficient `b₁² b₂²`). -/
theorem jac3_four_moments_insufficient :
    ∃ c c' : ℝ, c ≠ c' ∧ ∀ k ≤ 4, ((jac3 0 0 c 1 1) ^ k) 0 0 = ((jac3 0 0 c' 1 1) ^ k) 0 0 := by
  refine ⟨0, 1, by norm_num, ?_⟩
  intro k hk
  interval_cases k <;> simp [jac3, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

/-! ## General n (size `n + 1`, moments `k ≤ 2n + 1`) -/

/-- Krylov matrix: column `k` is `J^k e₀` (the unnormalised Lanczos/Krylov basis). -/
def krylov {n : ℕ} (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i k => (J ^ (k : ℕ)) i 0

lemma krylov_vanish {n : ℕ} {J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hJ : IsJacobi J) :
    ∀ (k : ℕ) (i : Fin (n + 1)), k < i → (J ^ k) i 0 = 0 := by
  obtain ⟨hs, ht, -⟩ := hJ
  intro k
  induction k with
  | zero =>
    intro i hi
    have : i ≠ 0 := by intro h; subst h; simp at hi
    simp [this]
  | succ k ih =>
    intro i hi
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : k < (l : ℕ)
    · rw [ih l hl, mul_zero]
    · rw [hs.apply l i, ht l i (by omega), zero_mul]

lemma krylov_diag_pos {n : ℕ} {J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hJ : IsJacobi J) :
    ∀ (k : ℕ) (i : Fin (n + 1)), (i : ℕ) = k → 0 < (J ^ k) i 0 := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have : i = 0 := Fin.ext hi
    subst this; simp
  | succ k ih =>
    intro i hi
    have hk : k < n + 1 := by omega
    rw [pow_succ', Matrix.mul_apply, Finset.sum_eq_single (⟨k, hk⟩ : Fin (n + 1))]
    · apply mul_pos
      · rw [hJ.1.apply]
        exact hJ.2.2 ⟨k, hk⟩ i (by simp [hi])
      · exact ih _ rfl
    · intro l _ hl
      by_cases hkl : k < (l : ℕ)
      · rw [krylov_vanish hJ k l hkl, mul_zero]
      · have hlk : (l : ℕ) < k := by
          rcases lt_or_eq_of_le (not_lt.mp hkl) with h | h
          · exact h
          · exact absurd (Fin.ext h) hl
        rw [hJ.1.apply l i, hJ.2.1 l i (by omega), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

lemma krylov_upper {n : ℕ} {J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hJ : IsJacobi J) :
    (krylov J).BlockTriangular id := by
  intro i k hik
  exact krylov_vanish hJ k i hik

lemma krylov_diag {n : ℕ} {J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hJ : IsJacobi J)
    (i : Fin (n + 1)) : 0 < krylov J i i :=
  krylov_diag_pos hJ i i rfl

lemma krylov_gram {n : ℕ} {J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hJ : J.IsSymm) :
    (krylov J)ᵀ * krylov J = Matrix.of fun j k : Fin (n + 1) => (J ^ ((j : ℕ) + k)) 0 0 := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, krylov, Matrix.of_apply]
  rw [pow_add, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hJ.pow j).apply]

lemma krylov_gram_J {n : ℕ} {J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hJ : J.IsSymm) :
    (krylov J)ᵀ * J * krylov J = Matrix.of fun j k : Fin (n + 1) => (J ^ ((j : ℕ) + k + 1)) 0 0 := by
  have hJV : J * krylov J = Matrix.of fun i k : Fin (n + 1) => (J ^ ((k : ℕ) + 1)) i 0 := by
    ext i k
    simp only [Matrix.mul_apply, krylov, Matrix.of_apply]
    rw [pow_succ', Matrix.mul_apply]
  ext j k
  rw [Matrix.mul_assoc, hJV]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, krylov, Matrix.of_apply]
  rw [add_assoc, pow_add J (j : ℕ) ((k : ℕ) + 1), Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hJ.pow j).apply]

/-- Uniqueness of the Cholesky factor: upper-triangular factors with positive diagonal. -/
lemma cholesky_unique {m : ℕ} (V W : Matrix (Fin m) (Fin m) ℝ)
    (hV : V.BlockTriangular id) (hW : W.BlockTriangular id)
    (hVd : ∀ i, 0 < V i i) (hWd : ∀ i, 0 < W i i) (h : Vᵀ * V = Wᵀ * W) : V = W := by
  have hdetV : IsUnit V.det := by
    rw [Matrix.det_of_isUpperTriangular hV]
    exact (Finset.prod_pos fun i _ => hVd i).ne'.isUnit
  have : Invertible V := Matrix.invertibleOfIsUnitDet V hdetV
  set Q := W * V⁻¹ with hQ
  have hQV : Q * V = W := by
    rw [hQ, Matrix.mul_assoc, Matrix.nonsing_inv_mul V hdetV, Matrix.mul_one]
  have hQQ : Qᵀ * Q = 1 := by
    rw [hQ, Matrix.transpose_mul]
    calc (V⁻¹)ᵀ * Wᵀ * (W * V⁻¹) = (V⁻¹)ᵀ * (Wᵀ * W) * V⁻¹ := by
            simp only [Matrix.mul_assoc]
      _ = (V⁻¹)ᵀ * (Vᵀ * V) * V⁻¹ := by rw [h]
      _ = ((V⁻¹)ᵀ * Vᵀ) * (V * V⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv V hdetV, Matrix.transpose_one,
            Matrix.one_mul]
  have hQu : Q.BlockTriangular id := hW.mul (Matrix.blockTriangular_inv_of_blockTriangular hV)
  have hQinv : Q⁻¹ = Qᵀ := Matrix.inv_eq_left_inv hQQ
  have hdetQ : IsUnit Q.det := isUnit_det_of_left_inverse hQQ
  have : Invertible Q := Matrix.invertibleOfIsUnitDet Q hdetQ
  have hQtu : Qᵀ.BlockTriangular id := hQinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hQu
  have hoff : ∀ i j, i ≠ j → Q i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hl | hl
    · have := hQtu (show id i < id j from hl)
      simpa [Matrix.transpose_apply] using this
    · exact hQu (show id j < id i from hl)
  have hdiag : ∀ i, Q i i = 1 := by
    intro i
    have h1 : W i i = Q i i * V i i := by
      rw [← hQV, Matrix.mul_apply, Finset.sum_eq_single i]
      · intro l _ hl; rw [hoff i l (Ne.symm hl), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hpos : 0 < Q i i := by
      have := hWd i; rw [h1] at this
      exact pos_of_mul_pos_left this (hVd i).le
    have h2 : Q i i * Q i i = 1 := by
      have := congrFun (congrFun hQQ i) i
      rw [Matrix.mul_apply, Finset.sum_eq_single i, Matrix.one_apply_eq] at this
      · simpa [Matrix.transpose_apply] using this
      · intro l _ hl; rw [Matrix.transpose_apply, hoff l i hl, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    nlinarith
  have hQ1 : Q = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [hdiag, Matrix.one_apply_eq]
    · rw [hoff i j hij, Matrix.one_apply_ne hij]
  rw [← hQV, hQ1, Matrix.one_mul]

/-- **Discrete inverse spectral theorem (general size).** A real symmetric tridiagonal
matrix of size `n + 1` with strictly positive super-diagonal is determined by its
boundary moments `(J^k)₀₀`, `k = 0, …, 2n + 1`. Proof: the Krylov matrix `V` (columns
`J^k e₀`) is upper triangular with positive diagonal; `VᵀV` and `VᵀJV` are Hankel
matrices of moments; Cholesky uniqueness gives `V = V'`; cancel the invertible `V`. -/
theorem jacobi_inverse (n : ℕ) (J J' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hJ : IsJacobi J) (hJ' : IsJacobi J')
    (h : ∀ k ≤ 2 * n + 1, (J ^ k) 0 0 = (J' ^ k) 0 0) :
    J = J' := by
  have hG : (krylov J)ᵀ * krylov J = (krylov J')ᵀ * krylov J' := by
    rw [krylov_gram hJ.1, krylov_gram hJ'.1]
    ext j k
    simp only [Matrix.of_apply]
    exact h _ (by omega)
  have hH : (krylov J)ᵀ * J * krylov J = (krylov J')ᵀ * J' * krylov J' := by
    rw [krylov_gram_J hJ.1, krylov_gram_J hJ'.1]
    ext j k
    simp only [Matrix.of_apply]
    exact h _ (by omega)
  have hV : krylov J = krylov J' :=
    cholesky_unique _ _ (krylov_upper hJ) (krylov_upper hJ') (krylov_diag hJ) (krylov_diag hJ') hG
  rw [← hV] at hH
  have hdet : IsUnit (krylov J).det := by
    rw [Matrix.det_of_isUpperTriangular (krylov_upper hJ)]
    exact (Finset.prod_pos fun i _ => krylov_diag hJ i).ne'.isUnit
  have hU : IsUnit (krylov J) := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hUt : IsUnit (krylov J)ᵀ :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [Matrix.det_transpose]; exact hdet)
  have := hU.mul_right_cancel hH
  exact hUt.mul_left_cancel this

/-- n = 3, matrix form: a `3 × 3` Jacobi matrix is determined by moments `k = 1, …, 5`
(instance `n = 2` of `jacobi_inverse`; `k = 0` is trivially equal). -/
theorem jacobi3_inverse (J J' : Matrix (Fin 3) (Fin 3) ℝ)
    (hJ : IsJacobi J) (hJ' : IsJacobi J')
    (h : ∀ k ∈ Finset.Icc 1 5, (J ^ k) 0 0 = (J' ^ k) 0 0) :
    J = J' := by
  refine jacobi_inverse 2 J J' hJ hJ' fun k hk => ?_
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0; simp
  · exact h k (Finset.mem_Icc.mpr ⟨hpos, by omega⟩)

/-! ## Added by the adversarial reviewer: concrete instance and a generalisation -/

/-- `jac3` with positive off-diagonals satisfies `IsJacobi` (so the hypotheses of
`jacobi3_inverse` / `jacobi_inverse` are satisfiable, not vacuous). -/
theorem isJacobi_jac3 (a₁ a₂ a₃ b₁ b₂ : ℝ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    IsJacobi (jac3 a₁ a₂ a₃ b₁ b₂) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [jac3]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [jac3] at hij ⊢
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [jac3] at hij ⊢ <;> assumption

/-- Concrete use of the general theorem: any `3 × 3` Jacobi matrix whose first five
moments are those of the free chain `jac3 0 0 0 1 1` (namely `0, 1, 0, 2, 0`) *is* the
free chain. -/
theorem jacobi3_eq_free_chain (J : Matrix (Fin 3) (Fin 3) ℝ) (hJ : IsJacobi J)
    (h : ∀ k ∈ Finset.Icc 1 5, (J ^ k) 0 0 = ((jac3 0 0 0 1 1) ^ k) 0 0) :
    J = jac3 0 0 0 1 1 :=
  jacobi3_inverse J _ hJ (isJacobi_jac3 0 0 0 1 1 one_pos one_pos) h

/-- Sanity check that the free-chain moments really are `m₁..m₅ = 0, 1, 0, 2, 0`. -/
theorem jac3_free_moments :
    ((jac3 0 0 0 1 1) ^ 1) 0 0 = 0 ∧ ((jac3 0 0 0 1 1) ^ 2) 0 0 = 1 ∧
      ((jac3 0 0 0 1 1) ^ 3) 0 0 = 0 ∧ ((jac3 0 0 0 1 1) ^ 4) 0 0 = 2 ∧
      ((jac3 0 0 0 1 1) ^ 5) 0 0 = 0 := by
  simp [jac3, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]; norm_num

/-- **Lanczos uniqueness, intertwiner form (generalisation).** Let `J, J'` be Jacobi
matrices of size `n + 1` and `U` a real orthogonal matrix (`Uᵀ U = 1`) fixing the
boundary vector (`U e₀ = e₀`) and intertwining them (`U J' = J U`). Then `U = 1` and
`J = J'`. So no nontrivial orthogonal change of basis fixing site 0 maps one Jacobi
matrix to another (interpretation: `e₀` is cyclic, so the Lanczos basis is unique). -/
theorem lanczos_intertwiner_trivial (n : ℕ) (J J' U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hJ : IsJacobi J) (hJ' : IsJacobi J') (hU : Uᵀ * U = 1)
    (he : ∀ i, U i 0 = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i 0)
    (hI : U * J' = J * U) :
    U = 1 ∧ J = J' := by
  have hcol : ∀ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i, (A * U) i 0 = A i 0 := by
    intro A i
    rw [Matrix.mul_apply]; simp_rw [he]; simp [Matrix.one_apply]
  have hrow : ∀ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ), (Uᵀ * B) 0 0 = B 0 0 := by
    intro B
    rw [Matrix.mul_apply]; simp_rw [Matrix.transpose_apply, he]; simp [Matrix.one_apply]
  have hpow : ∀ k : ℕ, U * J' ^ k = J ^ k * U := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', pow_succ', ← Matrix.mul_assoc, hI, Matrix.mul_assoc, ih,
        Matrix.mul_assoc]
  have hconj : ∀ k : ℕ, J' ^ k = Uᵀ * (J ^ k * U) := by
    intro k
    rw [← hpow, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hJJ : J = J' := by
    refine jacobi_inverse n J J' hJ hJ' fun k _ => ?_
    rw [hconj, hrow, hcol]
  refine ⟨?_, hJJ⟩
  subst hJJ
  have hUV : U * krylov J = 1 * krylov J := by
    ext i k
    rw [Matrix.one_mul]
    have := congrFun (congrFun (hpow k) i) 0
    rw [hcol] at this
    simp only [Matrix.mul_apply, krylov, Matrix.of_apply] at this ⊢
    exact this
  have hdet : IsUnit (krylov J).det := by
    rw [Matrix.det_of_isUpperTriangular (krylov_upper hJ)]
    exact (Finset.prod_pos fun i _ => krylov_diag hJ i).ne'.isUnit
  exact ((Matrix.isUnit_iff_isUnit_det _).mpr hdet).mul_right_cancel hUV

end A13
