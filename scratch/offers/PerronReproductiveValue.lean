import Mathlib

/-!
# Reproductive value as the unique no-arbitrage exchange rate

Let `M` be a square real matrix with strictly positive entries (the projection matrix of a
structured population: `M i j` is the contribution of an individual in state `i` to state `j`).
A row vector `w` of exchange rates assigns a value to each state.

PROVED
* `PerronReproductiveValue.exists_pos_left_eigenvector`: for `n ≥ 1` and `M : Matrix (Fin n) (Fin n) ℝ`
  with all entries positive, there are `λ > 0` and `v` with all `v i > 0` and `v ᵥ* M = λ • v`
  (a positive left Perron eigenvector). Proved by maximising the Collatz-Wielandt function
  `x ↦ min_j ((x M) M)_j / (x M)_j` over the compact standard simplex.
* `PerronReproductiveValue.exists_pos_right_eigenvector`: the same for right eigenvectors.
* `PerronReproductiveValue.left_eigenvector_unique`: if `v > 0`, `v ᵥ* M = λ • v`, and `w > 0`,
  `w ᵥ* M = μ • w`, then `μ = λ` and `w = t • v` for some `t > 0`.
* `PerronReproductiveValue.common_growth_iff`: for any `w` and `μ`,
  `(∀ x ≥ 0, w ⬝ᵥ (M *ᵥ x) = μ * (w ⬝ᵥ x)) ↔ w ᵥ* M = μ • w`
  (the `w`-weighted total grows by the common factor `μ` from every state iff `w` is a left
  eigenvector with eigenvalue `μ`).
* `PerronReproductiveValue.exists_common_growth_iff`: for `w > 0` and a positive left eigenvector
  `v`, `(∃ μ, ∀ x ≥ 0, w ⬝ᵥ (M *ᵥ x) = μ * (w ⬝ᵥ x)) ↔ ∃ t > 0, w = t • v`.
* `PerronReproductiveValue.arbitrage`: if `w > 0` is not a positive multiple of `v`, then for
  every `μ` there is a state `x ≥ 0` with `w ⬝ᵥ (M *ᵥ x) ≠ μ * (w ⬝ᵥ x)`.
* `PerronReproductiveValue.common_growth_rate_eq`: any common growth factor of a positive `w`
  equals the Perron eigenvalue `λ`.

The general statements are proved for an arbitrary nonempty finite index type; the `Fin n`
versions take `1 ≤ n`.

INTERPRETED (not formalized)
* Calling `v` the reproductive value and the failure of a common growth factor an arbitrage
  opportunity is interpretation; the theorems are the linear-algebra statements above.
-/

namespace PerronReproductiveValue

open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard simplex of nonnegative vectors summing to one. -/
def simplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

omit [DecidableEq ι] in
lemma isCompact_simplex : IsCompact (simplex ι) := by
  have hcl : IsClosed (simplex ι) := by
    have : simplex ι = (⋂ i, {x : ι → ℝ | 0 ≤ x i}) ∩ {x | ∑ i, x i = 1} := by
      ext x; simp [simplex]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun i => ?_) ?_
    · exact isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)) hcl ?_
  intro x hx
  refine ⟨fun i => hx.1 i, fun i => ?_⟩
  have := Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
  simpa [hx.2] using this

omit [DecidableEq ι] in
lemma vecMul_apply_eq (x : ι → ℝ) (M : Matrix ι ι ℝ) (j : ι) :
    (x ᵥ* M) j = ∑ i, x i * M i j := by
  simp [Matrix.vecMul, dotProduct]

omit [DecidableEq ι] in
lemma continuous_vecMul_apply (M : Matrix ι ι ℝ) (j : ι) :
    Continuous fun x : ι → ℝ => (x ᵥ* M) j := by
  simp only [vecMul_apply_eq]
  fun_prop

omit [DecidableEq ι] in
lemma continuous_vecMul (M : Matrix ι ι ℝ) : Continuous fun x : ι → ℝ => x ᵥ* M :=
  continuous_pi fun j => continuous_vecMul_apply M j

omit [DecidableEq ι] in
/-- A nonnegative nonzero vector times a positive matrix is strictly positive. -/
lemma vecMul_pos {M : Matrix ι ι ℝ} (hM : ∀ i j, 0 < M i j) {x : ι → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hx : x ≠ 0) (j : ι) : 0 < (x ᵥ* M) j := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hxi : 0 < x i := lt_of_le_of_ne (hx0 i) (Ne.symm hi)
  rw [vecMul_apply_eq]
  exact Finset.sum_pos' (fun k _ => mul_nonneg (hx0 k) (hM k j).le)
    ⟨i, Finset.mem_univ _, mul_pos hxi (hM i j)⟩

omit [DecidableEq ι] in
lemma ne_zero_of_simplex {x : ι → ℝ} (hx : x ∈ simplex ι) : x ≠ 0 := by
  intro h
  have := hx.2
  simp [h] at this

/-- Existence of a positive left eigenvector for a positive matrix on a nonempty index type. -/
theorem exists_pos_left_eigenvector' [Nonempty ι] (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ v : ι → ℝ, (∀ i, 0 < v i) ∧ v ᵥ* M = lam • v := by
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  have hpos : ∀ x ∈ simplex ι, ∀ j, 0 < (x ᵥ* M) j := fun x hx j =>
    vecMul_pos hM hx.1 (ne_zero_of_simplex hx) j
  let h : (ι → ℝ) → ℝ := fun x =>
    (Finset.univ : Finset ι).inf' hne (fun j => ((x ᵥ* M) ᵥ* M) j / (x ᵥ* M) j)
  have hcont : ContinuousOn h (simplex ι) := by
    refine ContinuousOn.finset_inf'_apply hne fun j _ => ?_
    refine ContinuousOn.div ?_ ?_ ?_
    · exact ((continuous_vecMul_apply M j).comp (continuous_vecMul M)).continuousOn
    · exact (continuous_vecMul_apply M j).continuousOn
    · exact fun x hx => (hpos x hx j).ne'
  -- the simplex is nonempty
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hS : (simplex ι).Nonempty :=
    ⟨Pi.single i0 1, fun i => by
      by_cases hi : i = i0 <;> simp [hi], by simp⟩
  obtain ⟨xs, hxs, hmax⟩ := isCompact_simplex.exists_isMaxOn hS hcont
  set y := xs ᵥ* M with hy
  set z := y ᵥ* M with hz
  set lam := h xs with hlam
  have hypos : ∀ j, 0 < y j := hpos xs hxs
  obtain ⟨j0⟩ := ‹Nonempty ι›
  have hy0 : y ≠ 0 := fun h0 => by have := hypos j0; rw [h0] at this; simp at this
  have hlam_le : ∀ j, lam ≤ z j / y j := fun j =>
    Finset.inf'_le (fun j => ((xs ᵥ* M) ᵥ* M) j / (xs ᵥ* M) j) (Finset.mem_univ j)
  have hle : ∀ j, lam * y j ≤ z j := fun j => (le_div_iff₀ (hypos j)).1 (hlam_le j)
  set d := z - lam • y with hd
  have hd0 : ∀ j, 0 ≤ d j := fun j => by
    simp only [hd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hle j]
  have hdz : d = 0 := by
    by_contra hdne
    have hdM : ∀ j, 0 < (d ᵥ* M) j := vecMul_pos hM hd0 hdne
    have hdM' : d ᵥ* M = z ᵥ* M - lam • z := by
      rw [hd, Matrix.sub_vecMul, Matrix.smul_vecMul]
    have hsum : 0 < ∑ j, y j := Finset.sum_pos (fun j _ => hypos j) hne
    set s := ∑ j, y j with hs
    have hx' : s⁻¹ • y ∈ simplex ι := by
      refine ⟨fun i => ?_, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.2 hsum.le) (hypos i).le
      · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        exact inv_mul_cancel₀ hsum.ne'
    have hgt : lam < h (s⁻¹ • y) := by
      refine (Finset.lt_inf'_iff hne).2 fun j _ => ?_
      have e1 : (s⁻¹ • y) ᵥ* M = s⁻¹ • z := by rw [Matrix.smul_vecMul]
      have e2 : ((s⁻¹ • y) ᵥ* M) ᵥ* M = s⁻¹ • (z ᵥ* M) := by
        rw [e1, Matrix.smul_vecMul]
      rw [e2, e1]
      simp only [Pi.smul_apply, smul_eq_mul]
      have hsinv : s⁻¹ ≠ 0 := inv_ne_zero hsum.ne'
      rw [mul_div_mul_left _ _ hsinv]
      have hzj : 0 < z j := vecMul_pos hM (fun i => (hypos i).le) hy0 j
      rw [lt_div_iff₀ hzj]
      have := hdM j
      rw [hdM'] at this
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      linarith
    have := hmax hx'
    change h (s⁻¹ • y) ≤ h xs at this
    linarith
  have heig : y ᵥ* M = lam • y := by
    have := hdz
    rw [hd, sub_eq_zero] at this
    exact this
  have hlampos : 0 < lam := by
    have h1 : 0 < (y ᵥ* M) j0 := vecMul_pos hM (fun i => (hypos i).le) hy0 j0
    rw [heig] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    exact pos_of_mul_pos_left h1 (hypos j0).le
  exact ⟨lam, hlampos, y, hypos, heig⟩

/-- Existence of a positive right eigenvector for a positive matrix on a nonempty index type. -/
theorem exists_pos_right_eigenvector' [Nonempty ι] (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ u : ι → ℝ, (∀ i, 0 < u i) ∧ M *ᵥ u = lam • u := by
  obtain ⟨lam, hlam, u, hu, hEu⟩ :=
    exists_pos_left_eigenvector' Mᵀ (fun i j => by simpa using hM j i)
  exact ⟨lam, hlam, u, hu, by rw [← Matrix.vecMul_transpose]; exact hEu⟩

/-- Uniqueness of the positive left eigenvector up to a positive scalar, and of its eigenvalue. -/
theorem left_eigenvector_unique' [Nonempty ι] (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j)
    {lam : ℝ} {v : ι → ℝ} (hv : ∀ i, 0 < v i) (hvM : v ᵥ* M = lam • v)
    {mu : ℝ} {w : ι → ℝ} (hw : ∀ i, 0 < w i) (hwM : w ᵥ* M = mu • w) :
    mu = lam ∧ ∃ t : ℝ, 0 < t ∧ w = t • v := by
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  obtain ⟨r, -, u, hu, hMu⟩ := exists_pos_right_eigenvector' M hM
  have rate : ∀ {a : ℝ} {p : ι → ℝ}, (∀ i, 0 < p i) → p ᵥ* M = a • p → a = r := by
    intro a p hp hpM
    have e := Matrix.dotProduct_mulVec p M u
    rw [hMu, hpM, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at e
    have hpu : 0 < p ⬝ᵥ u := by
      simp only [dotProduct]
      exact Finset.sum_pos (fun i _ => mul_pos (hp i) (hu i)) hne
    exact (mul_right_cancel₀ hpu.ne' e).symm
  have hmu : mu = lam := (rate hw hwM).trans (rate hv hvM).symm
  refine ⟨hmu, ?_⟩
  obtain ⟨k, -, hk⟩ := Finset.exists_min_image Finset.univ (fun j => w j / v j) hne
  set t := w k / v k with ht
  have htpos : 0 < t := div_pos (hw k) (hv k)
  set d := w - t • v with hd
  have hd0 : ∀ j, 0 ≤ d j := fun j => by
    have h1 : t ≤ w j / v j := hk j (Finset.mem_univ j)
    have h2 : t * v j ≤ w j := (le_div_iff₀ (hv j)).1 h1
    simp only [hd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hdk : d k = 0 := by
    simp only [hd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ht]
    rw [div_mul_cancel₀ _ (hv k).ne']
    ring
  have hdM : d ᵥ* M = lam • d := by
    rw [hd, Matrix.sub_vecMul, Matrix.smul_vecMul, hwM, hvM, hmu, smul_sub, smul_comm t lam v]
  refine ⟨t, htpos, ?_⟩
  by_contra hne'
  have hdne : d ≠ 0 := by
    intro h0
    apply hne'
    rw [hd, sub_eq_zero] at h0
    exact h0
  have := vecMul_pos hM hd0 hdne k
  rw [hdM] at this
  simp only [Pi.smul_apply, smul_eq_mul, hdk, mul_zero] at this
  exact lt_irrefl 0 this

/-- A `w`-weighted total grows by the common factor `mu` from every nonnegative state iff `w` is a
left eigenvector of `M` with eigenvalue `mu`. No positivity is needed. -/
theorem common_growth_iff' (M : Matrix ι ι ℝ) (w : ι → ℝ) (mu : ℝ) :
    (∀ x : ι → ℝ, (∀ i, 0 ≤ x i) → w ⬝ᵥ (M *ᵥ x) = mu * (w ⬝ᵥ x)) ↔ w ᵥ* M = mu • w := by
  constructor
  · intro h
    funext j
    have hx := h (Pi.single j 1) (fun i => by
      by_cases hij : i = j <;> simp [hij])
    rw [Matrix.dotProduct_mulVec, dotProduct_single, dotProduct_single] at hx
    simpa using hx
  · intro h x _
    rw [Matrix.dotProduct_mulVec, h, smul_dotProduct, smul_eq_mul]

/-! ## Statements for `Fin n` with `n ≥ 1` -/

variable {n : ℕ}

theorem exists_pos_left_eigenvector (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, 0 < M i j) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ v : Fin n → ℝ, (∀ i, 0 < v i) ∧ v ᵥ* M = lam • v :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exists_pos_left_eigenvector' M hM

theorem exists_pos_right_eigenvector (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, 0 < M i j) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ u : Fin n → ℝ, (∀ i, 0 < u i) ∧ M *ᵥ u = lam • u :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exists_pos_right_eigenvector' M hM

theorem left_eigenvector_unique (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, 0 < M i j)
    {lam : ℝ} {v : Fin n → ℝ} (hv : ∀ i, 0 < v i) (hvM : v ᵥ* M = lam • v)
    {mu : ℝ} {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) (hwM : w ᵥ* M = mu • w) :
    mu = lam ∧ ∃ t : ℝ, 0 < t ∧ w = t • v :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  left_eigenvector_unique' M hM hv hvM hw hwM

theorem common_growth_iff (M : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) (mu : ℝ) :
    (∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → w ⬝ᵥ (M *ᵥ x) = mu * (w ⬝ᵥ x)) ↔ w ᵥ* M = mu • w :=
  common_growth_iff' M w mu

/-- A positive exchange-rate vector admits a common growth factor iff it is a positive multiple of
the positive left eigenvector `v`. -/
theorem exists_common_growth_iff (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, 0 < M i j)
    {lam : ℝ} {v : Fin n → ℝ} (hv : ∀ i, 0 < v i) (hvM : v ᵥ* M = lam • v)
    {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) :
    (∃ mu : ℝ, ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → w ⬝ᵥ (M *ᵥ x) = mu * (w ⬝ᵥ x)) ↔
      ∃ t : ℝ, 0 < t ∧ w = t • v := by
  constructor
  · rintro ⟨mu, hmu⟩
    exact (left_eigenvector_unique hn M hM hv hvM hw ((common_growth_iff M w mu).1 hmu)).2
  · rintro ⟨t, -, rfl⟩
    refine ⟨lam, (common_growth_iff M _ lam).2 ?_⟩
    rw [Matrix.smul_vecMul, hvM, smul_comm]

/-- Any common growth factor of a positive exchange-rate vector is the Perron eigenvalue. -/
theorem common_growth_rate_eq (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, 0 < M i j)
    {lam : ℝ} {v : Fin n → ℝ} (hv : ∀ i, 0 < v i) (hvM : v ᵥ* M = lam • v)
    {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) {mu : ℝ}
    (hmu : ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → w ⬝ᵥ (M *ᵥ x) = mu * (w ⬝ᵥ x)) :
    mu = lam :=
  (left_eigenvector_unique hn M hM hv hvM hw ((common_growth_iff M w mu).1 hmu)).1

/-- If a positive exchange-rate vector `w` is not a positive multiple of the left Perron
eigenvector `v`, then for every proposed factor `mu` some nonnegative state breaks it. -/
theorem arbitrage (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, 0 < M i j)
    {lam : ℝ} {v : Fin n → ℝ} (hv : ∀ i, 0 < v i) (hvM : v ᵥ* M = lam • v)
    {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) (hnot : ¬ ∃ t : ℝ, 0 < t ∧ w = t • v) (mu : ℝ) :
    ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧ w ⬝ᵥ (M *ᵥ x) ≠ mu * (w ⬝ᵥ x) := by
  by_contra h
  push Not at h
  exact hnot ((exists_common_growth_iff hn M hM hv hvM hw).1 ⟨mu, h⟩)

end PerronReproductiveValue
