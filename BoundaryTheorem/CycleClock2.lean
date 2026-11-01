import Mathlib
import BoundaryTheorem.CycleClock

/-!
# Cycle vs clock, batch 2

Fidelity record: `FIDELITY_cycle_clock.md` (section "Batch 2").

* A3'' `complex_hermitian_nontrivial_clock_exists`, A2' `real_clock_needs_skew`;
* F1 `frechet_hoeffding`, F2 `bit_coupling_attainment` (formalisations of sketches),
  F3 `mean_corr_lower_bound`, F4 `no_three_way_antimonotone`;
* T1 `stochastic_inv_stochastic_is_perm`, T2 `stochastic_group_trivial`.
-/

open Matrix

namespace CycleClock

/-! ## Part A, continued -/

/-- A3'' (non-trivial complex clock exists) -/
theorem complex_hermitian_nontrivial_clock_exists :
    ∃ H : Matrix (Fin 2) (Fin 2) ℂ, H.IsHermitian ∧ ∀ c : ℂ, H ≠ c • 1 := by
  refine ⟨!![0, 1; 1, 0], ?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  · intro c hc
    have h01 := congrFun (congrFun hc 0) 1
    have h00 := congrFun (congrFun hc 0) 0
    simp at h01 h00

section OperatorNorm2

open scoped Matrix.Norms.Operator

/-- Helper: if `exp (u • A) = exp (u • B)` for every real `u`, then `A = B`
(differentiate at `u = 0`; the `L∞` operator norm is chosen locally, only to do calculus). -/
lemma eq_of_exp_smul_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ)
    (h : ∀ u : ℝ, NormedSpace.exp (u • A) = NormedSpace.exp (u • B)) : A = B := by
  have hA := hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)
  have hB := hasDerivAt_exp_smul_const (𝕂 := ℝ) B (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at hA hB
  have hA' : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • B)) A 0 :=
    hA.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => (h u).symm)
  exact hA'.unique hB

end OperatorNorm2

/-- A2' (converse of real_skew_clock) -/
theorem real_clock_needs_skew {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hU : ∀ t : ℝ, NormedSpace.exp (t • A) ∈ Matrix.orthogonalGroup ι ℝ) : Aᵀ = -A := by
  apply eq_of_exp_smul_eq
  intro u
  have h1 := hU u
  rw [Matrix.mem_orthogonalGroup_iff'] at h1
  have h2 : NormedSpace.exp (u • A) * NormedSpace.exp (-(u • A)) = 1 := by
    have := exp_neg_mul_exp_self (-(u • A))
    rwa [neg_neg] at this
  rw [← Matrix.exp_transpose, transpose_smul] at h1
  rw [smul_neg]
  calc NormedSpace.exp (u • Aᵀ)
      = NormedSpace.exp (u • Aᵀ) * (NormedSpace.exp (u • A) * NormedSpace.exp (-(u • A))) := by
        rw [h2, mul_one]
    _ = (NormedSpace.exp (u • Aᵀ) * NormedSpace.exp (u • A)) * NormedSpace.exp (-(u • A)) := by
        rw [mul_assoc]
    _ = NormedSpace.exp (-(u • A)) := by rw [h1, one_mul]

/-! ## Part F: Fréchet–Hoeffding and "chaos can't scale" -/

/-- Probability of an event `S` under point masses `p` on a finite space. -/
noncomputable def prob {Ω : Type*} (p : Ω → ℝ) (S : Finset Ω) : ℝ := ∑ ω ∈ S, p ω

/-- F1 (Fréchet–Hoeffding, two events, finite probability space). -/
theorem frechet_hoeffding {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1) (A B : Finset Ω) :
    max 0 (prob p A + prob p B - 1) ≤ prob p (A ∩ B) ∧
      prob p (A ∩ B) ≤ min (prob p A) (prob p B) := by
  unfold prob
  have hunion := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := p)
  have hle1 : ∑ ω ∈ A ∪ B, p ω ≤ 1 := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun ω _ _ => hp ω
  have hnn : 0 ≤ ∑ ω ∈ A ∩ B, p ω := Finset.sum_nonneg fun ω _ => hp ω
  refine ⟨max_le hnn (by linarith), le_min ?_ ?_⟩
  · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left fun ω _ _ => hp ω
  · exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun ω _ _ => hp ω

/-- A joint law `q` of two bits whose marginals are `P(first = true) = x`, `P(second = true) = y`. -/
def IsBitCoupling (x y : ℝ) (q : Bool × Bool → ℝ) : Prop :=
  (∀ s, 0 ≤ q s) ∧ ∑ s, q s = 1 ∧
    ∑ s with s.1 = true, q s = x ∧ ∑ s with s.2 = true, q s = y

/-- Helper: every value `t` of `P(both true)` allowed by the Fréchet–Hoeffding bounds is attained. -/
lemma bit_coupling_of_bounds (x y t : ℝ) (h0 : 0 ≤ t) (h1 : x + y - 1 ≤ t) (hx : t ≤ x)
    (hy : t ≤ y) : ∃ q, IsBitCoupling x y q ∧ q (true, true) = t := by
  refine ⟨fun s => if s = (true, true) then t else if s = (true, false) then x - t
    else if s = (false, true) then y - t else 1 - x - y + t, ⟨?_, ?_, ?_, ?_⟩, by simp⟩
  · rintro ⟨_ | _, _ | _⟩ <;> simp <;> linarith
  · simp [Fintype.sum_prod_type]
  · simp [Finset.sum_filter, Fintype.sum_prod_type]
  · simp [Finset.sum_filter, Fintype.sum_prod_type]

/-- F2 (attainment for bits): for marginals `x, y ∈ [0,1]` the upper Fréchet–Hoeffding bound,
the lower bound, and the independent value are all attained by joint laws of two bits. -/
theorem bit_coupling_attainment (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (∃ q, IsBitCoupling x y q ∧ q (true, true) = min x y) ∧
    (∃ q, IsBitCoupling x y q ∧ q (true, true) = max 0 (x + y - 1)) ∧
    (∃ q, IsBitCoupling x y q ∧ q (true, true) = x * y) := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · apply bit_coupling_of_bounds
    · exact le_min hx0 hy0
    · rcases min_cases x y with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
    · exact min_le_left _ _
    · exact min_le_right _ _
  · apply bit_coupling_of_bounds
    · exact le_max_left _ _
    · exact le_max_right _ _
    · exact max_le hx0 (by linarith)
    · exact max_le hy0 (by linarith)
  · apply bit_coupling_of_bounds
    · positivity
    · nlinarith
    · nlinarith
    · nlinarith

/-- F3 ("chaos can't scale", correlation-matrix form) -/
theorem mean_corr_lower_bound {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.PosSemidef) (hd : ∀ i, R i i = 1) :
    ∑ i, ∑ j, (if i = j then 0 else R i j) ≥ -(n : ℝ) := by
  have h1 := hR.dotProduct_mulVec_nonneg (fun _ => 1)
  simp only [dotProduct, mulVec, Pi.star_apply, star_one, one_mul, mul_one] at h1
  have hrow : ∀ i, ∑ j, (if i = j then 0 else R i j) = ∑ j, R i j - 1 := by
    intro i
    have : ∑ j, R i j = ∑ j, (if i = j then 0 else R i j) + ∑ j, (if i = j then R i j else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    rw [this, Finset.sum_ite_eq]
    simp [hd i]
  simp only [hrow, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  linarith

/-- F4 (three bits can't be pairwise perfectly anti-correlated) -/
theorem no_three_way_antimonotone :
    ¬ ∃ q : (Fin 3 → Bool) → ℝ, (∀ s, 0 ≤ q s) ∧ ∑ s, q s = 1 ∧
      ∀ i j, i ≠ j → ∑ s with s i = s j, q s = 0 := by
  rintro ⟨q, hq, hsum, hanti⟩
  have key : ∀ s : Fin 3 → Bool, ∃ i j, i ≠ j ∧ s i = s j := by decide
  have hzero : ∀ s, q s = 0 := by
    intro s
    obtain ⟨i, j, hij, hs⟩ := key s
    have := hanti i j hij
    rw [Finset.sum_eq_zero_iff_of_nonneg fun s _ => hq s] at this
    exact this s (by simp [hs])
  simp [hzero] at hsum

/-! ## Part T: lossless classical dynamics -/

-- `hPr` (row sums of `P`) turns out to be redundant: it follows from the other hypotheses.
set_option linter.unusedVariables false in
/-- T1 (lossless classical dynamics are permutations) -/
theorem stochastic_inv_stochastic_is_perm {ι : Type*} [Fintype ι] [DecidableEq ι] (P Q : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hPr : ∀ i, ∑ j, P i j = 1)
    (hQ : ∀ i j, 0 ≤ Q i j) (hQr : ∀ i, ∑ j, Q i j = 1) (hPQ : P * Q = 1) :
    ∃ σ : Equiv.Perm ι, P = (σ.toPEquiv.toMatrix : Matrix ι ι ℝ) := by
  have hQP : Q * P = 1 := mul_eq_one_comm.mp hPQ
  -- for each row `i` of `P`, a column `f i` carrying a positive product `P i (f i) * Q (f i) i`
  have hex : ∀ i, ∃ j, 0 < P i j ∧ 0 < Q j i := by
    intro i
    have hii : ∑ j, P i j * Q j i = 1 := by
      have := congrFun (congrFun hPQ i) i
      simpa [Matrix.mul_apply] using this
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hii]; exact one_ne_zero)
    refine ⟨j, lt_of_le_of_ne (hP i j) ?_, lt_of_le_of_ne (hQ j i) ?_⟩
    · intro h; exact hj (by rw [← h, zero_mul])
    · intro h; exact hj (by rw [← h, mul_zero])
  choose f hfP hfQ using hex
  -- row `f i` of `Q` is the unit vector at `i`
  have hQrow : ∀ i k, Q (f i) k = if k = i then 1 else 0 := by
    have hoff : ∀ i k, k ≠ i → Q (f i) k = 0 := by
      intro i k hki
      have hik : ∑ j, P i j * Q j k = 0 := by
        have := congrFun (congrFun hPQ i) k
        simpa [Matrix.mul_apply, Matrix.one_apply, Ne.symm hki] using this
      rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (hP i j) (hQ j k)] at hik
      have := hik (f i) (Finset.mem_univ _)
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (hfP i).ne'
      · exact h
    intro i k
    split_ifs with hki
    · subst hki
      have := hQr (f k)
      rwa [Finset.sum_eq_single k (fun b _ hb => hoff k b hb) (by simp)] at this
    · exact hoff i k hki
  -- hence row `i` of `P` is the unit vector at `f i`
  have hProw : ∀ i m, P i m = if f i = m then 1 else 0 := by
    intro i m
    have := congrFun (congrFun hQP (f i)) m
    simp only [Matrix.mul_apply, hQrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Matrix.one_apply] at this
    exact this
  have hinj : Function.Injective f := by
    intro i i' h
    have h1 := hQrow i i
    have h2 := hQrow i' i
    rw [← h, h1] at h2
    by_contra hne
    simp [hne] at h2
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_⟩
  ext i m
  rw [hProw, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  simp [Option.mem_def]

/-- T2 (continuous one-parameter group of stochastic matrices is constant) -/
theorem stochastic_group_trivial {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ℝ → Matrix ι ι ℝ) (hc : Continuous T)
    (h0 : T 0 = 1) (hadd : ∀ s t, T (s + t) = T s * T t)
    (hstoch : ∀ t, (∀ i j, 0 ≤ T t i j) ∧ ∀ i, ∑ j, T t i j = 1) : ∀ t, T t = 1 := by
  set S : Set (Matrix ι ι ℝ) :=
    Set.range fun σ : Equiv.Perm ι => (σ.toPEquiv.toMatrix : Matrix ι ι ℝ) with hS
  have hmaps : Set.MapsTo T Set.univ S := by
    intro t _
    have hinv : T t * T (-t) = 1 := by rw [← hadd, add_neg_cancel, h0]
    obtain ⟨σ, hσ⟩ := stochastic_inv_stochastic_is_perm (T t) (T (-t)) (hstoch t).1 (hstoch t).2
      (hstoch (-t)).1 (hstoch (-t)).2 hinv
    exact ⟨σ, hσ.symm⟩
  have hdisc : IsDiscrete S := (Set.finite_range _).isDiscrete
  intro t
  rw [← h0]
  exact isPreconnected_univ.constant_of_mapsTo hdisc hc.continuousOn hmaps
    (Set.mem_univ t) (Set.mem_univ 0)

end CycleClock
