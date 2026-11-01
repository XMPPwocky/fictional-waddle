import Mathlib

/-!
# Diversity prediction theorem (Scott Page)

Setting: `N ≥ 1` guesses `g : Fin N → ℝ` of a true value `θ : ℝ`, crowd mean
`m = (1/N) Σ g i`.

PROVED
* `sum_sub_mean_eq_zero`: `Σ (g i - m) = 0`.
* `sum_sq_decomp`: `Σ (g i - θ)² = Σ (g i - m)² + N (m - θ)²`.
* `diversity_prediction`: `(m - θ)² = (1/N) Σ (g i - θ)² - (1/N) Σ (g i - m)²`
  (crowd error = average individual error - diversity).
* `crowd_le_avg`: `(m - θ)² ≤ (1/N) Σ (g i - θ)²`.
* `crowd_eq_avg_iff`: `(m - θ)² = (1/N) Σ (g i - θ)² ↔ ∀ i j, g i = g j`.
* `avg_sub_crowd_eq_diversity`:
  `(1/N) Σ (g i - θ)² - (m - θ)² = (1/N) Σ (g i - m)²`.
* `diversity_nonneg`, `diversity_eq_zero_iff`: diversity is `≥ 0`, and `= 0` iff all
  guesses are equal.

INTERPRETED
* "Crowd error" is `crowdError g θ = (m - θ)²`; "average individual error" is
  `avgError g θ = (1/N) Σ (g i - θ)²`; "diversity" is `diversity g = (1/N) Σ (g i - m)²`.
* "Equality iff all guesses are equal" is read as equality in corollary (1), i.e.
  `crowdError = avgError ↔ ∀ i j, g i = g j`.
* "Beats by exactly the diversity" is read as `avgError - crowdError = diversity`.
* `N ≥ 1` is the hypothesis `hN : 1 ≤ N`; the identity itself is stated for every `θ`.
-/

namespace DiversityPredictionA

open Finset

variable {N : ℕ}

/-- Crowd mean `m = (1/N) Σ g i`. -/
noncomputable def mean (g : Fin N → ℝ) : ℝ := (1 / (N : ℝ)) * ∑ i, g i

/-- Crowd error `(m - θ)²`. -/
noncomputable def crowdError (g : Fin N → ℝ) (θ : ℝ) : ℝ := (mean g - θ) ^ 2

/-- Average individual error `(1/N) Σ (g i - θ)²`. -/
noncomputable def avgError (g : Fin N → ℝ) (θ : ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, (g i - θ) ^ 2

/-- Diversity `(1/N) Σ (g i - m)²`. -/
noncomputable def diversity (g : Fin N → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, (g i - mean g) ^ 2

lemma natCast_ne_zero (hN : 1 ≤ N) : (N : ℝ) ≠ 0 := by
  have : (0 : ℝ) < N := by exact_mod_cast hN
  exact this.ne'

lemma natCast_pos (hN : 1 ≤ N) : (0 : ℝ) < N := by exact_mod_cast hN

/-- Deviations from the mean sum to zero. -/
theorem sum_sub_mean_eq_zero (hN : 1 ≤ N) (g : Fin N → ℝ) :
    ∑ i, (g i - mean g) = 0 := by
  have hN0 := natCast_ne_zero hN
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mean]
  field_simp
  ring

/-- `Σ (g i - θ)² = Σ (g i - m)² + N (m - θ)²`. -/
theorem sum_sq_decomp (hN : 1 ≤ N) (g : Fin N → ℝ) (θ : ℝ) :
    ∑ i, (g i - θ) ^ 2 = ∑ i, (g i - mean g) ^ 2 + (N : ℝ) * (mean g - θ) ^ 2 := by
  have h0 := sum_sub_mean_eq_zero hN g
  have hexp : ∀ i, (g i - θ) ^ 2
      = (g i - mean g) ^ 2 + 2 * (mean g - θ) * (g i - mean g) + (mean g - θ) ^ 2 := by
    intro i; ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h0,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Diversity prediction theorem:
`(m - θ)² = (1/N) Σ (g i - θ)² - (1/N) Σ (g i - m)²`. -/
theorem diversity_prediction (hN : 1 ≤ N) (g : Fin N → ℝ) (θ : ℝ) :
    (mean g - θ) ^ 2
      = (1 / (N : ℝ)) * ∑ i, (g i - θ) ^ 2 - (1 / (N : ℝ)) * ∑ i, (g i - mean g) ^ 2 := by
  have hN0 := natCast_ne_zero hN
  rw [sum_sq_decomp hN g θ]
  field_simp
  ring

/-- The identity in named form: crowd error = average individual error - diversity. -/
theorem crowdError_eq (hN : 1 ≤ N) (g : Fin N → ℝ) (θ : ℝ) :
    crowdError g θ = avgError g θ - diversity g :=
  diversity_prediction hN g θ

theorem diversity_nonneg (g : Fin N → ℝ) : 0 ≤ diversity g := by
  unfold diversity
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- Diversity vanishes iff all guesses are equal. -/
theorem diversity_eq_zero_iff (hN : 1 ≤ N) (g : Fin N → ℝ) :
    diversity g = 0 ↔ ∀ i j, g i = g j := by
  have hN0 := natCast_ne_zero hN
  have hpos := natCast_pos hN
  constructor
  · intro h
    unfold diversity at h
    have hs : ∑ i, (g i - mean g) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 (by positivity)
      · exact h1
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (g i - mean g))).mp hs
    have hm : ∀ i, g i = mean g := by
      intro i
      have := hall i (Finset.mem_univ i)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith
    intro i j
    rw [hm i, hm j]
  · intro h
    have hm : ∀ i, mean g = g i := by
      intro i
      unfold mean
      have : ∑ j, g j = ∑ _j : Fin N, g i := Finset.sum_congr rfl (fun j _ => h j i)
      rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    unfold diversity
    have : ∑ i, (g i - mean g) ^ 2 = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [hm i]; ring)
    rw [this, mul_zero]

/-- Corollary (1): the crowd is never worse than the average individual. -/
theorem crowd_le_avg (hN : 1 ≤ N) (g : Fin N → ℝ) (θ : ℝ) :
    (mean g - θ) ^ 2 ≤ (1 / (N : ℝ)) * ∑ i, (g i - θ) ^ 2 := by
  have h := crowdError_eq hN g θ
  have hd := diversity_nonneg g
  unfold crowdError avgError at h
  linarith

/-- Corollary (2): equality in (1) holds iff all guesses are equal. -/
theorem crowd_eq_avg_iff (hN : 1 ≤ N) (g : Fin N → ℝ) (θ : ℝ) :
    (mean g - θ) ^ 2 = (1 / (N : ℝ)) * ∑ i, (g i - θ) ^ 2 ↔ ∀ i j, g i = g j := by
  rw [← diversity_eq_zero_iff hN g]
  have h := crowdError_eq hN g θ
  unfold crowdError avgError at h
  constructor
  · intro he; linarith
  · intro hd; linarith

/-- Corollary (3): the crowd beats the average individual by exactly the diversity. -/
theorem avg_sub_crowd_eq_diversity (hN : 1 ≤ N) (g : Fin N → ℝ) (θ : ℝ) :
    (1 / (N : ℝ)) * ∑ i, (g i - θ) ^ 2 - (mean g - θ) ^ 2
      = (1 / (N : ℝ)) * ∑ i, (g i - mean g) ^ 2 := by
  rw [diversity_prediction hN g θ]
  ring

end DiversityPredictionA
