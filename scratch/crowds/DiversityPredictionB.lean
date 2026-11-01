import Mathlib

/-!
# Diversity prediction theorem (Scott Page)

For `N ≥ 1` guesses `g : Fin N → ℝ` of a true value `θ`, with crowd mean
`m = (1/N) * Σ i, g i`:

  `(m - θ)^2 = (1/N) * Σ i, (g i - θ)^2 - (1/N) * Σ i, (g i - m)^2`.

PROVED:
* `diversity_prediction`: the exact identity above
  (crowd error = average individual error - diversity).
* `crowd_le_avg`: `(m - θ)^2 ≤ (1/N) * Σ i, (g i - θ)^2`.
* `crowd_eq_avg_iff`: equality holds in `crowd_le_avg` iff `∀ i j, g i = g j`.
* `avg_sub_crowd`: `(1/N) * Σ i, (g i - θ)^2 - (m - θ)^2 = (1/N) * Σ i, (g i - m)^2`
  (the crowd beats the average individual by exactly the diversity).
* `diversity_nonneg`, `diversity_eq_zero_iff`: auxiliary facts on the diversity term.

INTERPRETED:
* "Crowd error" is `(m - θ)^2`, "average individual error" is `(1/N) * Σ (g i - θ)^2`,
  "diversity" is `(1/N) * Σ (g i - m)^2`, all with `1/N` as a real number `1 / (N : ℝ)`.
* "All guesses are equal" is `∀ i j, g i = g j`.
* The hypothesis `N ≥ 1` is `hN : 1 ≤ N`. It is necessary: for `N = 0` Lean's
  `1 / 0 = 0` gives `m = 0`, so the identity would read `θ^2 = 0`.
-/

namespace DiversityPredictionB

open Finset

/-- Crowd mean. -/
noncomputable def mean {N : ℕ} (g : Fin N → ℝ) : ℝ := (1 / (N : ℝ)) * ∑ i, g i

/-- Average individual squared error. -/
noncomputable def avgErr {N : ℕ} (g : Fin N → ℝ) (θ : ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, (g i - θ) ^ 2

/-- Diversity: average squared deviation from the crowd mean. -/
noncomputable def diversity {N : ℕ} (g : Fin N → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, (g i - mean g) ^ 2

lemma sum_sub_mean {N : ℕ} (hN : 1 ≤ N) (g : Fin N → ℝ) :
    ∑ i, (g i - mean g) = 0 := by
  have hN' : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mean]
  field_simp
  ring

/-- Scott Page's diversity prediction theorem (exact identity). -/
theorem diversity_prediction {N : ℕ} (hN : 1 ≤ N) (g : Fin N → ℝ) (θ : ℝ) :
    (mean g - θ) ^ 2 =
      (1 / (N : ℝ)) * ∑ i, (g i - θ) ^ 2 - (1 / (N : ℝ)) * ∑ i, (g i - mean g) ^ 2 := by
  have hN' : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have h0 := sum_sub_mean hN g
  have hexp : ∑ i, (g i - θ) ^ 2 =
      ∑ i, (g i - mean g) ^ 2 + 2 * (mean g - θ) * ∑ i, (g i - mean g)
        + (N : ℝ) * (mean g - θ) ^ 2 := by
    have : ∀ i, (g i - θ) ^ 2 =
        (g i - mean g) ^ 2 + 2 * (mean g - θ) * (g i - mean g) + (mean g - θ) ^ 2 := by
      intro i; ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hexp, h0]
  field_simp
  ring

theorem diversity_nonneg {N : ℕ} (g : Fin N → ℝ) : 0 ≤ diversity g := by
  unfold diversity
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem diversity_eq_zero_iff {N : ℕ} (hN : 1 ≤ N) (g : Fin N → ℝ) :
    diversity g = 0 ↔ ∀ i j, g i = g j := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold diversity
  constructor
  · intro h
    have hs : ∑ i, (g i - mean g) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h with h1 | h1
      · exfalso
        have : (0 : ℝ) < 1 / (N : ℝ) := by positivity
        linarith
      · exact h1
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (g i - mean g))).mp hs
    intro i j
    have hi := hall i (Finset.mem_univ _)
    have hj := hall j (Finset.mem_univ _)
    have hi' : g i - mean g = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hi
    have hj' : g j - mean g = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hj
    linarith
  · intro h
    have i0 : Fin N := ⟨0, hN⟩
    have hm : mean g = g i0 := by
      unfold mean
      have : ∑ i, g i = ∑ _i : Fin N, g i0 := Finset.sum_congr rfl (fun i _ => h i i0)
      rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have : ∀ i, (g i - mean g) ^ 2 = 0 := by
      intro i; rw [hm, h i i0]; ring
    simp [this]

/-- Corollary (1): the crowd is never worse than the average individual. -/
theorem crowd_le_avg {N : ℕ} (hN : 1 ≤ N) (g : Fin N → ℝ) (θ : ℝ) :
    (mean g - θ) ^ 2 ≤ (1 / (N : ℝ)) * ∑ i, (g i - θ) ^ 2 := by
  have h := diversity_prediction hN g θ
  have hd := diversity_nonneg g
  unfold diversity at hd
  linarith

/-- Corollary (2): equality iff all guesses are equal. -/
theorem crowd_eq_avg_iff {N : ℕ} (hN : 1 ≤ N) (g : Fin N → ℝ) (θ : ℝ) :
    (mean g - θ) ^ 2 = (1 / (N : ℝ)) * ∑ i, (g i - θ) ^ 2 ↔ ∀ i j, g i = g j := by
  rw [← diversity_eq_zero_iff hN g]
  have h := diversity_prediction hN g θ
  unfold diversity
  constructor <;> intro h' <;> linarith

/-- Corollary (3): the crowd beats the average individual by exactly the diversity. -/
theorem avg_sub_crowd {N : ℕ} (hN : 1 ≤ N) (g : Fin N → ℝ) (θ : ℝ) :
    (1 / (N : ℝ)) * ∑ i, (g i - θ) ^ 2 - (mean g - θ) ^ 2 =
      (1 / (N : ℝ)) * ∑ i, (g i - mean g) ^ 2 := by
  have h := diversity_prediction hN g θ
  linarith

/-- Corollary (3) phrased with the named quantities. -/
theorem avgErr_sub_crowd_eq_diversity {N : ℕ} (hN : 1 ≤ N) (g : Fin N → ℝ) (θ : ℝ) :
    avgErr g θ - (mean g - θ) ^ 2 = diversity g :=
  avg_sub_crowd hN g θ

end DiversityPredictionB
