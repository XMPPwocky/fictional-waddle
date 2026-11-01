import Mathlib

/-!
# Molar versus molecular

PROVED:
* `mean_not_injective`: for `N ≥ 2`, the mean `Fin N → ℝ → ℝ` is not injective; the explicit
  witnesses `indicatorAt 0` and `indicatorAt 1` (standard basis vectors) are different and both
  have mean `1 / N`.
* `var_mean_uncorrelated`: for every `N : ℕ` and `σ : ℝ`,
  `(1 / N²) · Σ_j Σ_k (if j = k then σ² else 0) = σ² / N`.
* `var_mean_tendsto_zero`: the left-hand side above tends to `0` as `N → ∞`.
* `spread_invisible`: for every `ε > 0` there is `N₀` with `σ² / N < ε` for all `N ≥ N₀`.

The variance statement is the algebraic identity for the covariance matrix
`Cov(j,k) = if j = k then σ² else 0` of `N` uncorrelated quantities with common variance `σ²`,
using `Var((1/N) Σ X_j) = (1/N²) Σ_j Σ_k Cov(j,k)`; that bilinearity step is not formalized here.

INTERPRETED (Deleuze–Guattari reading, not part of any theorem claim):
* The mean is a molar aggregate: distinct molecular configurations collapse to one molar value,
  so the molar statistic cannot recover the molecular multiplicity (part 1).
* Molecular fluctuation is real at each component (variance `σ²`) but its trace in the molar
  aggregate decays like `σ² / N` and vanishes in the large-number limit (parts 2 and 3).
-/

namespace MolarForgetsMolecularB

open Filter Topology

/-- The mean of `N` real numbers. -/
noncomputable def mean (N : ℕ) (v : Fin N → ℝ) : ℝ := (∑ i, v i) / N

/-- The standard basis vector at index `a`. -/
noncomputable def indicatorAt {N : ℕ} (a : Fin N) : Fin N → ℝ := fun i => if i = a then 1 else 0

lemma mean_indicatorAt {N : ℕ} (a : Fin N) : mean N (indicatorAt a) = 1 / N := by
  simp [mean, indicatorAt]

/-- (1) Explicit witnesses: two different vectors with the same mean. -/
theorem mean_collision (N : ℕ) (hN : 2 ≤ N) :
    indicatorAt (⟨0, by omega⟩ : Fin N) ≠ indicatorAt (⟨1, by omega⟩ : Fin N) ∧
    mean N (indicatorAt (⟨0, by omega⟩ : Fin N)) = mean N (indicatorAt (⟨1, by omega⟩ : Fin N)) := by
  refine ⟨?_, by rw [mean_indicatorAt, mean_indicatorAt]⟩
  intro h
  have := congrFun h ⟨0, by omega⟩
  simp [indicatorAt, Fin.ext_iff] at this

/-- (1) The mean is not injective for `N ≥ 2`. -/
theorem mean_not_injective (N : ℕ) (hN : 2 ≤ N) : ¬ Function.Injective (mean N) := by
  intro hinj
  obtain ⟨hne, heq⟩ := mean_collision N hN
  exact hne (hinj heq)

/-- The covariance matrix of `N` uncorrelated quantities with common variance `σ²`. -/
noncomputable def uncorrCov (N : ℕ) (σ : ℝ) : Fin N → Fin N → ℝ :=
  fun j k => if j = k then σ ^ 2 else 0

/-- The variance of the mean, written in terms of the covariance matrix. -/
noncomputable def varMean (N : ℕ) (C : Fin N → Fin N → ℝ) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ j, ∑ k, C j k

/-- (2) `(1/N²) Σ_j Σ_k Cov(j,k) = σ²/N` for uncorrelated quantities of common variance `σ²`. -/
theorem var_mean_uncorrelated (N : ℕ) (σ : ℝ) : varMean N (uncorrCov N σ) = σ ^ 2 / N := by
  unfold varMean uncorrCov
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have : (N : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    field_simp

/-- (2) The variance of the mean tends to `0` as `N → ∞`. -/
theorem var_mean_tendsto_zero (σ : ℝ) :
    Tendsto (fun N : ℕ => varMean N (uncorrCov N σ)) atTop (𝓝 0) := by
  simp only [var_mean_uncorrelated]
  exact tendsto_const_div_atTop_nhds_zero_nat (σ ^ 2)

/-- (3) The molecular spread is invisible at the molar scale. -/
theorem spread_invisible (σ : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, σ ^ 2 / N < ε := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat (σ ^ 2)).eventually (gt_mem_nhds hε)
  exact eventually_atTop.mp h

end MolarForgetsMolecularB
