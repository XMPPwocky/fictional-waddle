import Mathlib

/-!
# Molar versus molecular

PROVED
* `mean_not_injective`: for `N ≥ 2` the mean `Fin N → ℝ → ℝ` is not injective; the explicit
  witnesses are `0` and `Pi.single 0 1 - Pi.single 1 1`, which differ but both have mean `0`.
* `diagCov_double_sum`: `Σ_j Σ_k Cov(j,k) = N · σ²` when `Cov(j,k) = if j = k then σ² else 0`.
* `variance_of_mean`: for `N ≠ 0`, `(1/N²) · Σ_j Σ_k Cov(j,k) = σ² / N` for that covariance.
* `variance_of_mean_tendsto_zero`: `N ↦ (1/N²) · Σ_j Σ_k Cov(j,k)` tends to `0` as `N → ∞`
  (as does `N ↦ σ² / N`, `sigmaSq_div_tendsto_zero`).
* `molar_invisible`: for every `ε > 0` there is `N₀` with `σ² / N < ε` for all `N ≥ N₀`.

INTERPRETED (not part of any theorem statement)
* The vector `x : Fin N → ℝ` is the molecular configuration; its mean is the molar aggregate.
  Non-injectivity says the molar description forgets molecular distinctions.
* The covariance algebra is the variance of the mean of `N` uncorrelated molecular quantities of
  common variance `σ²`; no probability space is constructed, only the bilinear algebra
  `Var((1/N) Σ X_j) = (1/N²) Σ_j Σ_k Cov(X_j, X_k)` is taken as given.
* `molar_invisible` reads the Deleuze–Guattari claim that molecular multiplicity is invisible at the
  molar scale as the statement that the molecular spread `σ²` is suppressed below any threshold by
  large-number aggregation.
-/

namespace MolarForgetsMolecularA

open Finset Filter Topology

/-- The molar aggregate: the arithmetic mean of a vector of `N` reals. -/
noncomputable def mean {N : ℕ} (x : Fin N → ℝ) : ℝ := (∑ i, x i) / N

/-- The covariance of `N` uncorrelated quantities with common variance `σ²`. -/
def diagCov (N : ℕ) (σsq : ℝ) (j k : Fin N) : ℝ := if j = k then σsq else 0

/-- (1) Two different explicit molecular configurations with the same mean. -/
theorem mean_not_injective (N : ℕ) (hN : 2 ≤ N) :
    let i₀ : Fin N := ⟨0, by omega⟩
    let i₁ : Fin N := ⟨1, by omega⟩
    (0 : Fin N → ℝ) ≠ (Pi.single i₀ 1 - Pi.single i₁ 1) ∧
      mean (0 : Fin N → ℝ) = mean (Pi.single i₀ (1 : ℝ) - Pi.single i₁ 1) ∧
      ¬ Function.Injective (mean (N := N)) := by
  intro i₀ i₁
  have hne : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    simp [i₀, i₁] at this
  have hdiff : (0 : Fin N → ℝ) ≠ (Pi.single i₀ 1 - Pi.single i₁ 1) := by
    intro h
    have := congrFun h i₀
    simp [hne] at this
  have hmean : mean (0 : Fin N → ℝ) = mean (Pi.single i₀ (1 : ℝ) - Pi.single i₁ 1) := by
    unfold mean
    simp [Finset.sum_sub_distrib]
  exact ⟨hdiff, hmean, fun hinj => hdiff (hinj hmean)⟩

/-- The double sum of the diagonal covariance. -/
theorem diagCov_double_sum (N : ℕ) (σsq : ℝ) :
    ∑ j : Fin N, ∑ k : Fin N, diagCov N σsq j k = N * σsq := by
  unfold diagCov
  simp [Finset.sum_ite_eq]

/-- (2) The variance of the mean of `N` uncorrelated quantities of common variance `σ²`. -/
theorem variance_of_mean (N : ℕ) (hN : N ≠ 0) (σsq : ℝ) :
    (1 / (N : ℝ) ^ 2) * ∑ j : Fin N, ∑ k : Fin N, diagCov N σsq j k = σsq / N := by
  rw [diagCov_double_sum]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  field_simp

theorem sigmaSq_div_tendsto_zero (σsq : ℝ) :
    Tendsto (fun N : ℕ => σsq / (N : ℝ)) atTop (𝓝 0) :=
  tendsto_const_div_atTop_nhds_zero_nat σsq

/-- (2) The variance of the mean tends to `0` as `N → ∞`. -/
theorem variance_of_mean_tendsto_zero (σsq : ℝ) :
    Tendsto (fun N : ℕ => (1 / (N : ℝ) ^ 2) * ∑ j : Fin N, ∑ k : Fin N, diagCov N σsq j k)
      atTop (𝓝 0) := by
  refine (sigmaSq_div_tendsto_zero σsq).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (variance_of_mean N (by omega) σsq).symm

/-- (3) The molecular spread is below any threshold at a large enough molar scale. -/
theorem molar_invisible (σsq : ℝ) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, σsq / (N : ℝ) < ε := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (sigmaSq_div_tendsto_zero σsq) ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have := hN₀ N hN
  rw [Real.dist_eq, sub_zero] at this
  exact lt_of_le_of_lt (le_abs_self _) this

end MolarForgetsMolecularA
