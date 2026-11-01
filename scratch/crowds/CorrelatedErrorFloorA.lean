import Mathlib

/-!
# Correlated error floor for the wisdom of crowds

Model: `N` guesses `g i = θ + b + e i` with shared bias `b` and errors `e i` having mean zero,
common variance `σ²` and pairwise correlation `ρ`.  The error covariance matrix is
`C i i = σ²`, `C i j = ρ σ²` for `i ≠ j` (`equicorrC`).

PROVED
* `mse_crowd_mean_eq` : (probabilistic derivation, any covariance matrix `C`) if the `e i` are in
  `L²` of a probability measure, have mean zero and `E[e i * e j] = C i j`, then
  `E[(mean g - θ)²] = b² + (1/N²) Σ_i Σ_j C i j`.  This is `crowdMSE b C`.
* `sum_equicorrC` : `Σ_i Σ_j C i j = N σ² + N (N - 1) ρ σ²`.
* `crowdMSE_equicorr` : for `N > 0`, `crowdMSE b C = b² + σ² (ρ + (1 - ρ)/N)`.
* `crowdMSE_indep_unbiased` : with `ρ = 0`, `b = 0` it equals `σ²/N`.
* `tendsto_crowdMSE_indep_unbiased` : with `ρ = 0`, `b = 0` it tends to `0` as `N → ∞`.
* `crowdMSE_ge_floor` : for `ρ ≤ 1` and every `N > 0`, `crowdMSE ≥ b² + ρ σ²`.
* `crowdMSE_ge_floor_of_psd` : the same floor for `N ≥ 2` with the hypothesis `ρ ≤ 1` replaced by
  positive semidefiniteness of `C` (which every covariance matrix satisfies).
* `not_floor_of_one_lt_rho` : the floor fails for `ρ > 1`, `σ ≠ 0` (e.g. at `N = 1`), so the
  correlation bound `ρ ≤ 1` cannot be dropped for an arbitrary real parameter `ρ`.
* `tendsto_crowdMSE_floor` : as `N → ∞`, `crowdMSE → b² + ρ σ²` (no hypothesis on `ρ`).

INTERPRETED
* "Mean squared error of the crowd mean" is the algebraic quantity `crowdMSE b C`
  `= b² + (1/N²) Σ_i Σ_j C i j`; `mse_crowd_mean_eq` shows it is the expectation
  `E[((1/N) Σ_i g i - θ)²]` under the stated moment assumptions.
* "Correlation `ρ`" carries the constraint `ρ ≤ 1`, used for the floor (2); alternatively the
  PSD form of a covariance matrix is assumed.
* Limits are along `N : ℕ` in `Filter.atTop`, with the matrix `equicorrC N σ ρ` at each `N`.
-/

namespace CorrelatedErrorFloorA

open MeasureTheory Filter Topology Finset

/-- The equicorrelated covariance matrix: `σ²` on the diagonal, `ρ σ²` off it. -/
def equicorrC (N : ℕ) (σ ρ : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i = j then σ ^ 2 else ρ * σ ^ 2

/-- Mean squared error of the crowd mean, written via the error covariance matrix. -/
noncomputable def crowdMSE {N : ℕ} (b : ℝ) (C : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  b ^ 2 + (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j, C i j

/-- Derivation: the expected squared error of the averaged guess `θ + b + e i` equals
`crowdMSE b C` when the errors are centred, square integrable, with second moments `C`. -/
theorem mse_crowd_mean_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N) (θ b : ℝ) (e : Fin N → Ω → ℝ)
    (C : Matrix (Fin N) (Fin N) ℝ)
    (he : ∀ i, MemLp (e i) 2 μ) (hmean : ∀ i, ∫ ω, e i ω ∂μ = 0)
    (hcov : ∀ i j, ∫ ω, e i ω * e j ω ∂μ = C i j) :
    ∫ ω, ((1 / (N : ℝ)) * ∑ i, (θ + b + e i ω) - θ) ^ 2 ∂μ = crowdMSE b C := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpt : ∀ ω, ((1 / (N : ℝ)) * ∑ i, (θ + b + e i ω) - θ) ^ 2
      = b ^ 2 + (2 * b / N) * ∑ i, e i ω + (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j, e i ω * e j ω := by
    intro ω
    have h1 : ∑ i, (θ + b + e i ω) = N * (θ + b) + ∑ i, e i ω := by
      rw [Finset.sum_add_distrib]; simp; ring
    have h2 : ∑ i, ∑ j, e i ω * e j ω = (∑ i, e i ω) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
    rw [h1, h2]
    field_simp
    ring
  have hint1 : ∀ i, Integrable (e i) μ := fun i => (he i).integrable one_le_two
  have hint2 : ∀ i j, Integrable (fun ω => e i ω * e j ω) μ :=
    fun i j => (he i).integrable_mul (he j)
  simp_rw [hpt]
  rw [integral_add, integral_add, integral_const, integral_const_mul, integral_const_mul,
    integral_finsetSum, integral_finsetSum]
  · simp only [hmean, Finset.sum_const_zero, mul_zero, add_zero, probReal_univ, smul_eq_mul,
      one_mul, crowdMSE]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum]
    · simp [hcov]
    · intro j _; exact hint2 i j
  · intro i _; exact integrable_finsetSum _ fun j _ => hint2 i j
  · intro i _; exact hint1 i
  · exact integrable_const _
  · exact (integrable_finsetSum _ fun i _ => hint1 i).const_mul _
  · exact (integrable_const _).add ((integrable_finsetSum _ fun i _ => hint1 i).const_mul _)
  · exact (integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hint2 i j).const_mul _

/-- Total of the entries of the equicorrelated covariance matrix. -/
theorem sum_equicorrC (N : ℕ) (σ ρ : ℝ) :
    ∑ i, ∑ j, equicorrC N σ ρ i j = N * σ ^ 2 + N * ((N : ℝ) - 1) * (ρ * σ ^ 2) := by
  have hrow : ∀ i : Fin N, ∑ j, equicorrC N σ ρ i j = σ ^ 2 + ((N : ℝ) - 1) * (ρ * σ ^ 2) := by
    intro i
    unfold equicorrC
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [Finset.sum_congr rfl (g := fun _ => ρ * σ ^ 2)]
    · rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rcases Nat.eq_zero_or_pos N with h | h
      · exact absurd i.isLt (by omega)
      · rw [Nat.cast_sub (by omega)]; simp
    · intro j hj
      simp [Ne.symm (Finset.ne_of_mem_erase hj)]
  simp_rw [hrow]
  simp
  ring

/-- The identity: `crowdMSE = b² + σ² (ρ + (1 - ρ)/N)`. -/
theorem crowdMSE_equicorr {N : ℕ} (hN : 0 < N) (b σ ρ : ℝ) :
    crowdMSE b (equicorrC N σ ρ) = b ^ 2 + σ ^ 2 * (ρ + (1 - ρ) / N) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold crowdMSE
  rw [sum_equicorrC]
  field_simp
  ring

/-- (1) Independent, unbiased errors: the crowd MSE is `σ²/N`. -/
theorem crowdMSE_indep_unbiased {N : ℕ} (hN : 0 < N) (σ : ℝ) :
    crowdMSE 0 (equicorrC N σ 0) = σ ^ 2 / N := by
  rw [crowdMSE_equicorr hN]; ring

/-- (1) Independent, unbiased errors: the crowd MSE tends to `0`. -/
theorem tendsto_crowdMSE_indep_unbiased (σ : ℝ) :
    Tendsto (fun N : ℕ => crowdMSE 0 (equicorrC N σ 0)) atTop (𝓝 0) := by
  have h : ∀ᶠ N : ℕ in atTop, σ ^ 2 / (N : ℝ) = crowdMSE 0 (equicorrC N σ 0) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [crowdMSE_indep_unbiased hN]
  refine Tendsto.congr' h ?_
  simpa using tendsto_const_div_atTop_nhds_zero_nat (σ ^ 2)

/-- (2) The shared part never averages out: for a correlation `ρ ≤ 1`, every crowd size has
MSE at least `b² + ρ σ²`. -/
theorem crowdMSE_ge_floor {N : ℕ} (hN : 0 < N) (b σ ρ : ℝ) (hρ : ρ ≤ 1) :
    b ^ 2 + ρ * σ ^ 2 ≤ crowdMSE b (equicorrC N σ ρ) := by
  rw [crowdMSE_equicorr hN]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have : 0 ≤ σ ^ 2 * ((1 - ρ) / N) :=
    mul_nonneg (sq_nonneg σ) (div_nonneg (by linarith) hNr.le)
  nlinarith

/-- (2) with positive semidefiniteness of `C` in place of `ρ ≤ 1` (needs two guessers). -/
theorem crowdMSE_ge_floor_of_psd {N : ℕ} (hN : 2 ≤ N) (b σ ρ : ℝ)
    (hpsd : ∀ x : Fin N → ℝ, 0 ≤ ∑ i, ∑ j, x i * equicorrC N σ ρ i j * x j) :
    b ^ 2 + ρ * σ ^ 2 ≤ crowdMSE b (equicorrC N σ ρ) := by
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  let x : Fin N → ℝ := fun k => if k = i0 then 1 else if k = i1 then -1 else 0
  have hx := hpsd x
  have hq : ∑ i, ∑ j, x i * equicorrC N σ ρ i j * x j = 2 * σ ^ 2 - 2 * (ρ * σ ^ 2) := by
    have hrow : ∀ i, ∑ j, x i * equicorrC N σ ρ i j * x j
        = x i * equicorrC N σ ρ i i0 - x i * equicorrC N σ ρ i i1 := by
      intro i
      rw [Finset.sum_eq_add_of_mem i0 i1 (Finset.mem_univ _) (Finset.mem_univ _) h01]
      · simp [x, h01.symm]; ring
      · intro k _ hk
        simp [x, hk.1, hk.2]
    simp_rw [hrow]
    rw [Finset.sum_sub_distrib,
      Finset.sum_eq_add_of_mem i0 i1 (Finset.mem_univ _) (Finset.mem_univ _) h01,
      Finset.sum_eq_add_of_mem i0 i1 (Finset.mem_univ _) (Finset.mem_univ _) h01]
    · simp [x, equicorrC, h01, h01.symm]; ring
    · intro k _ hk; simp [x, hk.1, hk.2]
    · intro k _ hk; simp [x, hk.1, hk.2]
  rw [hq] at hx
  rw [crowdMSE_equicorr (by omega)]
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 : 0 ≤ σ ^ 2 * (1 - ρ) := by nlinarith
  have : 0 ≤ σ ^ 2 * ((1 - ρ) / N) := by
    rw [← mul_div_assoc]; exact div_nonneg h1 hNr.le
  nlinarith

/-- The bound `ρ ≤ 1` is needed: for `ρ > 1` and `σ ≠ 0` the floor fails at `N = 1`. -/
theorem not_floor_of_one_lt_rho (b σ ρ : ℝ) (hρ : 1 < ρ) (hσ : σ ≠ 0) :
    crowdMSE b (equicorrC 1 σ ρ) < b ^ 2 + ρ * σ ^ 2 := by
  rw [crowdMSE_equicorr one_pos]
  have : 0 < σ ^ 2 := by positivity
  push_cast
  nlinarith

/-- (3) As the crowd grows, the MSE tends to the floor `b² + ρ σ²`. -/
theorem tendsto_crowdMSE_floor (b σ ρ : ℝ) :
    Tendsto (fun N : ℕ => crowdMSE b (equicorrC N σ ρ)) atTop (𝓝 (b ^ 2 + ρ * σ ^ 2)) := by
  have h : ∀ᶠ N : ℕ in atTop,
      b ^ 2 + σ ^ 2 * (ρ + (1 - ρ) / N) = crowdMSE b (equicorrC N σ ρ) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [crowdMSE_equicorr hN]
  refine Tendsto.congr' h ?_
  have h0 : Tendsto (fun N : ℕ => (1 - ρ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (1 - ρ)
  have := ((h0.const_add ρ).const_mul (σ ^ 2)).const_add (b ^ 2)
  simpa [mul_comm] using this

end CorrelatedErrorFloorA
