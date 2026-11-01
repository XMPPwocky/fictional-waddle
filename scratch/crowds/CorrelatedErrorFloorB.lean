import Mathlib

/-!
# Correlated error floor for crowd averaging

Model: `N` guesses `g i = θ + b + e i` with shared bias `b` and errors `e i` of mean `0`,
common variance `σ²` and pairwise covariance `ρσ²` (`i ≠ j`). The covariance matrix is
`corrCov N σ ρ i j = if i = j then σ² else ρσ²`, and the mean squared error of the crowd mean is
`crowdMSE N b σ ρ = b² + (1/N²) Σ_i Σ_j corrCov N σ ρ i j`.

PROVED
* `sq_mean_error_expand`: pointwise, `(mean g - θ)² = b² + 2b·(mean e) + (1/N²) Σ_i Σ_j e_i e_j`
  (the algebra that, after taking expectations with `E e_i = 0`, `E e_i e_j = C i j`, gives the
  definition of `crowdMSE`).
* `sum_corrCov`: `Σ_i Σ_j C i j = N σ² + N(N-1) ρσ²`.
* `crowdMSE_eq` (N ≥ 1): `crowdMSE = b² + σ²(ρ + (1-ρ)/N)`.
* `crowdMSE_indep` (ρ = 0, b = 0, N ≥ 1): `crowdMSE = σ²/N`, and `crowdMSE_indep_tendsto`: it tends to 0.
* `crowdMSE_floor` (N ≥ 1, ρ ≤ 1): `b² + ρσ² ≤ crowdMSE`.
* `quadForm_corrCov`: `xᵀ C x = ρσ² (Σ x)² + (σ² - ρσ²) Σ x²`.
* `crowdMSE_floor_of_psd` (N ≥ 2, C positive semidefinite as a quadratic form): same bound,
  with `ρσ² ≤ σ²` derived from positive semidefiniteness instead of assumed.
* `crowdMSE_floor_fails` : without `ρ ≤ 1` the floor is false (N = 1, ρ = 2, σ = 1, b = 0).
* `crowdMSE_tendsto`: as `N → ∞`, `crowdMSE → b² + ρσ²` (no hypothesis on ρ).

INTERPRETED
* The mean squared error is taken, as stated, to be the algebraic expression
  `b² + (1/N²) Σ Σ C i j`; no probability space is formalized.
* "Pairwise correlation ρ" is read as `ρ ≤ 1` (true of any correlation coefficient) for the floor;
  `N ≥ 1` (at least one guess) is required, since for `N = 0` the formula has a division by zero.
-/

namespace CorrelatedErrorFloorB

open Finset Filter Topology

/-- Covariance matrix with variance `σ²` on the diagonal and covariance `ρσ²` off it. -/
def corrCov (N : ℕ) (σ ρ : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i = j then σ ^ 2 else ρ * σ ^ 2

/-- Mean squared error of the crowd mean: squared shared bias plus variance of the mean error. -/
noncomputable def crowdMSE (N : ℕ) (b σ ρ : ℝ) : ℝ :=
  b ^ 2 + (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j, corrCov N σ ρ i j

/-- Pointwise expansion of the squared error of the crowd mean of `g i = θ + b + e i`. -/
theorem sq_mean_error_expand (N : ℕ) (hN : 1 ≤ N) (θ b : ℝ) (e : Fin N → ℝ) :
    ((1 / (N : ℝ)) * ∑ i, (θ + b + e i) - θ) ^ 2
      = b ^ 2 + 2 * b * ((1 / (N : ℝ)) * ∑ i, e i)
          + (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j, e i * e j := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have h1 : ∑ i : Fin N, (θ + b + e i) = (N : ℝ) * (θ + b) + ∑ i, e i := by
    rw [Finset.sum_add_distrib]; simp; ring
  have h2 : ∑ i : Fin N, ∑ j : Fin N, e i * e j = (∑ i, e i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  rw [h1, h2]
  field_simp
  ring

theorem sum_corrCov (N : ℕ) (σ ρ : ℝ) :
    ∑ i, ∑ j, corrCov N σ ρ i j = (N : ℝ) * σ ^ 2 + (N : ℝ) * ((N : ℝ) - 1) * (ρ * σ ^ 2) := by
  have hrow : ∀ i : Fin N, ∑ j, corrCov N σ ρ i j = σ ^ 2 + ((N : ℝ) - 1) * (ρ * σ ^ 2) := by
    intro i
    have : ∀ j : Fin N, corrCov N σ ρ i j
        = ρ * σ ^ 2 + (if i = j then σ ^ 2 - ρ * σ ^ 2 else 0) := by
      intro j; unfold corrCov; split_ifs <;> ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The identity `MSE = b² + σ²(ρ + (1-ρ)/N)`. -/
theorem crowdMSE_eq (N : ℕ) (hN : 1 ≤ N) (b σ ρ : ℝ) :
    crowdMSE N b σ ρ = b ^ 2 + σ ^ 2 * (ρ + (1 - ρ) / (N : ℝ)) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  unfold crowdMSE
  rw [sum_corrCov]
  field_simp
  ring

/-- (1) Independent, unbiased errors: `MSE = σ²/N`. -/
theorem crowdMSE_indep (N : ℕ) (hN : 1 ≤ N) (σ : ℝ) :
    crowdMSE N 0 σ 0 = σ ^ 2 / (N : ℝ) := by
  rw [crowdMSE_eq N hN]
  ring

/-- (1) Independent, unbiased errors: `MSE → 0` as `N → ∞`. -/
theorem crowdMSE_indep_tendsto (σ : ℝ) :
    Tendsto (fun N : ℕ => crowdMSE N 0 σ 0) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => σ ^ 2 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (σ ^ 2)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (crowdMSE_indep N hN σ).symm

/-- (2) The shared part never averages out: `b² + ρσ² ≤ MSE` for every `N ≥ 1`, when `ρ ≤ 1`. -/
theorem crowdMSE_floor (N : ℕ) (hN : 1 ≤ N) (b σ ρ : ℝ) (hρ : ρ ≤ 1) :
    b ^ 2 + ρ * σ ^ 2 ≤ crowdMSE N b σ ρ := by
  rw [crowdMSE_eq N hN]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have : 0 ≤ σ ^ 2 * ((1 - ρ) / (N : ℝ)) :=
    mul_nonneg (sq_nonneg σ) (div_nonneg (by linarith) hNpos.le)
  nlinarith [this]

/-- Quadratic form of `C`: `xᵀ C x = ρσ² (Σ x)² + (σ² - ρσ²) Σ x²`. -/
theorem quadForm_corrCov (N : ℕ) (σ ρ : ℝ) (x : Fin N → ℝ) :
    ∑ i, ∑ j, x i * corrCov N σ ρ i j * x j
      = ρ * σ ^ 2 * (∑ i, x i) ^ 2 + (σ ^ 2 - ρ * σ ^ 2) * ∑ i, x i ^ 2 := by
  have h : ∀ i j : Fin N, x i * corrCov N σ ρ i j * x j
      = ρ * σ ^ 2 * (x i * x j) + (if i = j then (σ ^ 2 - ρ * σ ^ 2) * (x i * x j) else 0) := by
    intro i j; unfold corrCov; split_ifs <;> ring
  have hs : (∑ i, x i) ^ 2 = ∑ i, ∑ j, x i * x j := by rw [sq, Finset.sum_mul_sum]
  have hd : ∀ i, x i ^ 2 = x i * x i := fun i => sq (x i)
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    ← Finset.mul_sum, hs, hd]

/-- (2) Variant: for `N ≥ 2`, if `C` is positive semidefinite (a genuine covariance matrix),
the floor holds with no separate assumption on `ρ`. -/
theorem crowdMSE_floor_of_psd (N : ℕ) (hN : 2 ≤ N) (b σ ρ : ℝ)
    (hpsd : ∀ x : Fin N → ℝ, 0 ≤ ∑ i, ∑ j, x i * corrCov N σ ρ i j * x j) :
    b ^ 2 + ρ * σ ^ 2 ≤ crowdMSE N b σ ρ := by
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  let x : Fin N → ℝ := Pi.single i0 (1 : ℝ) - Pi.single i1 (1 : ℝ)
  have hsum : ∑ i, x i = 0 := by
    simp [x, Finset.sum_sub_distrib]
  have hsq : ∀ i, x i ^ 2 = (Pi.single i0 (1 : ℝ) : Fin N → ℝ) i + (Pi.single i1 (1 : ℝ) : Fin N → ℝ) i := by
    intro i
    simp only [x, Pi.sub_apply]
    by_cases h0 : i = i0
    · subst h0; simp [hne]
    · by_cases h1 : i = i1
      · subst h1; simp [h0]
      · simp [h0, h1]
  have hsum2 : ∑ i, x i ^ 2 = 2 := by
    simp only [hsq, Finset.sum_add_distrib]
    simp; norm_num
  have hq := hpsd x
  rw [quadForm_corrCov, hsum, hsum2] at hq
  have hkey : 0 ≤ σ ^ 2 * (1 - ρ) := by nlinarith [hq]
  rw [crowdMSE_eq N (by omega)]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have : 0 ≤ σ ^ 2 * ((1 - ρ) / (N : ℝ)) := by
    rw [← mul_div_assoc]; exact div_nonneg hkey hNpos.le
  nlinarith [this]

/-- Without `ρ ≤ 1` the floor fails: `N = 1`, `b = 0`, `σ = 1`, `ρ = 2`. -/
theorem crowdMSE_floor_fails :
    ¬ ((0 : ℝ) ^ 2 + 2 * 1 ^ 2 ≤ crowdMSE 1 0 1 2) := by
  rw [crowdMSE_eq 1 le_rfl]
  norm_num

/-- (3) As `N → ∞`, `MSE → b² + ρσ²`. -/
theorem crowdMSE_tendsto (b σ ρ : ℝ) :
    Tendsto (fun N : ℕ => crowdMSE N b σ ρ) atTop (𝓝 (b ^ 2 + ρ * σ ^ 2)) := by
  have h0 : Tendsto (fun N : ℕ => (1 - ρ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (1 - ρ)
  have h : Tendsto (fun N : ℕ => b ^ 2 + σ ^ 2 * (ρ + (1 - ρ) / (N : ℝ))) atTop
      (𝓝 (b ^ 2 + σ ^ 2 * (ρ + 0))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_const_nhds.add h0))
  have hlim : b ^ 2 + σ ^ 2 * (ρ + 0) = b ^ 2 + ρ * σ ^ 2 := by ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (crowdMSE_eq N hN b σ ρ).symm

end CorrelatedErrorFloorB
