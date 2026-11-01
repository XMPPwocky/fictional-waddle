import Mathlib

/-!
# U5: a loop closed on itself collapses; an open loop does not

## Model (interpreted, not derived here)

Refit a Gaussian by maximum likelihood on `n` samples, a fraction `ρ ∈ [0,1]` of which are fresh
world data (variance `s > 0`) and the rest drawn from the current model (variance `v_t`). The MLE
variance is the biased sample variance `(1/n) Σ (X_i - X̄)^2`, whose expectation carries the factor
`c = (n-1)/n ∈ (0,1)` (needs `n ≥ 2`). This gives the expected-variance recursion
`v_{t+1} = c * ((1 - ρ) * v_t + ρ * s)`, the mechanism behind model collapse in
Shumailov et al., "AI models collapse when trained on recursively generated data", Nature 2024.
The passage from the sampling process to this deterministic recursion is CITED, not formalized; see
"What is not proved" below.

## Proved (main, about the recursion `v` as a real sequence)

* `closed_loop_formula`, `closed_loop_collapse`: with `ρ = 0`, `v_t = c^t v₀ → 0`.
* `vStar_pos`, `vStar_isFixed`, `fixed_unique`: for `ρ > 0` the map has the unique fixed point
  `v* = c ρ s / (1 - c (1 - ρ)) > 0`. (`fixed_unique`, `vStar_isFixed` hold for `ρ ≥ 0`.)
* `error_formula`, `open_loop_converges`, `open_loop_no_collapse`: `v_t - v* = (c(1-ρ))^t (v₀ - v*)`,
  so `v_t → v* > 0` from every `v₀` (any real `v₀`, not only `v₀ ≥ 0`).
* `vStar_strictMonoOn`: `v*` is strictly increasing in `ρ` on `[0,1]` (from `v*(0) = 0`).

## Proved (optional, Mathlib probability: one refit step)

* `sample_variance_bias`: for pairwise-independent `L²` real random variables `X_1..X_n` with a
  common mean and common variance `σ²`, `E[(1/n) Σ (X_i - X̄)^2] = (n-1)/n σ²`. No Gaussianity and
  no identical distribution needed: only equal means, equal variances, pairwise independence.
* `sample_variance_bias_hetero`: same with variances `σ²_i`: the result is `(n-1)/n · mean_i σ²_i`.
* `refit_step`: if the samples in `F` have variance `s` (fresh) and the others variance `w` (model),
  all with one common mean, then the expected refit variance is exactly
  `c * ((1 - ρ) w + ρ s)` with `ρ = |F|/n`, `c = (n-1)/n`: the recursion's right-hand side.
* `sample_variance_bias_means` (added by the second, adversarial pass): with means `μ_i` that may
  differ, the expected refit variance is `(n-1)/n · mean_i σ²_i + (1/n) Σ (μ_i - μ̄)^2`. The extra
  term is the spread of the means, which is `≥ 0`. So `refit_step`'s right-hand side is a LOWER
  bound when model and world means differ, and equality holds iff all means are equal.

## Concrete instance (proved, by `norm_num`)

`n = 2` (`c = 1/2`), `ρ = 1/2`, `s = 1`: `v* = 1/3`; from `v₀ = 1`, `v₂ = 3/8`; closed loop
`v₃ = 1/8`. The hypotheses of `open_loop_no_collapse` are discharged at these values, so the main
open-loop theorem is not vacuous.

## What is not proved (interpretation)

* Common mean. `refit_step` assumes model and world samples share a mean. In the real process the
  model mean is the previous refit's sample mean and drifts. `sample_variance_bias_means` PROVES the
  one-step consequence: a mean gap adds the nonnegative term `(1/n) Σ (μ_i - μ̄)^2`, so the true step
  is `E[v_{t+1} | model] ≥ c((1-ρ) v_t + ρ s)`. NOT formalized: the comparison argument that a
  sequence obeying this inequality stays above the recursion `v` (the map is increasing since
  `c(1-ρ) ≥ 0`, so this is routine), hence `liminf ≥ v* > 0`. With `ρ = 0` every sample comes from
  the model, the common-mean hypothesis holds automatically, and the closed-loop step is exact.
* From one step to the sequence. `refit_step` is a one-step expectation for a FIXED current model.
  That `E[v_{t+1}] = c((1-ρ)E[v_t] + ρ s)` for the random refit variances follows by the tower
  property and the affinity of the map; this conditioning argument is not formalized.
* Expectation vs. paths. `closed_loop_collapse` says the EXPECTED variance goes to 0. The stronger
  almost-sure collapse of the variance path in Shumailov et al. is not formalized here.
* `ρ` is a real parameter in the recursion; in `refit_step` it is `|F|/n` (a multiple of `1/n`).
-/

namespace U5OpenLoop

open Filter Topology MeasureTheory ProbabilityTheory

/-- The expected-variance recursion `v_{t+1} = c * ((1 - ρ) * v_t + ρ * s)`, started at `v₀`.
`c = (n-1)/n` is the refit bias, `ρ` the fresh-data fraction, `s` the world variance. -/
def v (c ρ s v₀ : ℝ) : ℕ → ℝ
  | 0 => v₀
  | t + 1 => c * ((1 - ρ) * v c ρ s v₀ t + ρ * s)

/-- The candidate fixed point `v* = c ρ s / (1 - c (1 - ρ))`. -/
noncomputable def vStar (c ρ s : ℝ) : ℝ := c * ρ * s / (1 - c * (1 - ρ))

/-- **(1a)** Closed loop (`ρ = 0`): `v_t = c^t v₀`. -/
theorem closed_loop_formula (c s v₀ : ℝ) (t : ℕ) : v c 0 s v₀ t = c ^ t * v₀ := by
  induction t with
  | zero => simp [v]
  | succ t ih => simp only [v, ih]; ring

/-- **(1b)** Closed loop collapses: `v_t → 0`. -/
theorem closed_loop_collapse (c s v₀ : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    Tendsto (v c 0 s v₀) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℕ => c ^ t * v₀) atTop (𝓝 (0 * v₀)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc0.le hc1).mul_const v₀
  rw [zero_mul] at h
  exact h.congr (fun t => (closed_loop_formula c s v₀ t).symm)

/-- Helper (proof file only): the fixed-point denominator is positive. `ρ ≤ 1` is not needed. -/
lemma denom_pos (c ρ : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hρ0 : 0 ≤ ρ) :
    0 < 1 - c * (1 - ρ) := by nlinarith

/-- **(2a)** The open-loop fixed point is strictly positive. (`hρ1` is unused: true for all `ρ > 0`.) -/
theorem vStar_pos (c ρ s : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hs : 0 < s) : 0 < vStar c ρ s := by
  unfold vStar
  exact div_pos (by positivity) (denom_pos c ρ hc0 hc1 hρ0.le)

/-- **(2b)** `v*` is a fixed point of the recursion map. (`hρ1` unused.) -/
theorem vStar_isFixed (c ρ s : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    c * ((1 - ρ) * vStar c ρ s + ρ * s) = vStar c ρ s := by
  have hD := (denom_pos c ρ hc0 hc1 hρ0).ne'
  unfold vStar
  field_simp
  ring

/-- **(2c)** `v*` is the unique fixed point of the recursion map. (`hρ1` unused.) -/
theorem fixed_unique (c ρ s w : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hw : c * ((1 - ρ) * w + ρ * s) = w) : w = vStar c ρ s := by
  have hD := (denom_pos c ρ hc0 hc1 hρ0).ne'
  unfold vStar
  rw [eq_div_iff hD]
  linarith

/-- **(2d)** Exact error: the distance to `v*` contracts by `c (1 - ρ)` per step. -/
theorem error_formula (c ρ s v₀ : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (t : ℕ) : v c ρ s v₀ t - vStar c ρ s = (c * (1 - ρ)) ^ t * (v₀ - vStar c ρ s) := by
  induction t with
  | zero => simp [v]
  | succ t ih =>
    have hfix := vStar_isFixed c ρ s hc0 hc1 hρ0 hρ1
    have step : v c ρ s v₀ (t + 1) - vStar c ρ s
        = c * (1 - ρ) * (v c ρ s v₀ t - vStar c ρ s) := by
      simp only [v]
      linear_combination hfix
    rw [step, ih, pow_succ]
    ring

/-- **(2e)** Open loop converges to `v*` from any start. -/
theorem open_loop_converges (c ρ s v₀ : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) : Tendsto (v c ρ s v₀) atTop (𝓝 (vStar c ρ s)) := by
  have hq0 : 0 ≤ c * (1 - ρ) := mul_nonneg hc0.le (by linarith)
  have hq1 : c * (1 - ρ) < 1 := by nlinarith
  have h : Tendsto (fun t : ℕ => (c * (1 - ρ)) ^ t * (v₀ - vStar c ρ s) + vStar c ρ s) atTop
      (𝓝 (0 * (v₀ - vStar c ρ s) + vStar c ρ s)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const _).add_const _
  rw [zero_mul, zero_add] at h
  refine h.congr (fun t => ?_)
  have := error_formula c ρ s v₀ hc0 hc1 hρ0.le hρ1 t
  linarith

/-- **(2f)** Open loop: positive limit, and convergence to it (2a + 2e). -/
theorem open_loop_no_collapse (c ρ s v₀ : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hs : 0 < s) :
    0 < vStar c ρ s ∧ Tendsto (v c ρ s v₀) atTop (𝓝 (vStar c ρ s)) :=
  ⟨vStar_pos c ρ s hc0 hc1 hρ0 hρ1 hs, open_loop_converges c ρ s v₀ hc0 hc1 hρ0 hρ1⟩

/-- **(3)** `v*` is strictly increasing in the fresh-data fraction `ρ ∈ [0, 1]`. -/
theorem vStar_strictMonoOn (c s : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hs : 0 < s) :
    StrictMonoOn (fun ρ => vStar c ρ s) (Set.Icc 0 1) := by
  intro a ha b hb hab
  simp only [vStar]
  have hDa := denom_pos c a hc0 hc1 ha.1
  have hDb := denom_pos c b hc0 hc1 hb.1
  rw [div_lt_div_iff₀ hDa hDb]
  have key : 0 < c * s * ((b - a) * (1 - c)) :=
    mul_pos (mul_pos hc0 hs) (mul_pos (by linarith) (by linarith))
  nlinarith [key]

/-! ## Optional: the refit bias `c = (n-1)/n` (Mathlib probability) -/

/-- Helper (proof file only): `(1/n) Σ (x_i - x̄)^2 = (1/n) Σ x_i^2 - x̄^2`. -/
lemma sample_var_alg (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) :
    (1 / (n : ℝ)) * ∑ i, (x i - (1 / (n : ℝ)) * ∑ j, x j) ^ 2
      = (1 / (n : ℝ)) * ∑ i, x i ^ 2 - (1 / (n : ℝ)) ^ 2 * (∑ i, x i) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- **(O2, optional)** Expected MLE variance with common mean, unequal variances:
`(n-1)/n` times the average variance. Pairwise independence and `L²` suffice. -/
theorem sample_variance_bias_hetero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (μ : ℝ) (σ2 : Fin n → ℝ)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hind : Pairwise (fun i j => X i ⟂ᵢ[P] X j))
    (hmean : ∀ i, P[X i] = μ) (hvar : ∀ i, Var[X i; P] = σ2 i) :
    ∫ ω, (1 / (n : ℝ)) * ∑ i, (X i ω - (1 / (n : ℝ)) * ∑ j, X j ω) ^ 2 ∂P
      = ((n - 1) / n : ℝ) * ((1 / (n : ℝ)) * ∑ i, σ2 i) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp_rw [sample_var_alg n hn]
  have hSL2 : MemLp (∑ i, X i) 2 P := memLp_finsetSum' _ (fun i _ => hL2 i)
  have hsq : ∀ i, P[X i ^ 2] = σ2 i + μ ^ 2 := by
    intro i; have := variance_eq_sub (hL2 i); rw [hvar i, hmean i] at this; linarith
  have hmeanS : P[∑ i, X i] = n * μ := by
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ (fun i _ => (hL2 i).integrable (by norm_num))]
    simp [hmean]
  have hvarS : Var[∑ i, X i; P] = ∑ i, σ2 i := by
    rw [IndepFun.variance_sum (fun i _ => hL2 i) (fun i _ j _ hij => hind hij)]
    simp [hvar]
  have hsqS : P[(∑ i, X i) ^ 2] = (∑ i, σ2 i) + (n * μ) ^ 2 := by
    have := variance_eq_sub hSL2; rw [hvarS, hmeanS] at this; linarith
  rw [integral_sub, integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun i _ => (hL2 i).integrable_sq)]
  · have e1 : ∀ i, ∫ ω, X i ω ^ 2 ∂P = σ2 i + μ ^ 2 := fun i => hsq i
    have e2 : ∫ ω, (∑ i, X i ω) ^ 2 ∂P = (∑ i, σ2 i) + (n * μ) ^ 2 := by
      rw [← hsqS]; congr 1; ext ω; simp
    rw [e2]
    simp only [e1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    ring
  · exact (integrable_finsetSum _ (fun i _ => (hL2 i).integrable_sq)).const_mul _
  · exact (hSL2.integrable_sq.const_mul ((1 / (n : ℝ)) ^ 2)).congr
      (Eventually.of_forall fun ω => by simp [Finset.sum_apply])

/-- **(O1, optional)** `E[(1/n) Σ (X_i - X̄)^2] = (n-1)/n · σ²` for pairwise-independent `L²`
variables with common mean and variance `σ²`: the refit bias `c = (n-1)/n`. -/
theorem sample_variance_bias {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (μ σ2 : ℝ)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hind : Pairwise (fun i j => X i ⟂ᵢ[P] X j))
    (hmean : ∀ i, P[X i] = μ) (hvar : ∀ i, Var[X i; P] = σ2) :
    ∫ ω, (1 / (n : ℝ)) * ∑ i, (X i ω - (1 / (n : ℝ)) * ∑ j, X j ω) ^ 2 ∂P
      = ((n - 1) / n : ℝ) * σ2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [sample_variance_bias_hetero n hn X μ (fun _ => σ2) hL2 hind hmean hvar]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **(O3, optional)** One refit step, common mean: `|F|` fresh samples of variance `s`, the rest
model samples of variance `w`. Expected refit variance `= c((1-ρ)w + ρs)`, `ρ = |F|/n`.
This is the recursion's right-hand side for a fixed current model (see the module docstring). -/
theorem refit_step {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (μ w s : ℝ)
    (F : Finset (Fin n))
    (hL2 : ∀ i, MemLp (X i) 2 P) (hind : Pairwise (fun i j => X i ⟂ᵢ[P] X j))
    (hmean : ∀ i, P[X i] = μ) (hfresh : ∀ i ∈ F, Var[X i; P] = s)
    (hmodel : ∀ i ∉ F, Var[X i; P] = w) :
    ∫ ω, (1 / (n : ℝ)) * ∑ i, (X i ω - (1 / (n : ℝ)) * ∑ j, X j ω) ^ 2 ∂P
      = ((n - 1) / n : ℝ) * ((1 - (F.card : ℝ) / n) * w + ((F.card : ℝ) / n) * s) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [sample_variance_bias_hetero n hn X μ (fun i => Var[X i; P]) hL2 hind hmean (fun _ => rfl)]
  have hsum : ∑ i, Var[X i; P] = (F.card : ℝ) * s + ((n : ℝ) - F.card) * w := by
    rw [← Finset.sum_add_sum_compl F]
    rw [Finset.sum_congr rfl hfresh,
      Finset.sum_congr rfl (fun i hi => hmodel i (Finset.mem_compl.mp hi))]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_compl, Fintype.card_fin]
    rw [Nat.cast_sub (by simpa using Finset.card_le_univ F)]
  rw [hsum]
  field_simp
  ring


/-- **(O4, new: unequal means)** Drop the common-mean hypothesis: with means `μ_i` and variances
`σ²_i`, the expected MLE variance is `(n-1)/n · mean_i σ²_i` PLUS the spread of the means
`(1/n) Σ (μ_i - μ̄)^2 ≥ 0`. This discharges the "common mean" caveat of `refit_step`. -/
theorem sample_variance_bias_means {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (μ σ2 : Fin n → ℝ)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hind : Pairwise (fun i j => X i ⟂ᵢ[P] X j))
    (hmean : ∀ i, P[X i] = μ i) (hvar : ∀ i, Var[X i; P] = σ2 i) :
    ∫ ω, (1 / (n : ℝ)) * ∑ i, (X i ω - (1 / (n : ℝ)) * ∑ j, X j ω) ^ 2 ∂P
      = ((n - 1) / n : ℝ) * ((1 / (n : ℝ)) * ∑ i, σ2 i)
        + (1 / (n : ℝ)) * ∑ i, (μ i - (1 / (n : ℝ)) * ∑ j, μ j) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp_rw [sample_var_alg n hn]
  have hSL2 : MemLp (∑ i, X i) 2 P := memLp_finsetSum' _ (fun i _ => hL2 i)
  have hsq : ∀ i, P[X i ^ 2] = σ2 i + μ i ^ 2 := by
    intro i; have := variance_eq_sub (hL2 i); rw [hvar i, hmean i] at this; linarith
  have hmeanS : P[∑ i, X i] = ∑ i, μ i := by
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ (fun i _ => (hL2 i).integrable (by norm_num))]
    simp [hmean]
  have hvarS : Var[∑ i, X i; P] = ∑ i, σ2 i := by
    rw [IndepFun.variance_sum (fun i _ => hL2 i) (fun i _ j _ hij => hind hij)]
    simp [hvar]
  have hsqS : P[(∑ i, X i) ^ 2] = (∑ i, σ2 i) + (∑ i, μ i) ^ 2 := by
    have := variance_eq_sub hSL2; rw [hvarS, hmeanS] at this; linarith
  rw [integral_sub, integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun i _ => (hL2 i).integrable_sq)]
  · have e1 : ∀ i, ∫ ω, X i ω ^ 2 ∂P = σ2 i + μ i ^ 2 := fun i => hsq i
    have e2 : ∫ ω, (∑ i, X i ω) ^ 2 ∂P = (∑ i, σ2 i) + (∑ i, μ i) ^ 2 := by
      rw [← hsqS]; congr 1; ext ω; simp
    rw [e2]
    simp only [e1, Finset.sum_add_distrib]
    field_simp
    ring
  · exact (integrable_finsetSum _ (fun i _ => (hL2 i).integrable_sq)).const_mul _
  · exact (hSL2.integrable_sq.const_mul ((1 / (n : ℝ)) ^ 2)).congr
      (Eventually.of_forall fun ω => by simp [Finset.sum_apply])

/-! ## Concrete instance (non-vacuity)

`n = 2` gives `c = 1/2`; with half fresh data (`ρ = 1/2`) and world variance `s = 1`, the open-loop
fixed point is `v* = (1/4)/(3/4) = 1/3`, while the closed loop halves every step. -/

example : vStar (1 / 2) (1 / 2) 1 = 1 / 3 := by norm_num [vStar]

example : v (1 / 2) (1 / 2) 1 1 2 = 3 / 8 := by norm_num [v]

example : v (1 / 2) 0 1 1 3 = 1 / 8 := by norm_num [v]

example (v₀ : ℝ) :
    0 < vStar (1 / 2) (1 / 2) 1 ∧ Tendsto (v (1 / 2) (1 / 2) 1 v₀) atTop (𝓝 (vStar (1 / 2) (1 / 2) 1)) :=
  open_loop_no_collapse _ _ _ v₀ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end U5OpenLoop
