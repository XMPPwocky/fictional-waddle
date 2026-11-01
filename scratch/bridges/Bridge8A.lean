import Mathlib

/-!
# Bridge8A: same-instance parallel copies keep the mixture-of-restarts tail index

Setting. `ν` is a Borel probability measure on `ℝ` carried by `(0,1]` (hypothesis
`∀ᵐ s ∂ν, s ∈ Ioc 0 1`); `s` is the per-round success probability of the instance.
`R_N` is the number of synchronous rounds until one of `N` copies (fresh seeds, same
instance) succeeds; `R'_N` is the analogue on `N` independent instances.

PROVED.
* `lintegral_nat_eq_tsum_tail`: for any measurable `R : Ω → ℕ`,
  `∫⁻ R dμ = ∑' k, μ {k < R}` (tail-sum formula).
* `tailSame_eq_ofReal_integral`, `tailIndep_eq_ofReal_integral`: the tails used below equal
  `∫ (1-s)^(N k) dν` and `(∫ (1-s)^k dν)^N` (Bochner integrals).
* (a) `expSame_eq_lintegral`: `∑' k, P(R_N > k) = ∫⁻ 1/(1-(1-s)^N) dν` for `N ≥ 1`;
  `bounds`: `s ≤ 1-(1-s)^N ≤ N s` on `[0,1]` for `N ≥ 1`;
  `expSame_lt_top_iff`: `E[R_N] < ∞ ↔ ∫⁻ s⁻¹ dν < ∞` for every `N ≥ 1`;
  `partA`: the same two statements for any measurable `ℕ`-valued `R` with these tails.
* (b) `tailSame_unif`: `P(R_N > k) = 1/(N k + 1)` for `ν` uniform on `(0,1]`;
  `expSame_unif_eq_top`: `E[R_N] = ∞` for every `N`;
  `lintegral_inv_unif_eq_top`: hence `∫⁻ s⁻¹ dν = ∞` (via (a));
  `tailIndep_unif`: `P(R'_N > k) = (k+1)^(-N)`;
  `expIndep_unif`, `zeta_eq_tsum`: `E[R'_N] = ζ(N)` (finite) for `N ≥ 2`.
* (c) `hazard_unif`: for `N = 1`, `ν` uniform and any `ℕ`-valued `R` with these tails,
  `P(R = k+1 | R > k) = 1/(k+2)` (run `k` succeeds given runs `0..k-1` failed);
  `hazard_unif_real`: the same identity for the real tails;
  `posterior_unif`: the posterior of `s` after `k` failures is `Beta(1, k+1)`
  (Mathlib's `ProbabilityTheory.betaMeasure 1 (k+1)`).

INTERPRETED.
* `P(R_N > k)` and `P(R'_N > k)` are taken to be the stated formulas (`tailSame`, `tailIndep`),
  written as lower Lebesgue integrals in `ℝ≥0∞`; `E[R_N]` is `∑' k, P(R_N > k)` in `ℝ≥0∞`
  (so `E = ∞` is a value, not an undefined quantity). `partA` and `hazard_unif` state the results
  for any random variable `R` whose tail probabilities are the stated ones.
* "ν uniform on (0,1]" is `volume.restrict (Ioc 0 1)`.
* `ζ(N)` is Mathlib's `riemannZeta (N : ℂ)`.
* The posterior after `k` failures is Bayes' rule for the likelihood `(1-s)^k`:
  `posterior ν k = (∫⁻ (1-s)^k dν)⁻¹ • ν.withDensity ((1-s)^k)`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Bridge8A

/-- `P(R_N > k)` for `N` same-instance copies: `∫ (1-s)^(N k) dν`. -/
noncomputable def tailSame (ν : Measure ℝ) (N k : ℕ) : ℝ≥0∞ :=
  ∫⁻ s, ENNReal.ofReal ((1 - s) ^ (N * k)) ∂ν

/-- `P(R'_N > k)` for `N` independent instances: `(∫ (1-s)^k dν)^N`. -/
noncomputable def tailIndep (ν : Measure ℝ) (N k : ℕ) : ℝ≥0∞ :=
  (∫⁻ s, ENNReal.ofReal ((1 - s) ^ k) ∂ν) ^ N

/-- `E[R_N] = ∑_{k ≥ 0} P(R_N > k)`. -/
noncomputable def expSame (ν : Measure ℝ) (N : ℕ) : ℝ≥0∞ := ∑' k, tailSame ν N k

/-- `E[R'_N] = ∑_{k ≥ 0} P(R'_N > k)`. -/
noncomputable def expIndep (ν : Measure ℝ) (N : ℕ) : ℝ≥0∞ := ∑' k, tailIndep ν N k

/-- The uniform distribution on `(0,1]`. -/
noncomputable def unif : Measure ℝ := volume.restrict (Ioc 0 1)

instance : IsProbabilityMeasure unif :=
  ⟨by simp [unif, Real.volume_Ioc]⟩

/-- Tail-sum formula for a `ℕ`-valued random variable. -/
theorem lintegral_nat_eq_tsum_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (R : Ω → ℕ) (hR : Measurable R) :
    ∫⁻ ω, (R ω : ℝ≥0∞) ∂μ = ∑' k : ℕ, μ {ω | k < R ω} := by
  have h1 : ∀ ω, (R ω : ℝ≥0∞) = ∑' k : ℕ, {ω | k < R ω}.indicator 1 ω := by
    intro ω
    rw [tsum_eq_sum (s := Finset.range (R ω))]
    · rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
      · simp
      · intro k hk
        simp [Set.indicator, Finset.mem_range.mp hk]
    · intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      simp [Set.indicator, not_lt.mpr hk]
  have hmeas : ∀ k : ℕ, MeasurableSet {ω | k < R ω} := fun k => hR measurableSet_Ioi
  simp_rw [h1]
  rw [lintegral_tsum (fun k => (measurable_one.indicator (hmeas k)).aemeasurable)]
  congr 1
  ext k
  exact lintegral_indicator_one (hmeas k)

section Bounds

/-- `s ≤ 1 - (1-s)^N ≤ N s` for `s ∈ [0,1]`, `N ≥ 1`. -/
theorem bounds {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    s ≤ 1 - (1 - s) ^ N ∧ 1 - (1 - s) ^ N ≤ N * s := by
  constructor
  · have : (1 - s) ^ N ≤ (1 - s) ^ 1 :=
      pow_le_pow_of_le_one (by linarith) (by linarith) hN
    simp only [pow_one] at this
    linarith
  · have := one_add_mul_le_pow (a := -s) (by linarith) N
    have h2 : (1 : ℝ) + -s = 1 - s := by ring
    rw [h2] at this
    linarith

lemma q_lt_one {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) {N : ℕ} (hN : 1 ≤ N) : (1 - s) ^ N < 1 := by
  have := (bounds hs.1.le hs.2 hN).1
  linarith [hs.1]

lemma geom_pointwise {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) {N : ℕ} (hN : 1 ≤ N) :
    ∑' k : ℕ, ENNReal.ofReal ((1 - s) ^ (N * k)) = ENNReal.ofReal (1 / (1 - (1 - s) ^ N)) := by
  have hq0 : 0 ≤ (1 - s) ^ N := pow_nonneg (by linarith [hs.2]) N
  have hq1 := q_lt_one hs hN
  simp_rw [pow_mul]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => pow_nonneg hq0 k)
    (summable_geometric_of_lt_one hq0 hq1), tsum_geometric_of_lt_one hq0 hq1, one_div]

end Bounds

section PartA

variable {ν : Measure ℝ}

lemma measurable_pow_ofReal (m : ℕ) :
    Measurable fun s : ℝ => ENNReal.ofReal ((1 - s) ^ m) := by fun_prop

/-- The stated tail of `R_N` agrees with the Bochner integral `∫ (1-s)^(N k) dν`. -/
theorem tailSame_eq_ofReal_integral [IsFiniteMeasure ν] (hν : ∀ᵐ s ∂ν, s ∈ Ioc (0 : ℝ) 1)
    (N k : ℕ) : tailSame ν N k = ENNReal.ofReal (∫ s, (1 - s) ^ (N * k) ∂ν) := by
  have hnn : ∀ᵐ s ∂ν, 0 ≤ (1 - s) ^ (N * k) :=
    hν.mono fun s hs => pow_nonneg (by linarith [hs.2]) _
  have hint : Integrable (fun s : ℝ => (1 - s) ^ (N * k)) ν := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [hν] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith [hs.2]) _)]
    exact pow_le_one₀ (by linarith [hs.2]) (by linarith [hs.1])
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
  rfl

/-- The stated tail of `R'_N` agrees with `(∫ (1-s)^k dν)^N` (Bochner integral). -/
theorem tailIndep_eq_ofReal_integral [IsFiniteMeasure ν] (hν : ∀ᵐ s ∂ν, s ∈ Ioc (0 : ℝ) 1)
    (N k : ℕ) : tailIndep ν N k = ENNReal.ofReal ((∫ s, (1 - s) ^ k ∂ν) ^ N) := by
  have h := tailSame_eq_ofReal_integral hν 1 k
  simp only [tailSame, one_mul] at h
  have hnn : 0 ≤ ∫ s, (1 - s) ^ k ∂ν :=
    integral_nonneg_of_ae (hν.mono fun s hs => pow_nonneg (by linarith [hs.2]) _)
  rw [tailIndep, h, ENNReal.ofReal_pow hnn]

/-- (a) `E[R_N] = ∫ 1/(1-(1-s)^N) dν` for `N ≥ 1`. -/
theorem expSame_eq_lintegral (hν : ∀ᵐ s ∂ν, s ∈ Ioc (0 : ℝ) 1) {N : ℕ} (hN : 1 ≤ N) :
    expSame ν N = ∫⁻ s, ENNReal.ofReal (1 / (1 - (1 - s) ^ N)) ∂ν := by
  unfold expSame tailSame
  rw [← lintegral_tsum (fun k => (measurable_pow_ofReal (N * k)).aemeasurable)]
  exact lintegral_congr_ae (hν.mono fun s hs => geom_pointwise hs hN)

/-- (a) `E[R_N] < ∞ ↔ ∫ s⁻¹ dν < ∞`, for every `N ≥ 1`. -/
theorem expSame_lt_top_iff (hν : ∀ᵐ s ∂ν, s ∈ Ioc (0 : ℝ) 1) {N : ℕ} (hN : 1 ≤ N) :
    expSame ν N < ∞ ↔ ∫⁻ s, ENNReal.ofReal s⁻¹ ∂ν < ∞ := by
  rw [expSame_eq_lintegral hν hN]
  constructor
  · intro h
    have hle : ∫⁻ s, ENNReal.ofReal s⁻¹ ∂ν ≤
        ∫⁻ s, (N : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - (1 - s) ^ N)) ∂ν := by
      refine lintegral_mono_ae (hν.mono fun s hs => ?_)
      have hb := (bounds hs.1.le hs.2 hN).2
      have hq := q_lt_one hs hN
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
      apply ENNReal.ofReal_le_ofReal
      rw [mul_one_div, inv_eq_one_div, div_le_div_iff₀ hs.1 (by linarith)]
      linarith
    rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)] at hle
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top (ENNReal.natCast_lt_top N) h)
  · intro h
    refine lt_of_le_of_lt (lintegral_mono_ae (hν.mono fun s hs => ?_)) h
    have hb := (bounds hs.1.le hs.2 hN).1
    apply ENNReal.ofReal_le_ofReal
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hs.1 hb

/-- (a) for a random variable: if `R : Ω → ℕ` has `P(R > k) = ∫ (1-s)^(N k) dν`, then
`E[R] = ∫ 1/(1-(1-s)^N) dν`, and `E[R] < ∞ ↔ ∫ s⁻¹ dν < ∞`. -/
theorem partA {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (R : Ω → ℕ) (hR : Measurable R)
    (hν : ∀ᵐ s ∂ν, s ∈ Ioc (0 : ℝ) 1) {N : ℕ} (hN : 1 ≤ N)
    (htail : ∀ k : ℕ, μ {ω | k < R ω} = tailSame ν N k) :
    ∫⁻ ω, (R ω : ℝ≥0∞) ∂μ = ∫⁻ s, ENNReal.ofReal (1 / (1 - (1 - s) ^ N)) ∂ν ∧
      (∫⁻ ω, (R ω : ℝ≥0∞) ∂μ < ∞ ↔ ∫⁻ s, ENNReal.ofReal s⁻¹ ∂ν < ∞) := by
  have hE : ∫⁻ ω, (R ω : ℝ≥0∞) ∂μ = expSame ν N := by
    rw [lintegral_nat_eq_tsum_tail μ R hR, expSame]
    exact tsum_congr htail
  rw [hE]
  exact ⟨expSame_eq_lintegral hν hN, expSame_lt_top_iff hν hN⟩

end PartA

section PartB

lemma unif_ae : ∀ᵐ s ∂unif, s ∈ Ioc (0 : ℝ) 1 :=
  ae_restrict_mem measurableSet_Ioc

theorem integral_unif_pow (m : ℕ) : ∫ s, (1 - s) ^ m ∂unif = 1 / ((m : ℝ) + 1) := by
  rw [unif, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_left (fun x => x ^ m) 1]
  simp [integral_pow]

/-- (b) `P(R_N > k) = 1/(N k + 1)` for `ν` uniform. -/
theorem tailSame_unif (N k : ℕ) :
    tailSame unif N k = ENNReal.ofReal (1 / ((N : ℝ) * k + 1)) := by
  rw [tailSame_eq_ofReal_integral unif_ae, integral_unif_pow]
  push_cast
  rfl

/-- (b) `E[R_N] = ∞` for every `N`, for `ν` uniform. -/
theorem expSame_unif_eq_top (N : ℕ) : expSame unif N = ∞ := by
  by_contra h
  unfold expSame at h
  simp_rw [tailSame_unif] at h
  have hs := ENNReal.summable_toReal h
  have hpos : ∀ k : ℕ, 0 ≤ 1 / ((N : ℝ) * k + 1) := fun k => by positivity
  simp_rw [ENNReal.toReal_ofReal (hpos _)] at hs
  have hs2 : Summable fun k : ℕ => ((N : ℝ) + 1) * (1 / ((N : ℝ) * k + 1)) := hs.mul_left _
  have hharm : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) := by
    refine hs2.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  apply Real.not_summable_one_div_natCast
  rw [← summable_nat_add_iff 1]
  exact_mod_cast hharm

/-- (b) consequently, by (a), `∫ s⁻¹ dν = ∞` for `ν` uniform. -/
theorem lintegral_inv_unif_eq_top : ∫⁻ s, ENNReal.ofReal s⁻¹ ∂unif = ∞ := by
  by_contra h
  have := (expSame_lt_top_iff unif_ae (le_refl 1)).mpr (lt_top_iff_ne_top.mpr h)
  rw [expSame_unif_eq_top] at this
  exact lt_irrefl _ this

/-- (b) `P(R'_N > k) = (k+1)^(-N)` for `ν` uniform. -/
theorem tailIndep_unif (N k : ℕ) :
    tailIndep unif N k = ENNReal.ofReal (((k : ℝ) + 1) ^ (-(N : ℤ))) := by
  rw [tailIndep_eq_ofReal_integral unif_ae, integral_unif_pow, zpow_neg, zpow_natCast,
    one_div, inv_pow]

lemma summable_shift_pow {N : ℕ} (hN : 2 ≤ N) :
    Summable fun k : ℕ => (((k : ℝ) + 1) ^ N)⁻¹ := by
  have h := (Real.summable_one_div_nat_pow (p := N)).mpr (by omega)
  rw [← summable_nat_add_iff 1] at h
  simpa [one_div] using h

/-- (b) `E[R'_N] = ∑_{k ≥ 0} (k+1)^(-N)`, a finite value, for `N ≥ 2`. -/
theorem expIndep_unif {N : ℕ} (hN : 2 ≤ N) :
    expIndep unif N = ENNReal.ofReal (∑' k : ℕ, (((k : ℝ) + 1) ^ N)⁻¹) ∧ expIndep unif N ≠ ∞ := by
  have h : expIndep unif N = ENNReal.ofReal (∑' k : ℕ, (((k : ℝ) + 1) ^ N)⁻¹) := by
    unfold expIndep
    simp_rw [tailIndep_unif, zpow_neg, zpow_natCast]
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) (summable_shift_pow hN)]
  exact ⟨h, by rw [h]; exact ENNReal.ofReal_ne_top⟩

/-- (b) `∑_{k ≥ 0} (k+1)^(-N) = ζ(N)` for `N ≥ 2`. -/
theorem zeta_eq_tsum {N : ℕ} (hN : 2 ≤ N) :
    ((∑' k : ℕ, (((k : ℝ) + 1) ^ N)⁻¹ : ℝ) : ℂ) = riemannZeta N := by
  set f : ℕ → ℂ := fun n => 1 / (n : ℂ) ^ N with hf
  have hshift : ∀ k : ℕ, f (k + 1) = (((((k : ℝ) + 1) ^ N)⁻¹ : ℝ) : ℂ) := by
    intro k
    simp only [hf]
    push_cast
    rw [one_div]
  have hsum : Summable fun k : ℕ => f (k + 1) := by
    have h := (Complex.summable_ofReal (f := fun k : ℕ => (((k : ℝ) + 1) ^ N)⁻¹)).mpr
      (summable_shift_pow hN)
    exact h.congr fun k => (hshift k).symm
  have h0 : f 0 = 0 := by simp [hf, zero_pow (by omega : N ≠ 0)]
  rw [zeta_nat_eq_tsum_of_gt_one (by omega)]
  change _ = ∑' n, f n
  rw [tsum_eq_zero_add' hsum, h0, zero_add, Complex.ofReal_tsum]
  exact tsum_congr fun k => (hshift k).symm

/-- (b) `E[R'_N] = ζ(N)` for `N ≥ 2`, for `ν` uniform. -/
theorem expIndep_unif_eq_zeta {N : ℕ} (hN : 2 ≤ N) :
    expIndep unif N = ENNReal.ofReal (riemannZeta N).re := by
  rw [(expIndep_unif hN).1, ← zeta_eq_tsum hN, Complex.ofReal_re]

end PartB

section PartC

/-- (c) For `N = 1`, `ν` uniform and any `R : Ω → ℕ` with `P(R > k) = ∫ (1-s)^k dν`:
`P(R = k+1 | R > k) = 1/(k+2)`, i.e. run `k` succeeds given runs `0..k-1` failed. -/
theorem hazard_unif {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (R : Ω → ℕ)
    (hR : Measurable R) (htail : ∀ k : ℕ, μ {ω | k < R ω} = tailSame unif 1 k) (k : ℕ) :
    μ[{ω | R ω = k + 1} | {ω | k < R ω}] = ENNReal.ofReal (1 / ((k : ℝ) + 2)) := by
  have hmeas : ∀ j : ℕ, MeasurableSet {ω | j < R ω} := fun j => hR measurableSet_Ioi
  have hT : ∀ j : ℕ, μ {ω | j < R ω} = ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
    intro j
    rw [htail, tailSame_unif]
    push_cast
    ring_nf
  have hset : {ω | k < R ω} ∩ {ω | R ω = k + 1} = {ω | k < R ω} \ {ω | k + 1 < R ω} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, not_lt]
    omega
  have hsub : {ω | k + 1 < R ω} ⊆ {ω | k < R ω} := fun ω (h : k + 1 < R ω) =>
    (show k < R ω by omega)
  rw [cond_apply (hmeas k), hset, measure_sdiff hsub (hmeas (k + 1)).nullMeasurableSet
    (by rw [hT]; exact ENNReal.ofReal_ne_top), hT, hT,
    ← ENNReal.ofReal_sub _ (by positivity), ← ENNReal.ofReal_inv_of_pos (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  field_simp
  ring

/-- (c) The same identity for the real tails `T k = ∫ (1-s)^k dν`, `ν` uniform:
`(T k - T (k+1)) / T k = 1/(k+2)`. -/
theorem hazard_unif_real (k : ℕ) :
    ((∫ s, (1 - s) ^ k ∂unif) - ∫ s, (1 - s) ^ (k + 1) ∂unif) / ∫ s, (1 - s) ^ k ∂unif
      = 1 / ((k : ℝ) + 2) := by
  rw [integral_unif_pow, integral_unif_pow]
  push_cast
  field_simp
  ring

/-- Bayes posterior of `s` after `k` failures: prior `ν` reweighted by the likelihood
`(1-s)^k` and normalised. -/
noncomputable def posterior (ν : Measure ℝ) (k : ℕ) : Measure ℝ :=
  (∫⁻ s, ENNReal.ofReal ((1 - s) ^ k) ∂ν)⁻¹ •
    ν.withDensity (fun s => ENNReal.ofReal ((1 - s) ^ k))

lemma beta_one (k : ℕ) : beta 1 ((k : ℝ) + 1) = 1 / ((k : ℝ) + 1) := by
  unfold beta
  have h1 : (1 : ℝ) + ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [h1, Real.Gamma_one, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
    Nat.factorial_succ]
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- (c) For `N = 1` and `ν` uniform, the posterior of `s` after `k` failures is
`Beta(1, k+1)`. -/
theorem posterior_unif (k : ℕ) : posterior unif k = betaMeasure 1 ((k : ℝ) + 1) := by
  have hc : ∫⁻ s, ENNReal.ofReal ((1 - s) ^ k) ∂unif = ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    have := tailSame_unif 1 k
    simp only [tailSame, one_mul, Nat.cast_one] at this
    exact this
  rw [posterior, hc, ← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv,
    ← withDensity_smul _ (measurable_pow_ofReal k), unif,
    ← withDensity_indicator measurableSet_Ioc, betaMeasure]
  refine withDensity_congr_ae ?_
  have hnull : volume ({1} : Set ℝ) = 0 := measure_singleton 1
  refine measure_mono_null (fun s hs => ?_) hnull
  simp only [mem_singleton_iff]
  by_contra hs1
  apply hs
  show (Ioc 0 1).indicator _ s = betaPDF 1 ((k : ℝ) + 1) s
  by_cases hin : s ∈ Ioo (0 : ℝ) 1
  · have hin' : s ∈ Ioc (0 : ℝ) 1 := ⟨hin.1, hin.2.le⟩
    rw [indicator_of_mem hin', betaPDF_of_pos_lt_one hin.1 hin.2, beta_one]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [sub_self, Real.rpow_zero, add_sub_cancel_right, Real.rpow_natCast]
    field_simp
  · have hout : s ∉ Ioc (0 : ℝ) 1 := by
      rintro ⟨h0, h1⟩
      exact hin ⟨h0, lt_of_le_of_ne h1 hs1⟩
    rw [indicator_of_notMem hout]
    rcases le_or_gt s 0 with h | h
    · rw [betaPDF_eq_zero_of_nonpos h]
    · have : 1 ≤ s := by
        by_contra h'
        exact hin ⟨h, lt_of_not_ge h'⟩
      rw [betaPDF_eq_zero_of_one_le this]

end PartC

end Bridge8A
