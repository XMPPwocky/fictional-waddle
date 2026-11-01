import Mathlib

/-!
# Bridge8B: same-instance parallel copies keep the mixture-of-restarts tail index

Setting. `ν` is a probability measure on `ℝ` with `ν`-a.e. `s ∈ (0,1]` (a Borel probability
measure on `(0,1]`). A run on an instance of difficulty `s` succeeds with probability `s`.

* `roundsLaw q` is the law on `ℕ` of the index `R ≥ 1` of the first successful round when every
  round independently fails with probability `q`: `P(R = n+1) = q^n (1-q)`.
* `minRound ω = ⨅ i, ω i` is the first round in which one of `N` synchronous copies succeeds.
* `lawSame ν N` (same instance, fresh seeds): the `ν`-mixture of `roundsLaw ((1-s)^N)`,
  written as `P(R_N = n+1) = ∫ ((1-s)^N)^n (1-(1-s)^N) dν`.
* `jointSame ν N` is the joint law of `(s, R_N)` on `ℝ × ℕ`.
* `lawIndep ν N` (independent instances): law of `minRound` under the product of `N` copies of
  the single-instance law `lawSame ν 1`.
* `mean μ = ∫⁻ n, n ∂μ` (valued in `ℝ≥0∞`, so `= ∞` is meaningful).
* `posterior ν N k` is the law of `s` under `jointSame ν N` conditioned on `R_N > k`.
* `uniform01 = volume.restrict (Ioc 0 1)`.

PROVED
* `roundsLaw_pi_map_minRound`: for fixed `q ∈ [0,1)` and `N ≥ 1`, the first-success round of `N`
  independent copies, each with law `roundsLaw q`, has law `roundsLaw (q^N)`.
* `lawSame_apply`, `lawSame_eq_mixture_of_copies`: `lawSame ν N S = ∫ roundsLaw((1-s)^N) S dν`
  `= ∫ P_s(first success among N iid copies ∈ S) dν(s)`; `jointSame_map_snd`: it is the second
  marginal of `jointSame ν N`.
* (a) `tail_same`: `P(R_N > k) = ∫ (1-s)^{Nk} dν`; `tail_indep`: `P(R'_N > k) = (∫ (1-s)^k dν)^N`;
  `mean_eq_tsum_tail`: `E[X] = Σ_{k≥0} P(X > k)` for every measure on `ℕ`;
  `mean_same`: `E[R_N] = Σ_k P(R_N>k) = ∫ 1/(1-(1-s)^N) dν`;
  `one_sub_pow_bounds`: `s ≤ 1-(1-s)^N ≤ N s` on `[0,1]`;
  `mean_same_lt_top_iff`, `mean_same_lt_top_iff_integrable`:
  `E[R_N] < ∞ ↔ ∫ s⁻¹ dν < ∞ ↔ Integrable s⁻¹ ν`, for every `N ≥ 1`.
* (b) `tail_same_uniform`: `P(R_N > k) = 1/(Nk+1)`; `mean_same_uniform`: `E[R_N] = ∞` for all
  `N ≥ 1`; `tail_indep_uniform`: `P(R'_N > k) = (k+1)^{-N}`; `mean_indep_uniform`:
  `E[R'_N] = ∑ (k+1)^{-N} < ∞` and equals `riemannZeta N` for `N ≥ 2`;
  `mean_indep_uniform_one`: `E[R'_1] = ∞`.
* (c) `hazard_uniform`: for `N = 1`, `P(R = k+1 | R > k) = 1/(k+2)`;
  `posterior_apply`: `posterior ν N k A = (∫ (1-s)^{Nk} dν)⁻¹ ∫_A (1-s)^{Nk} dν`;
  `posterior_uniform`: for `ν` uniform, `posterior = Beta(1, Nk+1)`; in particular
  `posterior_uniform_one`: for `N = 1` the posterior after `k` failures is `Beta(1, k+1)`.

INTERPRETED
* The per-round failure probability of the `N` same-instance copies is `(1-s)^N`; this is the
  content of `roundsLaw_pi_map_minRound` (conditionally on `s`, the `N` copies are independent),
  and `lawSame` is the `ν`-mixture of that conditional law. The underlying seed space is not
  built; the law of `R_N` is built from these conditional laws.
* "Run `k` succeeds given runs `0..k-1` failed" is the event `R = k+1` given `R > k` (round `j+1`
  is run `j`).
* `E[R'_N] = ζ(N)` is stated as `((E[R'_N]).toReal : ℂ) = riemannZeta N` with `E[R'_N] ≠ ∞`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Bridge8B

noncomputable section

/-- Law of the first successful round `R ≥ 1` when each round fails independently w.p. `q`. -/
def roundsLaw (q : ℝ) : Measure ℕ :=
  Measure.sum fun n => ENNReal.ofReal (q ^ n * (1 - q)) • Measure.dirac (n + 1)

/-- The first round in which one of `N` synchronous copies succeeds. -/
def minRound {N : ℕ} (ω : Fin N → ℕ) : ℕ := ⨅ i, ω i

/-- Same instance, `N` fresh seeds: mixture over `s ∼ ν` of `roundsLaw ((1-s)^N)`. -/
def lawSame (ν : Measure ℝ) (N : ℕ) : Measure ℕ :=
  Measure.sum fun n =>
    (∫⁻ s, ENNReal.ofReal (((1 - s) ^ N) ^ n * (1 - (1 - s) ^ N)) ∂ν) • Measure.dirac (n + 1)

/-- Joint law of `(s, R_N)`. -/
def jointSame (ν : Measure ℝ) (N : ℕ) : Measure (ℝ × ℕ) :=
  Measure.sum fun n =>
    (ν.withDensity fun s => ENNReal.ofReal (((1 - s) ^ N) ^ n * (1 - (1 - s) ^ N))).prod
      (Measure.dirac (n + 1))

/-- `N` independent instances, each with the single-instance law `lawSame ν 1`. -/
def lawIndep (ν : Measure ℝ) (N : ℕ) : Measure ℕ :=
  (Measure.pi fun _ : Fin N => lawSame ν 1).map minRound

/-- Expectation of the identity on `ℕ`, valued in `ℝ≥0∞`. -/
def mean (μ : Measure ℕ) : ℝ≥0∞ := ∫⁻ n, (n : ℝ≥0∞) ∂μ

/-- Posterior law of `s` given `R_N > k`. -/
def posterior (ν : Measure ℝ) (N k : ℕ) : Measure ℝ :=
  (cond (jointSame ν N) (Prod.snd ⁻¹' {n | k < n})).map Prod.fst

/-- The uniform law on `(0,1]`. -/
def uniform01 : Measure ℝ := volume.restrict (Ioc 0 1)

/-! ### Discrete helpers -/

lemma sum_dirac_apply (c : ℕ → ℝ≥0∞) (S : Set ℕ) :
    (Measure.sum fun n => c n • Measure.dirac (n + 1)) S =
      ∑' n, c n * S.indicator 1 (n + 1) := by
  rw [Measure.sum_apply _ (MeasurableSet.of_discrete)]
  congr 1
  funext n
  rw [Measure.smul_apply, Measure.dirac_apply' _ (MeasurableSet.of_discrete), smul_eq_mul]

lemma indicator_tail (k n : ℕ) :
    ({m : ℕ | k < m}.indicator (1 : ℕ → ℝ≥0∞) (n + 1)) = if k ≤ n then 1 else 0 := by
  by_cases h : k ≤ n
  · rw [ite_cond_eq_true _ _ (eq_true h), indicator_of_mem (show n + 1 ∈ {m : ℕ | k < m} by
      simp only [mem_setOf_eq]; omega)]
    rfl
  · rw [ite_cond_eq_false _ _ (eq_false h), indicator_of_notMem (show n + 1 ∉ {m : ℕ | k < m} by
      simp only [mem_setOf_eq]; omega)]

lemma geom_tail (Q : ℝ≥0∞) (hQ : Q < 1) (k : ℕ) :
    ∑' n, Q ^ n * (1 - Q) * (if k ≤ n then 1 else 0) = Q ^ k := by
  set f : ℕ → ℝ≥0∞ := fun n => Q ^ n * (1 - Q) * (if k ≤ n then 1 else 0) with hf
  have h2 : HasSum f (∑ i ∈ Finset.range k, f i + ∑' i, f (i + k)) :=
    (ENNReal.summable (f := fun i => f (i + k))).hasSum.sum_range_add
  rw [h2.tsum_eq]
  have hz : ∑ i ∈ Finset.range k, f i = 0 := Finset.sum_eq_zero fun i hi => by
    rw [Finset.mem_range] at hi
    have : ¬ k ≤ i := by omega
    simp [hf, this]
  have h3 : (fun i => f (i + k)) = fun n => Q ^ k * (1 - Q) * Q ^ n := by
    funext n
    have : k ≤ n + k := by omega
    simp only [hf, this, if_true, mul_one, pow_add]
    ring
  rw [hz, zero_add, h3, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, mul_assoc,
    ENNReal.mul_inv_cancel (tsub_pos_of_lt hQ).ne' (by simp), mul_one]

lemma ofReal_geom (q : ℝ) (h0 : 0 ≤ q) (n : ℕ) :
    ENNReal.ofReal (q ^ n * (1 - q)) = (ENNReal.ofReal q) ^ n * (1 - ENNReal.ofReal q) := by
  rw [ENNReal.ofReal_mul (pow_nonneg h0 n), ENNReal.ofReal_pow h0,
    ENNReal.ofReal_sub _ h0, ENNReal.ofReal_one]

lemma roundsLaw_apply (q : ℝ) (S : Set ℕ) :
    roundsLaw q S = ∑' n, ENNReal.ofReal (q ^ n * (1 - q)) * S.indicator 1 (n + 1) :=
  sum_dirac_apply _ S

/-- Tail of the geometric round law: `P(R > k) = q^k`. -/
theorem roundsLaw_tail (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) (k : ℕ) :
    roundsLaw q {n | k < n} = ENNReal.ofReal (q ^ k) := by
  rw [roundsLaw_apply]
  simp_rw [indicator_tail, ofReal_geom q h0]
  rw [geom_tail _ (ENNReal.ofReal_lt_one.mpr h1), ENNReal.ofReal_pow h0]

theorem roundsLaw_univ (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) : roundsLaw q univ = 1 := by
  have h := roundsLaw_tail q h0 h1 0
  have : ({n : ℕ | 0 < n} : Set ℕ) ⊆ univ := subset_univ _
  have hz : roundsLaw q {0} = 0 := by
    rw [roundsLaw_apply]
    simp
  rw [← union_compl_self ({0} : Set ℕ)]
  rw [measure_union (disjoint_compl_right) (MeasurableSet.of_discrete), hz, zero_add]
  have : ({0} : Set ℕ)ᶜ = {n | 0 < n} := by
    ext n; simp [Nat.pos_iff_ne_zero]
  rw [this, h, pow_zero, ENNReal.ofReal_one]

instance roundsLaw_isProb (q : ℝ) [Fact (0 ≤ q ∧ q < 1)] : IsProbabilityMeasure (roundsLaw q) :=
  ⟨roundsLaw_univ q (Fact.out : 0 ≤ q ∧ q < 1).1 (Fact.out : 0 ≤ q ∧ q < 1).2⟩

/-- Two finite measures on `ℕ` with equal total mass and equal tails are equal. -/
lemma ext_of_tail (μ ρ : Measure ℕ) [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    (huniv : μ univ = ρ univ) (htail : ∀ k, μ {n | k < n} = ρ {n | k < n}) : μ = ρ := by
  apply Measure.ext_of_singleton
  intro m
  cases m with
  | zero =>
    have hc : ({0} : Set ℕ) = {n | 0 < n}ᶜ := by ext n; simp [Nat.pos_iff_ne_zero]
    rw [hc, measure_compl MeasurableSet.of_discrete (measure_ne_top _ _),
      measure_compl MeasurableSet.of_discrete (measure_ne_top _ _), huniv, htail]
  | succ m =>
    have hc : ({m + 1} : Set ℕ) = {n | m < n} \ {n | m + 1 < n} := by
      ext n; simp only [mem_singleton_iff, mem_sdiff, mem_setOf_eq]; omega
    have hsub : {n : ℕ | m + 1 < n} ⊆ {n | m < n} := fun n hn => by
      simp only [mem_setOf_eq] at hn ⊢; omega
    rw [hc, measure_sdiff hsub MeasurableSet.of_discrete.nullMeasurableSet (measure_ne_top _ _),
      measure_sdiff hsub MeasurableSet.of_discrete.nullMeasurableSet (measure_ne_top _ _),
      htail, htail]

lemma minRound_preimage_tail {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    (minRound ⁻¹' {n | k < n} : Set (Fin N → ℕ)) = univ.pi fun _ => {n | k < n} := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  ext ω
  simp [minRound, Finite.lt_ciInf_iff]

/-- Conditionally on the instance, `N` independent copies with per-round failure probability `q`
first succeed at a round with law `roundsLaw (q^N)`. -/
theorem roundsLaw_pi_map_minRound (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) {N : ℕ} (hN : 1 ≤ N) :
    (Measure.pi fun _ : Fin N => roundsLaw q).map minRound = roundsLaw (q ^ N) := by
  haveI : Fact (0 ≤ q ∧ q < 1) := ⟨⟨h0, h1⟩⟩
  have hqN0 : 0 ≤ q ^ N := pow_nonneg h0 N
  have hqN1 : q ^ N < 1 := pow_lt_one₀ h0 h1 (by omega)
  haveI : Fact (0 ≤ q ^ N ∧ q ^ N < 1) := ⟨⟨hqN0, hqN1⟩⟩
  haveI : IsProbabilityMeasure ((Measure.pi fun _ : Fin N => roundsLaw q).map minRound) :=
    inferInstance
  apply ext_of_tail
  · rw [measure_univ, measure_univ]
  · intro k
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
      minRound_preimage_tail hN, Measure.pi_pi, roundsLaw_tail q h0 h1, roundsLaw_tail _ hqN0 hqN1,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (pow_nonneg h0 k),
      ← pow_mul, ← pow_mul, mul_comm]

/-! ### The same-instance law as a mixture -/

lemma lawSame_apply (ν : Measure ℝ) (N : ℕ) (S : Set ℕ) :
    lawSame ν N S = ∫⁻ s, roundsLaw ((1 - s) ^ N) S ∂ν := by
  rw [lawSame, sum_dirac_apply]
  simp_rw [roundsLaw_apply]
  rw [lintegral_tsum (fun n => by fun_prop)]
  congr 1
  funext n
  rw [lintegral_mul_const _ (by fun_prop)]

lemma ae_mem_of_supp {ν : Measure ℝ} (hν : ∀ᵐ s ∂ν, s ∈ Ioc (0 : ℝ) 1) {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ s ∂ν, 0 ≤ (1 - s) ^ N ∧ (1 - s) ^ N < 1 := by
  filter_upwards [hν] with s hs
  exact ⟨pow_nonneg (by linarith [hs.2]) N,
    pow_lt_one₀ (by linarith [hs.2]) (by linarith [hs.1]) (by omega)⟩

/-- The same-instance law is the `ν`-mixture of the law of the first success among `N`
conditionally independent copies. -/
theorem lawSame_eq_mixture_of_copies (ν : Measure ℝ) (hν : ∀ᵐ s ∂ν, s ∈ Ioc (0 : ℝ) 1)
    {N : ℕ} (hN : 1 ≤ N) (S : Set ℕ) :
    lawSame ν N S =
      ∫⁻ s, ((Measure.pi fun _ : Fin N => roundsLaw (1 - s)).map minRound) S ∂ν := by
  rw [lawSame_apply]
  apply lintegral_congr_ae
  filter_upwards [hν] with s hs
  rw [roundsLaw_pi_map_minRound (1 - s) (by linarith [hs.2]) (by linarith [hs.1]) hN]

lemma jointSame_rect (ν : Measure ℝ) [SFinite ν] (N : ℕ) {A : Set ℝ} (hA : MeasurableSet A)
    (S : Set ℕ) : jointSame ν N (A ×ˢ S) = ∫⁻ s in A, roundsLaw ((1 - s) ^ N) S ∂ν := by
  rw [jointSame, Measure.sum_apply _ (hA.prod MeasurableSet.of_discrete)]
  simp_rw [roundsLaw_apply]
  rw [lintegral_tsum (fun n => by fun_prop)]
  congr 1
  funext n
  rw [Measure.prod_prod, withDensity_apply _ hA,
    Measure.dirac_apply' _ (MeasurableSet.of_discrete), lintegral_mul_const _ (by fun_prop)]

/-- `lawSame ν N` is the law of `R_N` under the joint law of `(s, R_N)`. -/
theorem jointSame_map_snd (ν : Measure ℝ) [SFinite ν] (N : ℕ) :
    (jointSame ν N).map Prod.snd = lawSame ν N := by
  ext S hS
  rw [Measure.map_apply measurable_snd hS, ← univ_prod, jointSame_rect ν N MeasurableSet.univ,
    Measure.restrict_univ, lawSame_apply]

/-! ### (a) -/

/-- (a) `P(R_N > k) = ∫ (1-s)^{Nk} dν`. -/
theorem tail_same (ν : Measure ℝ) (hν : ∀ᵐ s ∂ν, s ∈ Ioc (0 : ℝ) 1) {N : ℕ} (hN : 1 ≤ N)
    (k : ℕ) : lawSame ν N {n | k < n} = ∫⁻ s, ENNReal.ofReal ((1 - s) ^ (N * k)) ∂ν := by
  rw [lawSame_apply]
  apply lintegral_congr_ae
  filter_upwards [ae_mem_of_supp hν hN] with s hs
  rw [roundsLaw_tail _ hs.1 hs.2, pow_mul]

theorem lawSame_univ (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ᵐ s ∂ν, s ∈ Ioc (0 : ℝ) 1)
    {N : ℕ} (hN : 1 ≤ N) : lawSame ν N univ = 1 := by
  rw [lawSame_apply]
  rw [lintegral_congr_ae (g := fun _ => 1) ?_]
  · simp
  filter_upwards [ae_mem_of_supp hν hN] with s hs
  exact roundsLaw_univ _ hs.1 hs.2

theorem lawSame_isProb (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν, s ∈ Ioc (0 : ℝ) 1) {N : ℕ} (hN : 1 ≤ N) :
    IsProbabilityMeasure (lawSame ν N) := ⟨lawSame_univ ν hν hN⟩

/-- (a) `P(R'_N > k) = (∫ (1-s)^k dν)^N`. -/
theorem tail_indep (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ᵐ s ∂ν, s ∈ Ioc (0 : ℝ) 1)
    {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    lawIndep ν N {n | k < n} = (∫⁻ s, ENNReal.ofReal ((1 - s) ^ k) ∂ν) ^ N := by
  haveI := lawSame_isProb ν hν le_rfl
  rw [lawIndep, Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
    minRound_preimage_tail hN, Measure.pi_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, tail_same ν hν le_rfl, one_mul]

/-- Tail-sum formula: `E[X] = Σ_{k≥0} P(X > k)` for every measure on `ℕ`. -/
theorem mean_eq_tsum_tail (μ : Measure ℕ) : mean μ = ∑' k, μ {n | k < n} := by
  have hpt : ∀ n : ℕ, (n : ℝ≥0∞) = ∑' k, {m : ℕ | k < m}.indicator 1 n := by
    intro n
    rw [tsum_eq_sum (s := Finset.range n)]
    · rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
      · simp
      intro k hk
      rw [Finset.mem_range] at hk
      exact indicator_of_mem (show n ∈ {m : ℕ | k < m} from hk) _
    · intro k hk
      rw [Finset.mem_range] at hk
      exact indicator_of_notMem (show n ∉ {m : ℕ | k < m} from hk) _
  rw [mean]
  simp_rw [hpt]
  rw [lintegral_tsum (fun k => Measurable.of_discrete.aemeasurable)]
  congr 1
  funext k
  exact lintegral_indicator_one MeasurableSet.of_discrete

/-- (a) `E[R_N] = Σ_k P(R_N > k) = ∫ 1/(1-(1-s)^N) dν`. -/
theorem mean_same (ν : Measure ℝ) (hν : ∀ᵐ s ∂ν, s ∈ Ioc (0 : ℝ) 1) {N : ℕ} (hN : 1 ≤ N) :
    mean (lawSame ν N) = ∑' k, lawSame ν N {n | k < n} ∧
      mean (lawSame ν N) = ∫⁻ s, ENNReal.ofReal (1 / (1 - (1 - s) ^ N)) ∂ν := by
  refine ⟨mean_eq_tsum_tail _, ?_⟩
  rw [mean_eq_tsum_tail]
  simp_rw [tail_same ν hν hN]
  rw [← lintegral_tsum (fun k => by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [ae_mem_of_supp hν hN] with s hs
  simp_rw [pow_mul]
  simp_rw [ENNReal.ofReal_pow hs.1]
  rw [ENNReal.tsum_geometric, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hs.1,
    ← ENNReal.ofReal_inv_of_pos (by linarith [hs.2]), one_div]

/-- (a) `s ≤ 1-(1-s)^N ≤ N s` on `[0,1]`, `N ≥ 1`. -/
theorem one_sub_pow_bounds {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    s ≤ 1 - (1 - s) ^ N ∧ 1 - (1 - s) ^ N ≤ N * s := by
  constructor
  · have := pow_le_of_le_one (by linarith : (0 : ℝ) ≤ 1 - s) (by linarith) (by omega : N ≠ 0)
    linarith
  · have := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -s) N
    have h' : (1 : ℝ) + -s = 1 - s := by ring
    rw [h'] at this
    linarith

/-- (a) `E[R_N] < ∞ ↔ ∫ s⁻¹ dν < ∞`, for every `N ≥ 1`. -/
theorem mean_same_lt_top_iff (ν : Measure ℝ) (hν : ∀ᵐ s ∂ν, s ∈ Ioc (0 : ℝ) 1) {N : ℕ}
    (hN : 1 ≤ N) :
    mean (lawSame ν N) < ∞ ↔ ∫⁻ s, ENNReal.ofReal s⁻¹ ∂ν < ∞ := by
  rw [(mean_same ν hν hN).2]
  constructor
  · intro h
    have hle : ∫⁻ s, ENNReal.ofReal s⁻¹ ∂ν ≤
        ∫⁻ s, (N : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - (1 - s) ^ N)) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hν] with s hs
      obtain ⟨hb1, hb2⟩ := one_sub_pow_bounds hs.1.le hs.2 hN
      have hpos : 0 < 1 - (1 - s) ^ N := lt_of_lt_of_le hs.1 hb1
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
      apply ENNReal.ofReal_le_ofReal
      rw [inv_eq_one_div, mul_one_div, div_le_div_iff₀ hs.1 hpos]
      linarith
    rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)] at hle
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top (ENNReal.natCast_lt_top N) h)
  · intro h
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) h
    filter_upwards [hν] with s hs
    obtain ⟨hb1, _⟩ := one_sub_pow_bounds hs.1.le hs.2 hN
    apply ENNReal.ofReal_le_ofReal
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hs.1 hb1

theorem mean_same_lt_top_iff_integrable (ν : Measure ℝ) (hν : ∀ᵐ s ∂ν, s ∈ Ioc (0 : ℝ) 1)
    {N : ℕ} (hN : 1 ≤ N) :
    mean (lawSame ν N) < ∞ ↔ Integrable (fun s : ℝ => s⁻¹) ν := by
  rw [mean_same_lt_top_iff ν hν hN, Integrable,
    hasFiniteIntegral_iff_ofReal (by
      filter_upwards [hν] with s hs
      exact inv_nonneg.mpr hs.1.le)]
  exact ⟨fun h => ⟨measurable_inv.aestronglyMeasurable, h⟩, fun h => h.2⟩

/-! ### (b) uniform `ν` -/

instance : IsProbabilityMeasure uniform01 := ⟨by simp [uniform01]⟩

lemma uniform01_supp : ∀ᵐ s ∂uniform01, s ∈ Ioc (0 : ℝ) 1 :=
  ae_restrict_mem measurableSet_Ioc

lemma lintegral_uniform_pow (m : ℕ) :
    ∫⁻ s, ENNReal.ofReal ((1 - s) ^ m) ∂uniform01 = ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
  rw [uniform01, ← ofReal_integral_eq_lintegral_ofReal
    ((by fun_prop : Continuous fun s : ℝ => (1 - s) ^ m).integrableOn_Ioc)]
  · rw [← intervalIntegral.integral_of_le zero_le_one]
    congr 1
    simp [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ m)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact pow_nonneg (by linarith [hs.2]) m

/-- (b) `P(R_N > k) = 1/(Nk+1)` for uniform `ν`. -/
theorem tail_same_uniform {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    lawSame uniform01 N {n | k < n} = ENNReal.ofReal (1 / ((N : ℝ) * k + 1)) := by
  rw [tail_same uniform01 uniform01_supp hN, lintegral_uniform_pow]
  push_cast
  rfl

/-- (b) `E[R_N] = ∞` for uniform `ν` and every `N ≥ 1`. -/
theorem mean_same_uniform {N : ℕ} (hN : 1 ≤ N) : mean (lawSame uniform01 N) = ∞ := by
  rw [mean_eq_tsum_tail]
  simp_rw [tail_same_uniform hN]
  by_contra hne
  have hs := ENNReal.summable_toReal hne
  have hnn : ∀ k : ℕ, 0 ≤ 1 / ((N : ℝ) * k + 1) := fun k => by positivity
  simp_rw [ENNReal.toReal_ofReal (hnn _)] at hs
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs2 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (show Summable fun k : ℕ => (N : ℝ) * (1 / ((N : ℝ) * k + 1)) from hs.mul_left _)
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hs3 : Summable fun n : ℕ => 1 / (n : ℝ) := by
    rw [← summable_nat_add_iff 1]
    simpa using hs2
  exact Real.not_summable_one_div_natCast hs3

/-- (b) `P(R'_N > k) = (k+1)^{-N}` for uniform `ν`. -/
theorem tail_indep_uniform {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    lawIndep uniform01 N {n | k < n} = ENNReal.ofReal (1 / ((k : ℝ) + 1) ^ N) := by
  rw [tail_indep uniform01 uniform01_supp hN, lintegral_uniform_pow,
    ← ENNReal.ofReal_pow (by positivity), div_pow, one_pow]

/-- (b) `E[R'_N] = Σ_k (k+1)^{-N} < ∞`, and it equals `ζ(N)`, for uniform `ν` and `N ≥ 2`. -/
theorem mean_indep_uniform {N : ℕ} (hN : 2 ≤ N) :
    mean (lawIndep uniform01 N) = ENNReal.ofReal (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ N) ∧
      mean (lawIndep uniform01 N) ≠ ∞ ∧
      (((mean (lawIndep uniform01 N)).toReal : ℝ) : ℂ) = riemannZeta N := by
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ N :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hsum1 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ N := by
    have := (summable_nat_add_iff 1).mpr hsum
    simpa using this
  have hmean : mean (lawIndep uniform01 N) = ENNReal.ofReal (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ N) := by
    rw [mean_eq_tsum_tail]
    simp_rw [tail_indep_uniform (by omega : 1 ≤ N)]
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum1]
  refine ⟨hmean, by rw [hmean]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [hmean, ENNReal.toReal_ofReal (tsum_nonneg fun k => by positivity),
    zeta_nat_eq_tsum_of_gt_one (by omega)]
  have hc : (fun n : ℕ => 1 / (n : ℂ) ^ N) = fun n : ℕ => (((1 / (n : ℝ) ^ N : ℝ)) : ℂ) := by
    funext n; push_cast; rfl
  rw [hc, ← Complex.ofReal_tsum, hsum.tsum_eq_zero_add]
  congr 1
  simp [zero_pow (by omega : N ≠ 0)]

/-- `E[R'_1] = ∞` for uniform `ν`. -/
theorem mean_indep_uniform_one : mean (lawIndep uniform01 1) = ∞ := by
  rw [← mean_same_uniform (le_refl 1), mean_eq_tsum_tail, mean_eq_tsum_tail]
  congr 1
  funext k
  rw [tail_indep_uniform le_rfl, tail_same_uniform le_rfl]
  simp

/-! ### (c) hazard and posterior -/

/-- (c) For `N = 1` and uniform `ν`: `P(R = k+1 | R > k) = 1/(k+2)`. -/
theorem hazard_uniform (k : ℕ) :
    cond (lawSame uniform01 1) {n | k < n} {k + 1} = ENNReal.ofReal (1 / ((k : ℝ) + 2)) := by
  haveI := lawSame_isProb uniform01 uniform01_supp le_rfl
  rw [cond_apply MeasurableSet.of_discrete]
  have hi : {n : ℕ | k < n} ∩ {k + 1} = {k + 1} := by
    ext n; simp only [mem_inter_iff, mem_setOf_eq, mem_singleton_iff]; omega
  have hc : ({k + 1} : Set ℕ) = {n | k < n} \ {n | k + 1 < n} := by
    ext n; simp only [mem_singleton_iff, mem_sdiff, mem_setOf_eq]; omega
  have hsub : {n : ℕ | k + 1 < n} ⊆ {n | k < n} := fun n hn => by
    simp only [mem_setOf_eq] at hn ⊢; omega
  rw [hi, hc, measure_sdiff hsub MeasurableSet.of_discrete.nullMeasurableSet (measure_ne_top _ _),
    tail_same_uniform le_rfl, tail_same_uniform le_rfl]
  have ha : (0 : ℝ) < 1 / ((1 : ℕ) * (k : ℝ) + 1) := by positivity
  rw [← ENNReal.ofReal_sub _ (by positivity), ← ENNReal.ofReal_inv_of_pos ha,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  field_simp
  ring

/-- (c) The posterior of `s` given `R_N > k` has density `∝ (1-s)^{Nk}` w.r.t. `ν`. -/
theorem posterior_apply (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν, s ∈ Ioc (0 : ℝ) 1) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    posterior ν N k A = (∫⁻ s, ENNReal.ofReal ((1 - s) ^ (N * k)) ∂ν)⁻¹ *
      ∫⁻ s in A, ENNReal.ofReal ((1 - s) ^ (N * k)) ∂ν := by
  rw [posterior, Measure.map_apply measurable_fst hA,
    cond_apply (measurable_snd MeasurableSet.of_discrete)]
  have h1 : (Prod.snd ⁻¹' {n : ℕ | k < n} : Set (ℝ × ℕ)) = univ ×ˢ {n | k < n} := by
    ext p; simp
  have h2 : (Prod.snd ⁻¹' {n : ℕ | k < n} ∩ Prod.fst ⁻¹' A : Set (ℝ × ℕ)) = A ×ˢ {n | k < n} := by
    ext p; simp [and_comm]
  rw [h2, h1, jointSame_rect ν N MeasurableSet.univ, jointSame_rect ν N hA, Measure.restrict_univ]
  have hae : ∀ᵐ s ∂ν, roundsLaw ((1 - s) ^ N) {n | k < n} =
      ENNReal.ofReal ((1 - s) ^ (N * k)) := by
    filter_upwards [ae_mem_of_supp hν hN] with s hs
    rw [roundsLaw_tail _ hs.1 hs.2, pow_mul]
  rw [lintegral_congr_ae hae, lintegral_congr_ae (ae_restrict_of_ae hae)]

lemma beta_one (m : ℝ) (hm : 0 < m) : ProbabilityTheory.beta 1 m = 1 / m := by
  rw [ProbabilityTheory.beta, Real.Gamma_one, one_mul, add_comm,
    Real.Gamma_add_one hm.ne']
  have := Real.Gamma_pos_of_pos hm
  field_simp

/-- (c) For uniform `ν`, the posterior of `s` given `R_N > k` is `Beta(1, Nk+1)`. -/
theorem posterior_uniform {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    posterior uniform01 N k = betaMeasure 1 ((N : ℝ) * k + 1) := by
  ext A hA
  set m : ℕ := N * k with hm
  have hmR : ((N : ℝ) * k + 1) = (m : ℝ) + 1 := by rw [hm]; push_cast; ring
  rw [posterior_apply uniform01 uniform01_supp hN k hA, ← hm, lintegral_uniform_pow, hmR,
    betaMeasure, withDensity_apply _ hA]
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, uniform01, Measure.restrict_restrict hA,
    inter_comm, ← Measure.restrict_restrict measurableSet_Ioc,
    ← lintegral_indicator measurableSet_Ioc]
  have hfun : ∀ᵐ s ∂(volume.restrict A),
      (Ioc (0 : ℝ) 1).indicator
        (fun s => ENNReal.ofReal ((m : ℝ) + 1) * ENNReal.ofReal ((1 - s) ^ m)) s =
      betaPDF 1 ((m : ℝ) + 1) s := by
    refine ae_restrict_of_ae ?_
    filter_upwards [Measure.ae_ne volume 1] with s hs1
    by_cases h : 0 < s ∧ s < 1
    · rw [betaPDF_of_pos_lt_one h.1 h.2, indicator_of_mem (show s ∈ Ioc (0 : ℝ) 1 from ⟨h.1, h.2.le⟩),
        ← ENNReal.ofReal_mul hpos.le, beta_one _ hpos]
      congr 1
      rw [sub_self, Real.rpow_zero, add_sub_cancel_right, Real.rpow_natCast]
      field_simp
    · rw [betaPDF_eq, if_neg h, ENNReal.ofReal_zero, indicator_of_notMem]
      rintro ⟨h0, h1⟩
      exact h ⟨h0, lt_of_le_of_ne h1 hs1⟩
  rw [lintegral_congr_ae hfun]

/-- (c) For `N = 1` and uniform `ν`, the posterior of `s` after `k` failures is `Beta(1, k+1)`. -/
theorem posterior_uniform_one (k : ℕ) :
    posterior uniform01 1 k = betaMeasure 1 ((k : ℝ) + 1) := by
  rw [posterior_uniform le_rfl, Nat.cast_one, one_mul]

end

end Bridge8B
