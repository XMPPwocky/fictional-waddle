import Mathlib

/-!
# Expected cost of a restarted search

A search is restarted in runs `0, 1, 2, …`. Run `k` is cut off after `τ` steps; the event
`A k` is "run `k` succeeds within the cutoff". The events `A k` are independent with
probability `s ≤ 1`. Run `k` is performed exactly when runs `0, …, k-1` all failed, and
it costs at most `τ` steps. The measure-theoretic statements need only `s ≤ 1`; at `s = 0`
the bound `τ / s` is `⊤` (or `0` when `τ = 0`) and holds trivially. The real-series identity
assumes `s ∈ (0, 1]`.

PROVED
* `RestartBound.measure_allFail` : the probability that the first `k` runs all fail is
  `(1 - s) ^ k`.
* `RestartBound.lintegral_numRuns` : the expected number of runs performed is exactly `1 / s`.
* `RestartBound.numRuns_eq_of_first_success` : if the first success is run `n`, the number of
  runs performed is `n + 1`.
* `RestartBound.lintegral_totalCost_le` : the expected total cost is at most `τ / s`, for any
  per-run costs bounded by `τ` (in particular when a failed run costs exactly `τ` and a
  successful run costs at most `τ`; the bound only uses `cost ≤ τ`). No measurability of the
  costs is assumed.
* `RestartBound.lintegral_totalCost_eq` : if every performed run costs exactly `τ`, the
  expected total cost equals `τ / s`.
* `RestartBound.hasSum_restart_series` : the real series
  `∑_{k ≥ 0} (1 - s)^k * s * (k + 1) * τ` sums to `τ / s` for `s ∈ (0, 1]`.
* `RestartBound.restart_bound_lt_top` : `τ / s` is finite for finite `τ` and `s > 0`.
* `RestartBound.heavy_tail_example` : a run time with `P(T = 2^k) = 2^{-(k+1)}` has infinite
  expectation, while restarting with cutoff `τ = 1` (success probability `s = P(T ≤ 1) = 1/2`)
  has expected cost at most `τ / s = 2`.
-/

open MeasureTheory ProbabilityTheory ENNReal Finset

namespace RestartBound

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The event that runs `0, …, k-1` all fail, i.e. run `k` is performed. -/
def allFail (A : ℕ → Set Ω) (k : ℕ) : Set Ω := ⋂ i ∈ range k, (A i)ᶜ

/-- Number of runs performed: the number of `k` such that runs `0, …, k-1` all failed. -/
noncomputable def numRuns (A : ℕ → Set Ω) (ω : Ω) : ℝ≥0∞ :=
  ∑' k, (allFail A k).indicator (fun _ => (1 : ℝ≥0∞)) ω

/-- Total cost: run `k` contributes `cost k ω` when it is performed. -/
noncomputable def totalCost (A : ℕ → Set Ω) (cost : ℕ → Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ∑' k, (allFail A k).indicator (cost k) ω

lemma measurableSet_allFail {A : ℕ → Set Ω} (hA : ∀ i, MeasurableSet (A i)) (k : ℕ) :
    MeasurableSet (allFail A k) :=
  Finset.measurableSet_biInter _ (fun i _ => (hA i).compl)

theorem measure_allFail {μ : Measure Ω} {A : ℕ → Set Ω} {s : ℝ≥0∞}
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ) (hs : ∀ i, μ (A i) = s) (k : ℕ) :
    μ (allFail A k) = (1 - s) ^ k := by
  have := hind.isProbabilityMeasure
  have h := (iIndepSet_iff A μ).1 hind (range k) (f := fun i => (A i)ᶜ)
    (fun i _ => (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)).compl)
  rw [allFail, h]
  simp [prob_compl_eq_one_sub (hA _), hs]

theorem lintegral_numRuns {μ : Measure Ω} {A : ℕ → Set Ω} {s : ℝ≥0∞}
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ) (hs : ∀ i, μ (A i) = s)
    (hs1 : s ≤ 1) :
    ∫⁻ ω, numRuns A ω ∂μ = s⁻¹ := by
  unfold numRuns
  rw [lintegral_tsum (fun k =>
    (measurable_const.indicator (measurableSet_allFail hA k)).aemeasurable)]
  simp_rw [lintegral_indicator_const (measurableSet_allFail hA _), one_mul,
    measure_allFail hA hind hs]
  rw [ENNReal.tsum_geometric, ENNReal.sub_sub_cancel one_ne_top hs1]

lemma measurable_numRuns {A : ℕ → Set Ω} (hA : ∀ i, MeasurableSet (A i)) :
    Measurable (numRuns A) :=
  Measurable.tsum (fun k => measurable_const.indicator (measurableSet_allFail hA k))

omit [MeasurableSpace Ω] in
theorem numRuns_eq_of_first_success {A : ℕ → Set Ω} {ω : Ω} {n : ℕ}
    (hn : ω ∈ A n) (hbefore : ∀ i < n, ω ∉ A i) :
    numRuns A ω = n + 1 := by
  unfold numRuns
  have hsupp : ∀ k ∉ range (n + 1),
      (allFail A k).indicator (fun _ => (1 : ℝ≥0∞)) ω = 0 := by
    intro k hk
    simp only [mem_range, not_lt] at hk
    apply Set.indicator_of_notMem
    simp only [allFail, Set.mem_iInter, mem_range, Set.mem_compl_iff, not_forall]
    exact ⟨n, by omega, not_not.2 hn⟩
  rw [tsum_eq_sum hsupp]
  have hin : ∀ k ∈ range (n + 1),
      (allFail A k).indicator (fun _ => (1 : ℝ≥0∞)) ω = 1 := by
    intro k hk
    simp only [mem_range] at hk
    apply Set.indicator_of_mem
    simp only [allFail, Set.mem_iInter, mem_range, Set.mem_compl_iff]
    intro i hi
    exact hbefore i (by omega)
  rw [Finset.sum_congr rfl hin]
  simp

theorem lintegral_totalCost_le {μ : Measure Ω} {A : ℕ → Set Ω} {s τ : ℝ≥0∞}
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ) (hs : ∀ i, μ (A i) = s)
    (hs1 : s ≤ 1) (cost : ℕ → Ω → ℝ≥0∞) (hcost : ∀ k ω, cost k ω ≤ τ) :
    ∫⁻ ω, totalCost A cost ω ∂μ ≤ τ / s := by
  have hpt : ∀ ω, totalCost A cost ω ≤ τ * numRuns A ω := by
    intro ω
    unfold totalCost numRuns
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum (fun k => ?_)
    by_cases hk : ω ∈ allFail A k
    · simp [Set.indicator_of_mem hk, hcost k ω]
    · simp [Set.indicator_of_notMem hk]
  calc ∫⁻ ω, totalCost A cost ω ∂μ ≤ ∫⁻ ω, τ * numRuns A ω ∂μ := lintegral_mono hpt
    _ = τ * ∫⁻ ω, numRuns A ω ∂μ := lintegral_const_mul _ (measurable_numRuns hA)
    _ = τ / s := by rw [lintegral_numRuns hA hind hs hs1, div_eq_mul_inv]

theorem lintegral_totalCost_eq {μ : Measure Ω} {A : ℕ → Set Ω} {s τ : ℝ≥0∞}
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ) (hs : ∀ i, μ (A i) = s)
    (hs1 : s ≤ 1) :
    ∫⁻ ω, totalCost A (fun _ _ => τ) ω ∂μ = τ / s := by
  have hpt : ∀ ω, totalCost A (fun _ _ => τ) ω = τ * numRuns A ω := by
    intro ω
    unfold totalCost numRuns
    rw [← ENNReal.tsum_mul_left]
    congr 1
    ext k
    by_cases hk : ω ∈ allFail A k
    · simp [Set.indicator_of_mem hk]
    · simp [Set.indicator_of_notMem hk]
  simp_rw [hpt]
  rw [lintegral_const_mul _ (measurable_numRuns hA), lintegral_numRuns hA hind hs hs1, div_eq_mul_inv]

theorem hasSum_restart_series {s τ : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    HasSum (fun k : ℕ => (1 - s) ^ k * s * ((k : ℝ) + 1) * τ) (τ / s) := by
  have hr : ‖(1 - s : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have h2 := hasSum_geometric_of_norm_lt_one hr
  have h3 := (h1.add h2).mul_left (s * τ)
  have hsne : s ≠ 0 := hs0.ne'
  convert h3 using 1
  · ext k; ring
  · have : (1 : ℝ) - (1 - s) = s := by ring
    rw [this]
    field_simp
    ring

theorem restart_bound_lt_top {s τ : ℝ≥0∞} (hτ : τ ≠ ⊤) (hs0 : 0 < s) : τ / s < ⊤ :=
  ENNReal.div_lt_top hτ hs0.ne'

theorem heavy_tail_example :
    (∑' k : ℕ, (2 : ℝ≥0∞) ^ k * (2 ^ (k + 1))⁻¹ = ⊤) ∧
      (∑' k : ℕ, ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ = 1) ∧
      ((∑' k : ℕ, if (2 : ℕ) ^ k ≤ 1 then ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ else 0) = 2⁻¹) ∧
      (1 : ℝ≥0∞) / 2⁻¹ = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : ∀ k : ℕ, (2 : ℝ≥0∞) ^ k * (2 ^ (k + 1))⁻¹ = 2⁻¹ := by
      intro k
      rw [pow_succ, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), ← mul_assoc,
        ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
    simp_rw [this]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (by simp)
  · simp_rw [ENNReal.inv_pow, pow_succ]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
      ENNReal.mul_inv_cancel (by simp) (by simp)]
  · rw [tsum_eq_single 0]
    · simp
    · intro k hk
      have : ¬ (2 : ℕ) ^ k ≤ 1 := by
        have : 2 ≤ 2 ^ k := Nat.le_self_pow hk 2
        omega
      simp [this]
  · simp

end RestartBound
