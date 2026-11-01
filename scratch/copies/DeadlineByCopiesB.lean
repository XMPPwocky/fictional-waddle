import Mathlib

/-!
# Deadline success by running independent copies

A single run finishes by the deadline `τ` with probability `f`. Running `N` independent
copies, the probability that at least one finishes by `τ` is `1 - (1 - f) ^ N`.

PROVED
* `prob_some_copy_finishes`: for `N` independent measurable events `A i` (copy `i` finishes
  by `τ`) on a probability space, each of probability `f`, the probability of their union is
  `1 - (1 - f) ^ N`.
* `prob_some_copy_finishes_seq`: the same for the first `N` events of an independent sequence.
* `tendsto_one_sub_pow`: for `0 < f ≤ 1`, `1 - (1 - f) ^ N → 1` as `N → ∞`.
* `tendsto_prob_some_copy_finishes`: for an independent sequence of finish events of common
  probability `f ∈ (0,1]`, the probability that one of the first `N` finishes tends to `1`.
* `one_sub_pow_ge_of_copies`: for `0 < f < 1` and `0 < ε`, if `N ≥ log ε / log (1 - f)` then
  `1 - (1 - f) ^ N ≥ 1 - ε`.
* `pow_le_iff`: for `0 < f < 1` and `0 < ε`, `(1 - f) ^ N ≤ ε` iff `N ≥ log ε / log (1 - f)`.
* `one_sub_pow_ge_iff`: for `0 < f < 1` and `0 < ε`, `1 - (1 - f) ^ N ≥ 1 - ε` holds exactly
  when `N ≥ log ε / log (1 - f)`; the copy count is therefore sharp.
* `prob_some_copy_finishes_ge`: the probabilistic form of the bound: with
  `N ≥ log ε / log (1 - f)` independent copies, the union has probability at least `1 - ε`.
* `one_sub_pow_eq_one_of_f_eq_one`: for `f = 1` and `N ≥ 1` the success probability is `1`.
* `one_sub_pow_monotone`: for `0 ≤ f ≤ 1` the success probability is monotone in `N`.

INTERPRETED
* "Copy `i` finishes by `τ`" is modelled as a measurable event `A i`; "independent copies" is
  `ProbabilityTheory.iIndepSet A μ`; probabilities are `μ.real`.
* The hypothesis `0 < ε` is required: in Lean `Real.log 0 = 0`, so for `ε = 0` the threshold
  would be `0` and the bound would be false.
-/

namespace DeadlineByCopiesB

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Probability that at least one of `N` independent copies finishes by the deadline. -/
theorem prob_some_copy_finishes {N : ℕ} (A : Fin N → Set Ω) (f : ℝ)
    (hmeas : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (hf : ∀ i, μ.real (A i) = f) :
    μ.real (⋃ i, A i) = 1 - (1 - f) ^ N := by
  have : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  have hI : iIndep (fun i ↦ MeasurableSpace.generateFrom {A i}) μ :=
    (iIndepSet_iff_iIndep _ _).1 hind
  have hc : ∀ i, MeasurableSet[MeasurableSpace.generateFrom {A i}] (A i)ᶜ := fun i ↦
    (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)).compl
  have hprod : μ (⋂ i, (A i)ᶜ) = ∏ i, μ ((A i)ᶜ) := hI.meas_iInter hc
  have hprodR : μ.real (⋂ i, (A i)ᶜ) = ∏ i, μ.real ((A i)ᶜ) := by
    simp only [measureReal_def, hprod, ENNReal.toReal_prod]
  have hU : MeasurableSet (⋃ i, A i) := MeasurableSet.iUnion hmeas
  have : μ.real (⋃ i, A i) = 1 - μ.real ((⋃ i, A i)ᶜ) := by
    rw [probReal_compl_eq_one_sub hU]; ring
  rw [this, Set.compl_iUnion, hprodR]
  congr 1
  rw [Finset.prod_congr rfl (fun i _ ↦ by rw [probReal_compl_eq_one_sub (hmeas i), hf i])]
  simp

/-- The same statement for the first `N` events of an independent sequence of copies. -/
theorem prob_some_copy_finishes_seq (A : ℕ → Set Ω) (f : ℝ)
    (hmeas : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (hf : ∀ i, μ.real (A i) = f) (N : ℕ) :
    μ.real (⋃ i : Fin N, A i) = 1 - (1 - f) ^ N :=
  prob_some_copy_finishes (fun i : Fin N ↦ A i) f (fun i ↦ hmeas i)
    (hind.precomp Fin.val_injective) (fun i ↦ hf i)

/-- For `0 < f ≤ 1`, `1 - (1 - f) ^ N → 1`. -/
theorem tendsto_one_sub_pow {f : ℝ} (hf0 : 0 < f) (hf1 : f ≤ 1) :
    Tendsto (fun N : ℕ ↦ 1 - (1 - f) ^ N) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ ↦ (1 - f) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h

/-- The probability that one of the first `N` independent copies finishes tends to `1`. -/
theorem tendsto_prob_some_copy_finishes (A : ℕ → Set Ω) {f : ℝ}
    (hmeas : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (hf : ∀ i, μ.real (A i) = f) (hf0 : 0 < f) (hf1 : f ≤ 1) :
    Tendsto (fun N : ℕ ↦ μ.real (⋃ i : Fin N, A i)) atTop (𝓝 1) := by
  simp_rw [prob_some_copy_finishes_seq A f hmeas hind hf]
  exact tendsto_one_sub_pow hf0 hf1

/-- Exact characterisation: `(1 - f) ^ N ≤ ε` iff `N ≥ log ε / log (1 - f)`. -/
theorem pow_le_iff {f ε : ℝ} (hf0 : 0 < f) (hf1 : f < 1) (hε : 0 < ε) (N : ℕ) :
    (1 - f) ^ N ≤ ε ↔ Real.log ε / Real.log (1 - f) ≤ N := by
  have hq0 : 0 < 1 - f := by linarith
  have hlog : Real.log (1 - f) < 0 := Real.log_neg hq0 (by linarith)
  have hpos : 0 < (1 - f) ^ N := pow_pos hq0 N
  rw [div_le_iff_of_neg hlog, ← Real.log_le_log_iff hpos hε, Real.log_pow]

/-- Sharp copy count: `1 - (1 - f) ^ N ≥ 1 - ε` iff `N ≥ log ε / log (1 - f)`. -/
theorem one_sub_pow_ge_iff {f ε : ℝ} (hf0 : 0 < f) (hf1 : f < 1) (hε : 0 < ε) (N : ℕ) :
    1 - ε ≤ 1 - (1 - f) ^ N ↔ Real.log ε / Real.log (1 - f) ≤ N := by
  rw [← pow_le_iff hf0 hf1 hε N]
  constructor <;> intro h <;> linarith

/-- With `N ≥ log ε / log (1 - f)` copies the success probability is at least `1 - ε`. -/
theorem one_sub_pow_ge_of_copies {f ε : ℝ} (hf0 : 0 < f) (hf1 : f < 1) (hε : 0 < ε) {N : ℕ}
    (hN : Real.log ε / Real.log (1 - f) ≤ N) :
    1 - ε ≤ 1 - (1 - f) ^ N :=
  (one_sub_pow_ge_iff hf0 hf1 hε N).2 hN

/-- Probabilistic form of the copy-count bound. -/
theorem prob_some_copy_finishes_ge {N : ℕ} (A : Fin N → Set Ω) {f ε : ℝ}
    (hmeas : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (hf : ∀ i, μ.real (A i) = f) (hf0 : 0 < f) (hf1 : f < 1) (hε : 0 < ε)
    (hN : Real.log ε / Real.log (1 - f) ≤ N) :
    1 - ε ≤ μ.real (⋃ i, A i) := by
  rw [prob_some_copy_finishes A f hmeas hind hf]
  exact one_sub_pow_ge_of_copies hf0 hf1 hε hN

/-- When a single run always finishes (`f = 1`), one copy suffices. -/
theorem one_sub_pow_eq_one_of_f_eq_one {N : ℕ} (hN : 1 ≤ N) :
    1 - (1 - (1 : ℝ)) ^ N = 1 := by
  rw [sub_self, zero_pow (by omega), sub_zero]

/-- The success probability `1 - (1 - f) ^ N` is monotone in `N` for `0 ≤ f ≤ 1`. -/
theorem one_sub_pow_monotone {f : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    Monotone (fun N : ℕ ↦ 1 - (1 - f) ^ N) := by
  intro m n hmn
  have : (1 - f) ^ n ≤ (1 - f) ^ m := pow_le_pow_of_le_one (by linarith) (by linarith) hmn
  simp only
  linarith

end DeadlineByCopiesB
