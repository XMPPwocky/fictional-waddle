import Mathlib

/-!
# Deadline by independent copies

PROVED
* `prob_some_finishes` : if events `A i` (copy `i` finishes by the deadline), indexed by a finite
  type of size `N`, are mutually independent and each has probability `f`, then the probability
  that at least one occurs is `1 - (1 - f)^N` (stated in `ℝ≥0∞`).
* `prob_some_finishes_real` : the same identity for the real-valued measure `μ.real`.
* `tendsto_one_sub_pow` : for `f ∈ (0,1]`, `1 - (1 - f)^N → 1` as `N → ∞`.
* `tendsto_prob_some_finishes` : for independent copies `A : ℕ → Set Ω` of probability `f ∈ (0,1]`,
  the probability that one of the first `N` finishes tends to `1`.
* `one_sub_pow_ge_iff` : for `f ∈ (0,1)` and `ε > 0`,
  `1 - ε ≤ 1 - (1 - f)^N ↔ log ε / log (1 - f) ≤ N` (the threshold is exact).
* `one_sub_pow_ge_of_le` : the forward direction, `N ≥ log ε / log (1 - f) → 1 - (1 - f)^N ≥ 1 - ε`.
* `prob_some_finishes_ge` : the same bound for the probability of the union of the first `N`
  independent copies.
* `one_sub_pow_eq_one_of_f_eq_one` : for `f = 1` a single copy suffices.

INTERPRETED
* "Copy `i` finishes by `τ`" is modelled as a measurable event `A i` in a probability space;
  independence of copies is `ProbabilityTheory.iIndepSet A μ`. The hypothesis `ε > 0` is needed:
  for `ε ≤ 0` the bound `≥ 1 - ε` is impossible when `f < 1`.
-/

namespace DeadlineByCopiesA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem prob_some_finishes [Fintype ι] {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i))
    (hind : iIndepSet A μ) {f : ℝ≥0∞} (hf : ∀ i, μ (A i) = f) :
    μ (⋃ i, A i) = 1 - (1 - f) ^ Fintype.card ι := by
  have := hind.isProbabilityMeasure
  have hI : iIndep (fun i ↦ MeasurableSpace.generateFrom {A i}) μ :=
    (iIndepSet_iff_iIndep _ _).1 hind
  have hc : μ (⋂ i, (A i)ᶜ) = ∏ i, μ ((A i)ᶜ) :=
    hI.meas_iInter (fun i ↦ (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)).compl)
  have hU : MeasurableSet (⋃ i, A i) := MeasurableSet.iUnion hA
  have h1 : μ ((⋃ i, A i)ᶜ) = (1 - f) ^ Fintype.card ι := by
    rw [Set.compl_iUnion, hc]
    simp_rw [prob_compl_eq_one_sub (hA _), hf]
    simp
  have h2 := prob_compl_eq_one_sub (μ := μ) hU.compl
  rw [compl_compl, h1] at h2
  exact h2

theorem prob_some_finishes_real [Fintype ι] {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i))
    (hind : iIndepSet A μ) {f : ℝ} (hf : ∀ i, μ.real (A i) = f) :
    μ.real (⋃ i, A i) = 1 - (1 - f) ^ Fintype.card ι := by
  have := hind.isProbabilityMeasure
  have hI : iIndep (fun i ↦ MeasurableSpace.generateFrom {A i}) μ :=
    (iIndepSet_iff_iIndep _ _).1 hind
  have hc : μ (⋂ i, (A i)ᶜ) = ∏ i, μ ((A i)ᶜ) :=
    hI.meas_iInter (fun i ↦ (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)).compl)
  have hU : MeasurableSet (⋃ i, A i) := MeasurableSet.iUnion hA
  have h1 : μ.real ((⋃ i, A i)ᶜ) = (1 - f) ^ Fintype.card ι := by
    rw [Set.compl_iUnion, measureReal_def, hc, ENNReal.toReal_prod]
    have : ∀ i, (μ ((A i)ᶜ)).toReal = 1 - f := by
      intro i
      rw [← measureReal_def, probReal_compl_eq_one_sub (hA i), hf]
    simp_rw [this]
    simp
  have h2 := probReal_compl_eq_one_sub (μ := μ) hU.compl
  rw [compl_compl, h1] at h2
  exact h2

theorem tendsto_one_sub_pow {f : ℝ} (hf0 : 0 < f) (hf1 : f ≤ 1) :
    Tendsto (fun N : ℕ ↦ 1 - (1 - f) ^ N) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ ↦ (1 - f) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h

theorem tendsto_prob_some_finishes {A : ℕ → Set Ω} (hA : ∀ i, MeasurableSet (A i))
    (hind : iIndepSet A μ) {f : ℝ} (hf0 : 0 < f) (hf1 : f ≤ 1) (hf : ∀ i, μ.real (A i) = f) :
    Tendsto (fun N : ℕ ↦ μ.real (⋃ i : Fin N, A i)) atTop (𝓝 1) := by
  have key : ∀ N : ℕ, μ.real (⋃ i : Fin N, A i) = 1 - (1 - f) ^ N := by
    intro N
    have hN : iIndepSet (fun i : Fin N ↦ A i) μ := hind.precomp Fin.val_injective
    simpa using prob_some_finishes_real (fun i : Fin N ↦ hA i) hN (fun i ↦ hf i)
  simp_rw [key]
  exact tendsto_one_sub_pow hf0 hf1

theorem one_sub_pow_ge_iff {f ε : ℝ} (hf0 : 0 < f) (hf1 : f < 1) (hε : 0 < ε) (N : ℕ) :
    1 - ε ≤ 1 - (1 - f) ^ N ↔ Real.log ε / Real.log (1 - f) ≤ N := by
  have hq0 : 0 < 1 - f := by linarith
  have hlog : Real.log (1 - f) < 0 := Real.log_neg hq0 (by linarith)
  have hpow : 0 < (1 - f) ^ N := pow_pos hq0 N
  rw [div_le_iff_of_neg hlog, sub_le_sub_iff_left, ← Real.log_le_log_iff hpow hε,
    Real.log_pow]

theorem one_sub_pow_ge_of_le {f ε : ℝ} (hf0 : 0 < f) (hf1 : f < 1) (hε : 0 < ε) {N : ℕ}
    (hN : Real.log ε / Real.log (1 - f) ≤ N) :
    1 - ε ≤ 1 - (1 - f) ^ N :=
  (one_sub_pow_ge_iff hf0 hf1 hε N).2 hN

theorem prob_some_finishes_ge {A : ℕ → Set Ω} (hA : ∀ i, MeasurableSet (A i))
    (hind : iIndepSet A μ) {f ε : ℝ} (hf0 : 0 < f) (hf1 : f < 1) (hε : 0 < ε)
    (hf : ∀ i, μ.real (A i) = f) {N : ℕ} (hN : Real.log ε / Real.log (1 - f) ≤ N) :
    1 - ε ≤ μ.real (⋃ i : Fin N, A i) := by
  have hN' : iIndepSet (fun i : Fin N ↦ A i) μ := hind.precomp Fin.val_injective
  have := prob_some_finishes_real (fun i : Fin N ↦ hA i) hN' (fun i ↦ hf i)
  rw [Fintype.card_fin] at this
  rw [this]
  exact one_sub_pow_ge_of_le hf0 hf1 hε hN

theorem one_sub_pow_eq_one_of_f_eq_one {N : ℕ} (hN : 1 ≤ N) :
    1 - (1 - (1 : ℝ)) ^ N = 1 := by
  rw [sub_self, zero_pow (by omega), sub_zero]

end DeadlineByCopiesA
