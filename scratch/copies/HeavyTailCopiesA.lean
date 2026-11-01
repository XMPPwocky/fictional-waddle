import Mathlib

/-!
# HeavyTailCopiesA: minimum of independent Pareto copies

PROVED
* `rpow_tail_pow`: for `t ≥ 0`, `(t ^ (-α)) ^ N = t ^ (-(N * α))` (the algebraic tail identity).
* `min_tail`: if `X 0, …, X (N-1)` are independent and each satisfies `P(X i > t) = t ^ (-α)`
  for `t ≥ 1`, then the minimum satisfies `P(min > t) = t ^ (-(N * α))` for `t ≥ 1`.
* `min_tail_eq_one_of_le_one`: under the same hypotheses (`N ≥ 1`), `P(min > t) = 1` for `t ≤ 1`.
* `integrableOn_tail_iff`: `t ↦ t ^ (-(N * α))` is integrable on `(1, ∞)` iff `1 < N * α`.
* `integral_tail`: if `1 < N * α`, then `∫_1^∞ t ^ (-(N * α)) dt = 1 / (N * α - 1)`.
* `lintegral_tail_lt_top_iff`: the Lebesgue integral of the tail over `(1, ∞)` is finite
  iff `1 < N * α`.
* `lintegral_min_eq`: the expectation of the minimum equals `1 + ∫_1^∞ t ^ (-(N * α)) dt`
  (derived from the layer-cake formula, not assumed).
* `lintegral_min_lt_top_iff`: the expectation of the minimum is finite iff `1 < N * α`.
* `lintegral_min_eq_of_lt`: if `1 < N * α`, the expectation equals `N * α / (N * α - 1)`.
* `lintegral_single_eq_top`: with `α ≤ 1`, a single run (`N = 1`) has infinite expectation.
* `exists_copies_finite`: for every `α > 0` there is `N₀` such that for all `N ≥ N₀` the
  expected minimum of `N` independent copies is finite.
* `heavy_tail_rescue`: with `0 < α ≤ 1`, one run has infinite expected time while for some
  `N` the minimum of `N` copies has finite expected time.

INTERPRETED
* "Expected time" is the Lebesgue integral `∫⁻ ω, ENNReal.ofReal (T ω) ∂μ` (values in `[0, ∞]`),
  so "infinite expectation" means this equals `⊤`.
* "Independent copies" means `iIndepFun X μ` on a probability space, with each `X i`
  measurable and satisfying the Pareto tail law for `t ≥ 1`; identical distribution is not
  needed beyond the common tail.
* The minimum is `Finset.univ.inf' _ (fun i => X i ω)` over `Fin N` with `N ≥ 1`.
-/

open MeasureTheory ProbabilityTheory Set

namespace HeavyTailCopiesA

theorem rpow_tail_pow {t : ℝ} (ht : 0 ≤ t) (α : ℝ) (N : ℕ) :
    (t ^ (-α)) ^ N = t ^ (-(N * α)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  ring_nf

theorem integrableOn_tail_iff (N : ℕ) (α : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (-(N * α))) (Ioi 1) ↔ 1 < N * α := by
  rw [integrableOn_Ioi_rpow_iff zero_lt_one]
  constructor <;> intro h <;> linarith

theorem integral_tail {N : ℕ} {α : ℝ} (h : 1 < N * α) :
    ∫ t in Ioi (1 : ℝ), t ^ (-(N * α)) = 1 / (N * α - 1) := by
  rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
  have : (N : ℝ) * α - 1 ≠ 0 := by linarith
  have : -((N : ℝ) * α) + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem lintegral_tail_lt_top_iff (N : ℕ) (α : ℝ) :
    ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-(N * α))) < ⊤ ↔ 1 < N * α := by
  rw [← integrableOn_tail_iff, IntegrableOn, ← lintegral_ofReal_ne_top_iff_integrable,
    lt_top_iff_ne_top]
  · exact (Measurable.pow_const measurable_id _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (zero_le_one.trans (le_of_lt ht)) _

theorem lintegral_tail_eq_of_lt {N : ℕ} {α : ℝ} (h : 1 < N * α) :
    ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-(N * α))) = ENNReal.ofReal (1 / (N * α - 1)) := by
  rw [← integral_tail h, ofReal_integral_eq_lintegral_ofReal]
  · exact (integrableOn_tail_iff N α).2 h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (zero_le_one.trans (le_of_lt ht)) _

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Pareto tail law on `[1, ∞)` with index `α`. -/
def ParetoTail (μ : Measure Ω) (X : Ω → ℝ) (α : ℝ) : Prop :=
  ∀ t : ℝ, 1 ≤ t → μ {ω | t < X ω} = ENNReal.ofReal (t ^ (-α))

/-- Minimum of `N ≥ 1` real random variables. -/
noncomputable def minCopies {N : ℕ} [NeZero N] (X : Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => X i ω)

omit [MeasurableSpace Ω] in
theorem setOf_lt_minCopies {N : ℕ} [NeZero N] (X : Fin N → Ω → ℝ) (t : ℝ) :
    {ω | t < minCopies X ω} = ⋂ i ∈ (Finset.univ : Finset (Fin N)), X i ⁻¹' Ioi t := by
  ext ω
  simp [minCopies, Finset.lt_inf'_iff]

theorem measurable_minCopies {N : ℕ} [NeZero N] (X : Fin N → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) : Measurable (minCopies X) := by
  have : minCopies X = Finset.univ.inf' Finset.univ_nonempty X := by
    funext ω
    simp [minCopies, Finset.inf'_apply]
  rw [this]
  exact Finset.inf'_induction _ _ (fun _ hf _ hg => hf.inf hg) (fun i _ => hX i)

theorem min_tail {N : ℕ} [NeZero N] {α : ℝ} (X : Fin N → Ω → ℝ)
    (hind : iIndepFun X μ) (hP : ∀ i, ParetoTail μ (X i) α) {t : ℝ} (ht : 1 ≤ t) :
    μ {ω | t < minCopies X ω} = ENNReal.ofReal (t ^ (-(N * α))) := by
  rw [setOf_lt_minCopies, hind.measure_inter_preimage_eq_mul _ (fun _ _ => measurableSet_Ioi)]
  have h1 : ∀ i, μ (X i ⁻¹' Ioi t) = ENNReal.ofReal (t ^ (-α)) := fun i => hP i t ht
  simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg (zero_le_one.trans ht) _),
    rpow_tail_pow (zero_le_one.trans ht)]

theorem min_tail_eq_one_of_le_one [IsProbabilityMeasure μ] {N : ℕ} [NeZero N] {α : ℝ}
    (X : Fin N → Ω → ℝ) (hind : iIndepFun X μ) (hP : ∀ i, ParetoTail μ (X i) α)
    {t : ℝ} (ht : t ≤ 1) :
    μ {ω | t < minCopies X ω} = 1 := by
  have h1 : μ {ω | 1 < minCopies X ω} = 1 := by
    rw [min_tail X hind hP le_rfl, Real.one_rpow, ENNReal.ofReal_one]
  refine le_antisymm prob_le_one ?_
  rw [← h1]
  exact measure_mono (fun ω (hω : 1 < minCopies X ω) => show t < minCopies X ω by linarith)

theorem lintegral_min_eq [IsProbabilityMeasure μ] {N : ℕ} [NeZero N] {α : ℝ}
    (X : Fin N → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hP : ∀ i, ParetoTail μ (X i) α) :
    ∫⁻ ω, ENNReal.ofReal (minCopies X ω) ∂μ
      = 1 + ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-(N * α))) := by
  have hm := measurable_minCopies X hX
  have hnn : 0 ≤ᵐ[μ] minCopies X := by
    have hs : MeasurableSet {ω | 1 < minCopies X ω} := measurableSet_lt measurable_const hm
    have h1 : μ {ω | 1 < minCopies X ω} = 1 := by
      rw [min_tail X hind hP le_rfl, Real.one_rpow, ENNReal.ofReal_one]
    have h0 : μ {ω | 1 < minCopies X ω}ᶜ = 0 := (prob_compl_eq_zero_iff hs).2 h1
    have hae : ∀ᵐ ω ∂μ, 1 < minCopies X ω := by
      rw [ae_iff]
      simpa [Set.compl_def] using h0
    filter_upwards [hae] with ω hω
    simp only [Pi.zero_apply]
    linarith
  rw [lintegral_eq_lintegral_meas_lt μ hnn hm.aemeasurable,
    ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
  congr 1
  · rw [setLIntegral_congr_fun measurableSet_Ioc
      (g := fun _ => (1 : ENNReal)) (fun t ht => min_tail_eq_one_of_le_one X hind hP ht.2)]
    simp
  · exact setLIntegral_congr_fun measurableSet_Ioi
      (fun t ht => min_tail X hind hP (le_of_lt ht))

theorem lintegral_min_lt_top_iff [IsProbabilityMeasure μ] {N : ℕ} [NeZero N] {α : ℝ}
    (X : Fin N → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hP : ∀ i, ParetoTail μ (X i) α) :
    ∫⁻ ω, ENNReal.ofReal (minCopies X ω) ∂μ < ⊤ ↔ 1 < N * α := by
  rw [lintegral_min_eq X hX hind hP, ← lintegral_tail_lt_top_iff N α, ENNReal.add_lt_top]
  simp

theorem lintegral_min_eq_of_lt [IsProbabilityMeasure μ] {N : ℕ} [NeZero N] {α : ℝ}
    (X : Fin N → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hP : ∀ i, ParetoTail μ (X i) α) (h : 1 < N * α) :
    ∫⁻ ω, ENNReal.ofReal (minCopies X ω) ∂μ = ENNReal.ofReal (N * α / (N * α - 1)) := by
  have hpos : 0 < (N : ℝ) * α - 1 := by linarith
  rw [lintegral_min_eq X hX hind hP, lintegral_tail_eq_of_lt h, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (by positivity)]
  congr 1
  field_simp
  ring

theorem lintegral_single_eq_top [IsProbabilityMeasure μ] {α : ℝ} (X : Ω → ℝ)
    (hX : Measurable X) (hP : ParetoTail μ X α) (hα : α ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ = ⊤ := by
  have hind : iIndepFun (fun _ : Fin 1 => X) μ := iIndepFun.of_subsingleton
  have h := lintegral_min_lt_top_iff (fun _ : Fin 1 => X) (fun _ => hX) hind (fun _ => hP)
  have hmin : minCopies (fun _ : Fin 1 => X) = X := by
    funext ω
    simp [minCopies]
  rw [hmin] at h
  rw [← not_lt_top_iff, h]
  simp only [Nat.cast_one, one_mul]
  linarith

theorem exists_copies_finite {α : ℝ} (hα : 0 < α) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → 1 < N * α := by
  refine ⟨⌈1 / α⌉₊ + 1, Nat.succ_pos _, fun N hN => ?_⟩
  have h1 : 1 / α < (⌈1 / α⌉₊ + 1 : ℕ) := by
    push_cast
    exact (Nat.le_ceil _).trans_lt (lt_add_one _)
  have h2 : ((⌈1 / α⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  have h3 : 1 / α < N := h1.trans_le h2
  rw [div_lt_iff₀ hα] at h3
  exact h3

theorem heavy_tail_rescue [IsProbabilityMeasure μ] {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (Y : Ω → ℝ) (hY : Measurable Y) (hPY : ParetoTail μ Y α) :
    ∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ = ⊤ ∧
      ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] (X : Fin N → Ω → ℝ),
        (∀ i, Measurable (X i)) → iIndepFun X μ → (∀ i, ParetoTail μ (X i) α) →
          ∫⁻ ω, ENNReal.ofReal (minCopies X ω) ∂μ < ⊤ := by
  refine ⟨lintegral_single_eq_top Y hY hPY hα1, ?_⟩
  obtain ⟨N₀, hN₀, hN⟩ := exists_copies_finite hα0
  exact ⟨N₀, hN₀, fun N hle _ X hX hind hP =>
    (lintegral_min_lt_top_iff X hX hind hP).2 (hN N hle)⟩

end HeavyTailCopiesA
