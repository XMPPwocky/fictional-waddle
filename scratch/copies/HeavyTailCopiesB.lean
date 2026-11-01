import Mathlib

/-!
# Pareto tails: the minimum of independent copies

Setting: `T i` (for `i : Fin N`, `N = n + 1 ≥ 1`) are independent real random variables on a
probability space, each with the Pareto tail `P(T i > t) = t^(-α)` for every `t ≥ 1`, `α > 0`.
`minT T ω` is the minimum of the `T i ω`.

PROVED
* `rpow_pow_eq` : for `t ≥ 0`, `(t^(-α))^N = t^(-(N α))` (the arithmetic of the tail).
* `minT_tail` : `P(min_i T i > t) = t^(-(N α))` for all `t ≥ 1` (independence gives the product).
* `minT_tail_of_le_one` : `P(min_i T i > t) = 1` for all `t ≤ 1`.
* `integrableOn_tail_iff` : `t ↦ t^(-(N α))` is integrable on `(1, ∞)` iff `1 < N α`.
* `integral_tail` : if `1 < N α` then `∫_1^∞ t^(-(N α)) dt = 1 / (N α - 1)`.
* `formula_value` : if `1 < N α` then `1 + ∫_1^∞ t^(-(N α)) dt = N α / (N α - 1)`.
* `lintegral_tail_lt_top_iff` : the Lebesgue integral `∫⁻_1^∞ t^(-(N α)) dt` is finite iff
  `1 < N α`.
* `expectation_eq` : the actual expectation of the minimum satisfies
  `E[min] = 1 + ∫⁻_1^∞ t^(-(N α)) dt` (layer-cake formula; equality in `ℝ≥0∞`).
* `expectation_lt_top_iff` : `E[min] < ∞ ↔ 1 < N α`.
* `expectation_eq_of_lt` : if `1 < N α` then `E[min] = N α / (N α - 1)`.
* `single_run_infinite`, `single_run_infinite'` : with one copy (`N = 1`) and `α ≤ 1`,
  `E[T] = ∞`.
* `minT_pos_ae`, `measurable_minT` : the minimum is a.s. nonnegative and measurable.
* `enough_copies_finite` : for every `α > 0` and every `N` with `1 < N α` (equivalently
  `N > 1/α`), `E[min] < ∞`; and such `N` exist (`exists_enough_copies`).
* `heavy_tail_copies` : summary: if `α ≤ 1` a single run has infinite expectation, while for
  every `N > 1/α` the minimum of `N` independent runs has finite expectation `Nα/(Nα-1)`.

INTERPRETED
* "Expectation" is the Lebesgue integral `∫⁻ ω, ENNReal.ofReal (minT T ω) ∂μ` (values in
  `ℝ≥0∞`, so "infinite expected time" is the value `∞`). The informal formula
  `1 + ∫_1^∞ t^(-Nα) dt` is proved equal to this expectation, not assumed.
-/

namespace HeavyTailCopiesB

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

/-- `(t^(-α))^N = t^(-(N α))` for `t ≥ 0`. -/
theorem rpow_pow_eq {t : ℝ} (ht : 0 ≤ t) (α : ℝ) (N : ℕ) :
    (t ^ (-α)) ^ N = t ^ (-((N : ℝ) * α)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  congr 1
  ring

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {n : ℕ}

/-- The minimum of finitely many (at least one) real random variables. -/
noncomputable def minT (T : Fin (n + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => T i ω)

omit [MeasurableSpace Ω] in
theorem lt_minT_iff (T : Fin (n + 1) → Ω → ℝ) (ω : Ω) (t : ℝ) :
    t < minT T ω ↔ ∀ i, t < T i ω := by
  simp [minT, Finset.lt_inf'_iff]

omit [MeasurableSpace Ω] in
theorem setOf_lt_minT (T : Fin (n + 1) → Ω → ℝ) (t : ℝ) :
    {ω | t < minT T ω} = ⋂ i, T i ⁻¹' Ioi t := by
  ext ω
  simp [lt_minT_iff]

theorem measurable_minT {T : Fin (n + 1) → Ω → ℝ} (hT : ∀ i, Measurable (T i)) :
    Measurable (minT T) := by
  refine measurable_of_Ioi fun t => ?_
  have : minT T ⁻¹' Ioi t = ⋂ i, T i ⁻¹' Ioi t := setOf_lt_minT T t
  rw [this]
  exact MeasurableSet.iInter fun i => hT i measurableSet_Ioi

omit [IsProbabilityMeasure μ] in
/-- The tail of the minimum of `N = n + 1` independent Pareto(α) copies is `t^(-(N α))`. -/
theorem minT_tail {T : Fin (n + 1) → Ω → ℝ} {α : ℝ} (hind : iIndepFun T μ)
    (htail : ∀ i, ∀ t : ℝ, 1 ≤ t → μ {ω | t < T i ω} = ENNReal.ofReal (t ^ (-α)))
    {t : ℝ} (ht : 1 ≤ t) :
    μ {ω | t < minT T ω} = ENNReal.ofReal (t ^ (-(((n + 1 : ℕ) : ℝ) * α))) := by
  rw [setOf_lt_minT, hind.meas_iInter (fun i => ⟨Ioi t, measurableSet_Ioi, rfl⟩)]
  have h1 : ∀ i, μ (T i ⁻¹' Ioi t) = ENNReal.ofReal (t ^ (-α)) := fun i => htail i t ht
  simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg (by linarith) _), rpow_pow_eq (by linarith)]

theorem minT_tail_of_le_one {T : Fin (n + 1) → Ω → ℝ} {α : ℝ} (hind : iIndepFun T μ)
    (htail : ∀ i, ∀ t : ℝ, 1 ≤ t → μ {ω | t < T i ω} = ENNReal.ofReal (t ^ (-α)))
    {t : ℝ} (ht : t ≤ 1) :
    μ {ω | t < minT T ω} = 1 := by
  have h1 : μ {ω | (1 : ℝ) < minT T ω} = 1 := by
    rw [minT_tail hind htail le_rfl]
    simp
  refine le_antisymm prob_le_one ?_
  rw [← h1]
  exact measure_mono fun ω (hω : 1 < minT T ω) => show t < minT T ω by linarith

theorem minT_pos_ae {T : Fin (n + 1) → Ω → ℝ} {α : ℝ} (hind : iIndepFun T μ)
    (hT : ∀ i, Measurable (T i))
    (htail : ∀ i, ∀ t : ℝ, 1 ≤ t → μ {ω | t < T i ω} = ENNReal.ofReal (t ^ (-α))) :
    0 ≤ᵐ[μ] minT T := by
  have h1 : μ {ω | (0 : ℝ) < minT T ω} = 1 := minT_tail_of_le_one hind htail zero_le_one
  have hm : MeasurableSet {ω | (0 : ℝ) < minT T ω} := measurable_minT hT measurableSet_Ioi
  have h0 : μ {ω | (0 : ℝ) < minT T ω}ᶜ = 0 := by
    rw [prob_compl_eq_one_sub hm, h1, tsub_self]
  rw [Filter.EventuallyLE, ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h0
  have h' : minT T ω < 0 := by simpa using hω
  exact fun hh => lt_asymm (show (0 : ℝ) < minT T ω from hh) h'

end Probability

section Integrals

/-- `t ↦ t^(-(N α))` is integrable on `(1, ∞)` iff `1 < N α`. -/
theorem integrableOn_tail_iff (β : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (-β)) (Ioi 1) ↔ 1 < β := by
  rw [integrableOn_Ioi_rpow_iff zero_lt_one]
  constructor <;> intro h <;> linarith

theorem integral_tail {β : ℝ} (hβ : 1 < β) :
    ∫ t in Ioi (1 : ℝ), t ^ (-β) = 1 / (β - 1) := by
  rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
  have : -β + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem formula_value {β : ℝ} (hβ : 1 < β) :
    1 + ∫ t in Ioi (1 : ℝ), t ^ (-β) = β / (β - 1) := by
  rw [integral_tail hβ]
  have : β - 1 ≠ 0 := by linarith
  field_simp
  ring

theorem tail_nonneg_ae (β : ℝ) :
    0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] fun t : ℝ => t ^ (-β) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _

theorem lintegral_tail_lt_top_iff (β : ℝ) :
    (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-β))) < ∞ ↔ 1 < β := by
  rw [← integrableOn_tail_iff β, IntegrableOn, Integrable,
    hasFiniteIntegral_iff_ofReal (tail_nonneg_ae β)]
  have : AEStronglyMeasurable (fun t : ℝ => t ^ (-β)) (volume.restrict (Ioi (1 : ℝ))) :=
    (Measurable.pow_const measurable_id _).aestronglyMeasurable
  simp [this]

theorem lintegral_tail_eq {β : ℝ} (hβ : 1 < β) :
    (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-β))) = ENNReal.ofReal (1 / (β - 1)) := by
  rw [← integral_tail hβ, ofReal_integral_eq_lintegral_ofReal
    ((integrableOn_tail_iff β).2 hβ) (tail_nonneg_ae β)]

end Integrals

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {n : ℕ}

/-- Layer-cake: `E[min] = 1 + ∫⁻_1^∞ t^(-(N α)) dt`. -/
theorem expectation_eq {T : Fin (n + 1) → Ω → ℝ} {α : ℝ} (hind : iIndepFun T μ)
    (hT : ∀ i, Measurable (T i))
    (htail : ∀ i, ∀ t : ℝ, 1 ≤ t → μ {ω | t < T i ω} = ENNReal.ofReal (t ^ (-α))) :
    ∫⁻ ω, ENNReal.ofReal (minT T ω) ∂μ =
      1 + ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-(((n + 1 : ℕ) : ℝ) * α))) := by
  rw [lintegral_eq_lintegral_meas_lt μ (minT_pos_ae hind hT htail)
    (measurable_minT hT).aemeasurable]
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi_same)]
  congr 1
  · rw [setLIntegral_congr_fun measurableSet_Ioc
      (g := fun _ => (1 : ℝ≥0∞)) (fun t ht => minT_tail_of_le_one hind htail ht.2)]
    simp
  · exact setLIntegral_congr_fun measurableSet_Ioi
      (fun t ht => minT_tail hind htail (le_of_lt ht))

theorem expectation_lt_top_iff {T : Fin (n + 1) → Ω → ℝ} {α : ℝ} (hind : iIndepFun T μ)
    (hT : ∀ i, Measurable (T i))
    (htail : ∀ i, ∀ t : ℝ, 1 ≤ t → μ {ω | t < T i ω} = ENNReal.ofReal (t ^ (-α))) :
    ∫⁻ ω, ENNReal.ofReal (minT T ω) ∂μ < ∞ ↔ 1 < ((n + 1 : ℕ) : ℝ) * α := by
  rw [expectation_eq hind hT htail, ENNReal.add_lt_top, lintegral_tail_lt_top_iff]
  simp

theorem expectation_eq_of_lt {T : Fin (n + 1) → Ω → ℝ} {α : ℝ} (hind : iIndepFun T μ)
    (hT : ∀ i, Measurable (T i))
    (htail : ∀ i, ∀ t : ℝ, 1 ≤ t → μ {ω | t < T i ω} = ENNReal.ofReal (t ^ (-α)))
    (h : 1 < ((n + 1 : ℕ) : ℝ) * α) :
    ∫⁻ ω, ENNReal.ofReal (minT T ω) ∂μ =
      ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * α / (((n + 1 : ℕ) : ℝ) * α - 1)) := by
  rw [expectation_eq hind hT htail, lintegral_tail_eq h]
  have hpos : 0 < ((n + 1 : ℕ) : ℝ) * α - 1 := by linarith
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (div_nonneg zero_le_one hpos.le)]
  congr 1
  field_simp
  ring

/-- One run with `α ≤ 1` has infinite expected time. -/
theorem single_run_infinite {T : Fin 1 → Ω → ℝ} {α : ℝ} (hind : iIndepFun T μ)
    (hT : ∀ i, Measurable (T i))
    (htail : ∀ i, ∀ t : ℝ, 1 ≤ t → μ {ω | t < T i ω} = ENNReal.ofReal (t ^ (-α)))
    (hα : α ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (minT T ω) ∂μ = ∞ := by
  by_contra hne
  have h := (expectation_lt_top_iff (n := 0) hind hT htail).1 (lt_top_iff_ne_top.2 hne)
  norm_num at h
  linarith

theorem single_run_infinite' {X : Ω → ℝ} {α : ℝ} (hX : Measurable X)
    (htail : ∀ t : ℝ, 1 ≤ t → μ {ω | t < X ω} = ENNReal.ofReal (t ^ (-α)))
    (hα : α ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ = ∞ := by
  have hmin : ∀ ω, minT (fun _ : Fin 1 => X) ω = X ω := fun ω => by simp [minT]
  have := single_run_infinite (μ := μ) (T := fun _ : Fin 1 => X)
    (iIndepFun.of_subsingleton) (fun _ => hX) (fun _ => htail) hα
  simpa [hmin] using this

theorem exists_enough_copies {α : ℝ} (hα : 0 < α) : ∃ N : ℕ, 1 < (N : ℝ) * α := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / α)
  exact ⟨N, by rwa [div_lt_iff₀ hα] at hN⟩

theorem enough_copies_finite {T : Fin (n + 1) → Ω → ℝ} {α : ℝ} (hα : 0 < α)
    (hind : iIndepFun T μ) (hT : ∀ i, Measurable (T i))
    (htail : ∀ i, ∀ t : ℝ, 1 ≤ t → μ {ω | t < T i ω} = ENNReal.ofReal (t ^ (-α)))
    (hN : 1 / α < ((n + 1 : ℕ) : ℝ)) :
    ∫⁻ ω, ENNReal.ofReal (minT T ω) ∂μ < ∞ := by
  rw [expectation_lt_top_iff hind hT htail]
  rwa [div_lt_iff₀ hα] at hN

/-- Summary: one heavy-tailed run (`α ≤ 1`) has infinite expectation; the minimum of any
`N > 1/α` independent runs has finite expectation `N α / (N α - 1)`. -/
theorem heavy_tail_copies {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∀ X : Ω → ℝ, Measurable X →
        (∀ t : ℝ, 1 ≤ t → μ {ω | t < X ω} = ENNReal.ofReal (t ^ (-α))) →
        ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ = ∞) ∧
    (∃ N : ℕ, 1 < (N : ℝ) * α) ∧
    (∀ (m : ℕ) (T : Fin (m + 1) → Ω → ℝ), iIndepFun T μ → (∀ i, Measurable (T i)) →
        (∀ i, ∀ t : ℝ, 1 ≤ t → μ {ω | t < T i ω} = ENNReal.ofReal (t ^ (-α))) →
        1 / α < ((m + 1 : ℕ) : ℝ) →
        ∫⁻ ω, ENNReal.ofReal (minT T ω) ∂μ =
          ENNReal.ofReal (((m + 1 : ℕ) : ℝ) * α / (((m + 1 : ℕ) : ℝ) * α - 1)) ∧
        ∫⁻ ω, ENNReal.ofReal (minT T ω) ∂μ < ∞) := by
  refine ⟨fun X hX ht => single_run_infinite' hX ht hα1, exists_enough_copies hα0, ?_⟩
  intro m T hind hT htail hN
  refine ⟨expectation_eq_of_lt hind hT htail ?_, enough_copies_finite hα0 hind hT htail hN⟩
  rwa [div_lt_iff₀ hα0] at hN

end Expectation

end HeavyTailCopiesB
