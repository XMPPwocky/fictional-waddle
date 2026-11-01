import Mathlib

/-!
# Survival function of the minimum of independent copies

PROVED

* `lt_inf'_iff_forall` : `t < min_i T_i` iff every `T_i` exceeds `t`.
* `measure_min_gt_eq_prod` : for independent `T_1, ..., T_N` (any linearly ordered codomain,
  `Ioi t` measurable), `P(min_i T_i > t) = ∏_i P(T_i > t)`.
* `measure_min_gt_eq_pow` : if moreover all copies share the survival function `S`, then
  `P(min_i T_i > t) = S(t)^N`.
* `measure_all_gt_eq_pow` : the same identity with the event written as `∀ i, T_i > t`, which
  also covers `N = 0` (value `1`).
* `measure_min_gt_geometric` : if each copy is geometric with `P(T_i > t) = (1-p)^t`, then
  `P(min_i T_i > t) = (1-p)^(N t)`.
* `min_geometric_rate` : `(1-p)^(N t) = (1 - q)^t` with `q = 1 - (1-p)^N`, i.e. the minimum is
  geometric with per-step success probability `1 - (1-p)^N` (in `ℝ≥0∞`, for `p ≤ 1`).
* `measure_min_gt_geometric_rate` : combination of the two previous results.
* Explicit finite Bernoulli model (`Fin N × Fin t → Bool`, each entry is "copy i succeeds at
  step s", independent with probability `p`):
  - `prob_total` : the weights sum to `1`.
  - `prob_copy_survives` : `P(copy i has no success in steps 1..t) = (1-p)^t`.
  - `prob_min_survives` : `P(no copy has a success in steps 1..t) = (1-p)^(N t)`.
  - `prob_min_survives_eq_pow` : `P(min > t) = P(copy i > t)^N`.
  - `prob_min_survives_eq_geometric` : `P(min > t) = (1 - (1 - (1-p)^N))^t`.
* `tail_strictAnti` : for real `0 < p < 1` and `t ≥ 1`, `N ↦ (1-p)^(N t)` is strictly
  decreasing.
* `tail_strictAnti_ennreal` : the same in `ℝ≥0∞`.
* `tail_not_strictAnti_of_p_eq_one` : for `p = 1`, `t ≥ 1`, the tail is not strictly
  decreasing (it is `0` for every `N ≥ 1`), so the hypothesis `p < 1` is needed.

INTERPRETED

* In the finite model, "the run time of copy `i` exceeds `t`" is the event that copy `i` has
  no success among its first `t` steps; "the minimum exceeds `t`" is the event that this holds
  for every copy.
-/

namespace MinOfCopiesTailA

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

section General

variable {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [LinearOrder β]

omit [MeasurableSpace β] in
theorem lt_inf'_iff_forall {N : ℕ} (hne : (univ : Finset (Fin N)).Nonempty)
    (x : Fin N → β) (t : β) :
    t < univ.inf' hne x ↔ ∀ i, t < x i := by
  simp [Finset.lt_inf'_iff]

theorem measure_all_gt_eq_prod {μ : Measure Ω} {N : ℕ} (T : Fin N → Ω → β)
    (hind : iIndepFun T μ) (t : β) (ht : MeasurableSet (Ioi t)) :
    μ {ω | ∀ i, t < T i ω} = ∏ i, μ (T i ⁻¹' Ioi t) := by
  have hset : {ω | ∀ i, t < T i ω} = ⋂ i ∈ (univ : Finset (Fin N)), T i ⁻¹' Ioi t := by
    ext ω; simp
  rw [hset]
  exact hind.measure_inter_preimage_eq_mul univ (sets := fun _ => Ioi t) (fun _ _ => ht)

theorem measure_min_gt_eq_prod {μ : Measure Ω} {N : ℕ} (hne : (univ : Finset (Fin N)).Nonempty)
    (T : Fin N → Ω → β) (hind : iIndepFun T μ) (t : β) (ht : MeasurableSet (Ioi t)) :
    μ {ω | t < univ.inf' hne (fun i => T i ω)} = ∏ i, μ (T i ⁻¹' Ioi t) := by
  have hset : {ω | t < univ.inf' hne (fun i => T i ω)} = {ω | ∀ i, t < T i ω} := by
    ext ω; simp
  rw [hset]
  exact measure_all_gt_eq_prod T hind t ht

theorem measure_all_gt_eq_pow {μ : Measure Ω} {N : ℕ} (T : Fin N → Ω → β)
    (hind : iIndepFun T μ) (S : β → ℝ≥0∞) (hS : ∀ i t, μ (T i ⁻¹' Ioi t) = S t)
    (t : β) (ht : MeasurableSet (Ioi t)) :
    μ {ω | ∀ i, t < T i ω} = S t ^ N := by
  rw [measure_all_gt_eq_prod T hind t ht]
  simp [hS]

theorem measure_min_gt_eq_pow {μ : Measure Ω} {N : ℕ} (hne : (univ : Finset (Fin N)).Nonempty)
    (T : Fin N → Ω → β) (hind : iIndepFun T μ) (S : β → ℝ≥0∞)
    (hS : ∀ i t, μ (T i ⁻¹' Ioi t) = S t) (t : β) (ht : MeasurableSet (Ioi t)) :
    μ {ω | t < univ.inf' hne (fun i => T i ω)} = S t ^ N := by
  rw [measure_min_gt_eq_prod hne T hind t ht]
  simp [hS]

end General

section Geometric

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measure_min_gt_geometric {μ : Measure Ω} {N : ℕ}
    (hne : (univ : Finset (Fin N)).Nonempty) (T : Fin N → Ω → ℕ) (hind : iIndepFun T μ)
    (p : ℝ≥0∞) (hS : ∀ i (t : ℕ), μ (T i ⁻¹' Ioi t) = (1 - p) ^ t) (t : ℕ) :
    μ {ω | t < univ.inf' hne (fun i => T i ω)} = (1 - p) ^ (N * t) := by
  rw [measure_min_gt_eq_pow hne T hind (fun t => (1 - p) ^ t) hS t (measurableSet_Ioi)]
  rw [← pow_mul, mul_comm]

theorem min_geometric_rate (p : ℝ≥0∞) (N t : ℕ) :
    (1 - (1 - (1 - p) ^ N)) ^ t = (1 - p) ^ (N * t) := by
  have h1 : (1 - p) ^ N ≤ 1 := pow_le_one₀ (by simp) tsub_le_self
  rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top h1, pow_mul]

theorem measure_min_gt_geometric_rate {μ : Measure Ω} {N : ℕ}
    (hne : (univ : Finset (Fin N)).Nonempty) (T : Fin N → Ω → ℕ) (hind : iIndepFun T μ)
    (p : ℝ≥0∞) (hS : ∀ i (t : ℕ), μ (T i ⁻¹' Ioi t) = (1 - p) ^ t) (t : ℕ) :
    μ {ω | t < univ.inf' hne (fun i => T i ω)} = (1 - (1 - (1 - p) ^ N)) ^ t := by
  rw [measure_min_gt_geometric hne T hind p hS t, min_geometric_rate]

end Geometric

section FiniteModel

/-- Outcomes of the first `t` steps of `N` copies: `ω (i, s)` says whether copy `i`
succeeds at step `s`. -/
abbrev Outcome (N t : ℕ) := Fin N × Fin t → Bool

/-- Bernoulli weight of a single trial. -/
def trialWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- Product weight of an outcome: all trials independent with success probability `p`. -/
def weight (p : ℝ) {N t : ℕ} (ω : Outcome N t) : ℝ := ∏ k, trialWeight p (ω k)

/-- Probability of an event in the finite model. -/
def prob (p : ℝ) {N t : ℕ} (E : Outcome N t → Prop) [DecidablePred E] : ℝ :=
  ∑ ω, if E ω then weight p ω else 0

/-- Copy `i` has no success among its first `t` steps, i.e. its run time exceeds `t`. -/
def copySurvives {N t : ℕ} (i : Fin N) (ω : Outcome N t) : Prop := ∀ s, ω (i, s) = false

/-- No copy has a success among the first `t` steps, i.e. the minimum run time exceeds `t`. -/
def minSurvives {N t : ℕ} (ω : Outcome N t) : Prop := ∀ i, copySurvives i ω

instance {N t : ℕ} (i : Fin N) : DecidablePred (copySurvives (N := N) (t := t) i) := by
  intro ω; unfold copySurvives; infer_instance

instance {N t : ℕ} : DecidablePred (minSurvives (N := N) (t := t)) := by
  intro ω; unfold minSurvives copySurvives; infer_instance

theorem prob_total (p : ℝ) (N t : ℕ) :
    ∑ ω : Outcome N t, weight p ω = 1 := by
  unfold weight
  rw [← Fintype.prod_sum (fun (_ : Fin N × Fin t) (b : Bool) => trialWeight p b)]
  simp [trialWeight]

theorem prob_copy_survives (p : ℝ) {N t : ℕ} (i : Fin N) :
    prob p (copySurvives (t := t) i) = (1 - p) ^ t := by
  unfold prob weight
  have key : ∀ ω : Outcome N t,
      (if copySurvives i ω then ∏ k, trialWeight p (ω k) else 0)
        = ∏ k, (fun (k : Fin N × Fin t) (b : Bool) =>
            if k.1 = i ∧ b = true then 0 else trialWeight p b) k (ω k) := by
    intro ω
    by_cases h : copySurvives i ω
    · simp only [h, ↓reduceIte]
      refine Finset.prod_congr rfl (fun k _ => ?_)
      by_cases hk : k.1 = i
      · have : ω k = false := by
          obtain ⟨a, s⟩ := k; simp only at hk; subst hk; exact h s
        simp [this]
      · simp [hk]
    · simp only [h, ↓reduceIte]
      unfold copySurvives at h
      push Not at h
      obtain ⟨s, hs⟩ := h
      symm
      refine Finset.prod_eq_zero (i := (i, s)) (Finset.mem_univ _) ?_
      simp at hs
      simp [hs]
  simp_rw [key]
  rw [← Fintype.prod_sum (fun (k : Fin N × Fin t) (b : Bool) =>
    if k.1 = i ∧ b = true then (0 : ℝ) else trialWeight p b)]
  have hk : ∀ k : Fin N × Fin t,
      (∑ b : Bool, if k.1 = i ∧ b = true then (0 : ℝ) else trialWeight p b)
        = if k.1 = i then 1 - p else 1 := by
    intro k
    by_cases hk : k.1 = i <;> simp [hk, trialWeight]
  simp_rw [hk]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  have : (Finset.univ.filter fun k : Fin N × Fin t => k.1 = i)
      = Finset.image (fun s : Fin t => (i, s)) Finset.univ := by
    ext ⟨a, s⟩; simp [eq_comm]
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp

theorem prob_min_survives (p : ℝ) (N t : ℕ) :
    prob p (minSurvives (N := N) (t := t)) = (1 - p) ^ (N * t) := by
  unfold prob weight
  have key : ∀ ω : Outcome N t,
      (if minSurvives ω then ∏ k, trialWeight p (ω k) else 0)
        = ∏ k, (fun (_ : Fin N × Fin t) (b : Bool) =>
            if b = true then 0 else trialWeight p b) k (ω k) := by
    intro ω
    by_cases h : minSurvives ω
    · simp only [h, ↓reduceIte]
      refine Finset.prod_congr rfl (fun k _ => ?_)
      have : ω k = false := h k.1 k.2
      simp [this]
    · simp only [h, ↓reduceIte]
      unfold minSurvives copySurvives at h
      push Not at h
      obtain ⟨i, s, hs⟩ := h
      symm
      refine Finset.prod_eq_zero (i := (i, s)) (Finset.mem_univ _) ?_
      simp at hs
      simp [hs]
  simp_rw [key]
  rw [← Fintype.prod_sum (fun (_ : Fin N × Fin t) (b : Bool) =>
    if b = true then (0 : ℝ) else trialWeight p b)]
  simp [trialWeight, Finset.prod_const]

theorem prob_min_survives_eq_pow (p : ℝ) {N t : ℕ} (i : Fin N) :
    prob p (minSurvives (N := N) (t := t)) = (prob p (copySurvives (t := t) i)) ^ N := by
  rw [prob_min_survives, prob_copy_survives, ← pow_mul, mul_comm]

theorem prob_min_survives_eq_geometric (p : ℝ) (N t : ℕ) :
    prob p (minSurvives (N := N) (t := t)) = (1 - (1 - (1 - p) ^ N)) ^ t := by
  rw [prob_min_survives, sub_sub_cancel, pow_mul]

end FiniteModel

section Monotone

theorem tail_strictAnti {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {t : ℕ} (ht : 1 ≤ t) :
    StrictAnti (fun N : ℕ => (1 - p) ^ (N * t)) := by
  intro m n hmn
  have ha0 : 0 < 1 - p := by linarith
  have ha1 : 1 - p < 1 := by linarith
  exact pow_lt_pow_right_of_lt_one₀ ha0 ha1 (Nat.mul_lt_mul_of_pos_right hmn (by omega))

theorem tail_strictAnti_ennreal {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) {t : ℕ} (ht : 1 ≤ t) :
    StrictAnti (fun N : ℕ => (1 - p) ^ (N * t)) := by
  have hpt : p ≠ ⊤ := ne_top_of_lt hp1
  have hr0 : 0 < p.toReal := ENNReal.toReal_pos hp0.ne' hpt
  have hr1 : p.toReal < 1 := by
    have := (ENNReal.toReal_lt_toReal hpt ENNReal.one_ne_top).2 hp1
    simpa using this
  have hrepr : ∀ k : ℕ, (1 - p) ^ k = ENNReal.ofReal ((1 - p.toReal) ^ k) := by
    intro k
    rw [ENNReal.ofReal_pow (by linarith), ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
      ENNReal.ofReal_one, ENNReal.ofReal_toReal hpt]
  intro m n hmn
  simp only [hrepr]
  rw [ENNReal.ofReal_lt_ofReal_iff (pow_pos (by linarith) _)]
  exact tail_strictAnti hr0 hr1 ht hmn

theorem tail_not_strictAnti_of_p_eq_one {t : ℕ} (ht : 1 ≤ t) :
    ¬ StrictAnti (fun N : ℕ => ((1 : ℝ) - 1) ^ (N * t)) := by
  intro h
  have := h (show (1 : ℕ) < 2 by norm_num)
  simp only [sub_self] at this
  rw [zero_pow (by omega), zero_pow (by omega)] at this
  exact lt_irrefl _ this

end Monotone

end MinOfCopiesTailA
