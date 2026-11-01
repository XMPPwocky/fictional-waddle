import Mathlib

/-!
# Elitist ratchet

An elitist search on a type `X` with fitness `f : X → ℝ` keeps the best point found so far:
`best (t+1) = if f (cand t) > f (best t) then cand t else best t`.

PROVED
* `fitness_best_monotone`: for every candidate sequence and start point, `t ↦ f (best t)` is
  monotone nondecreasing.
* `isOpt_best_of_le`, `isOpt_best_succ_of_isOpt_cand`, `not_isOpt_cand_of_not_isOpt_best`:
  once an optimal point is held it is kept; a step whose candidate is optimal makes `best`
  optimal; hence if `best t` is not optimal, none of `cand 0, …, cand (t-1)` was optimal.
* `exists_isOpt`: on a finite nonempty `X` a maximizer `x*` of `f` exists.
* `prod_one_sub_le_pow`: finite product form. If `q ≤ p i ≤ 1` for all `i < t` then
  `∏_{i<t} (1 - p i) ≤ (1 - q)^t`.
* `measure_none_le_pow`: measure form. For independent events `A i` (`iIndepSet`) on a
  probability space, each of probability at least `q ∈ [0,1]`, the probability that none of
  `A 0, …, A (t-1)` occurs is at most `(1 - q)^t`.
* `measure_not_opt_le_pow`: for random candidates `C i : Ω → X` such that the events
  `{C i is optimal}` are independent, measurable and of probability at least `q ∈ [0,1]`, the
  probability that `best t` is not optimal is at most `(1 - q)^t` (any start point, possibly
  random).
* `pow_one_sub_tendsto_zero`: for `q ∈ (0,1]`, `(1 - q)^t → 0` as `t → ∞`.
* `measure_not_opt_tendsto_zero`: under the hypotheses of `measure_not_opt_le_pow` with
  `q ∈ (0,1]`, the probability that `best t` is not optimal tends to `0`.

INTERPRETED
* Keep what works (the elitist update never regresses) and keep trying (each fresh candidate
  has a fixed chance of being optimal): together they reach an optimum with probability
  tending to one, at a geometric rate.
* "Optimal" means `IsOpt f x : ∀ y, f y ≤ f x`; the probabilistic hypothesis is placed on the
  events `{C i is optimal}`, which is what "each candidate independently equals an optimal
  point with probability at least q" asserts.
-/

namespace ElitistRatchetB

open MeasureTheory ProbabilityTheory Filter Topology

variable {X : Type*}

/-- Elitist record: the best point found so far. -/
noncomputable def best (f : X → ℝ) (cand : ℕ → X) (x₀ : X) : ℕ → X
  | 0 => x₀
  | t + 1 => if f (cand t) > f (best f cand x₀ t) then cand t else best f cand x₀ t

/-- `x` maximizes `f`. -/
def IsOpt (f : X → ℝ) (x : X) : Prop := ∀ y, f y ≤ f x

lemma best_succ (f : X → ℝ) (cand : ℕ → X) (x₀ : X) (t : ℕ) :
    best f cand x₀ (t + 1) =
      if f (cand t) > f (best f cand x₀ t) then cand t else best f cand x₀ t := rfl

lemma fitness_best_le_succ (f : X → ℝ) (cand : ℕ → X) (x₀ : X) (t : ℕ) :
    f (best f cand x₀ t) ≤ f (best f cand x₀ (t + 1)) := by
  rw [best_succ]
  split_ifs with h
  · exact le_of_lt h
  · exact le_rfl

/-- (1) Keep what works never regresses. -/
theorem fitness_best_monotone (f : X → ℝ) (cand : ℕ → X) (x₀ : X) :
    Monotone (fun t => f (best f cand x₀ t)) :=
  monotone_nat_of_le_succ (fitness_best_le_succ f cand x₀)

lemma isOpt_of_fitness_le {f : X → ℝ} {x y : X} (hx : IsOpt f x) (h : f x ≤ f y) :
    IsOpt f y := fun z => (hx z).trans h

theorem isOpt_best_of_le {f : X → ℝ} {cand : ℕ → X} {x₀ : X} {s t : ℕ} (hst : s ≤ t)
    (hs : IsOpt f (best f cand x₀ s)) : IsOpt f (best f cand x₀ t) :=
  isOpt_of_fitness_le hs (fitness_best_monotone f cand x₀ hst)

theorem isOpt_best_succ_of_isOpt_cand {f : X → ℝ} {cand : ℕ → X} {x₀ : X} {i : ℕ}
    (hi : IsOpt f (cand i)) : IsOpt f (best f cand x₀ (i + 1)) := by
  rw [best_succ]
  split_ifs with h
  · exact hi
  · exact isOpt_of_fitness_le hi (not_lt.mp h)

theorem not_isOpt_cand_of_not_isOpt_best {f : X → ℝ} {cand : ℕ → X} {x₀ : X} {t : ℕ}
    (ht : ¬ IsOpt f (best f cand x₀ t)) : ∀ i < t, ¬ IsOpt f (cand i) := by
  intro i hi hci
  exact ht (isOpt_best_of_le (Nat.succ_le_of_lt hi) (isOpt_best_succ_of_isOpt_cand hci))

theorem exists_isOpt [Finite X] [Nonempty X] (f : X → ℝ) : ∃ x, IsOpt f x := by
  obtain ⟨x, hx⟩ := Finite.exists_max f
  exact ⟨x, hx⟩

/-- (2), finite product form. -/
theorem prod_one_sub_le_pow (p : ℕ → ℝ) (q : ℝ) (t : ℕ)
    (hqp : ∀ i < t, q ≤ p i) (hp1 : ∀ i < t, p i ≤ 1) :
    ∏ i ∈ Finset.range t, (1 - p i) ≤ (1 - q) ^ t := by
  calc ∏ i ∈ Finset.range t, (1 - p i) ≤ ∏ _i ∈ Finset.range t, (1 - q) :=
        Finset.prod_le_prod₀
          (fun i hi => by have := hp1 i (Finset.mem_range.mp hi); linarith)
          (fun i hi => by have := hqp i (Finset.mem_range.mp hi); linarith)
    _ = (1 - q) ^ t := by simp

/-- (2), measure form: none of `t` independent events of probability `≥ q` occurs with
probability at most `(1 - q)^t`. -/
theorem measure_none_le_pow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : ℕ → Set Ω) (hind : iIndepSet A μ) (hmeas : ∀ i, MeasurableSet (A i))
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hq : ∀ i, ENNReal.ofReal q ≤ μ (A i)) (t : ℕ) :
    μ (⋂ i ∈ Finset.range t, (A i)ᶜ) ≤ ENNReal.ofReal ((1 - q) ^ t) := by
  have := hind.isProbabilityMeasure
  have hprod : μ (⋂ i ∈ Finset.range t, (A i)ᶜ) = ∏ i ∈ Finset.range t, μ ((A i)ᶜ) :=
    (iIndepSet_iff A μ).1 hind (Finset.range t)
      (fun i _ => (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton (A i))).compl)
  rw [hprod, ENNReal.ofReal_pow (by linarith)]
  have := Finset.prod_le_pow_card (Finset.range t) (fun i => μ ((A i)ᶜ)) (ENNReal.ofReal (1 - q))
    (fun i _ => by
      rw [prob_compl_eq_one_sub (hmeas i), ENNReal.ofReal_sub _ hq0, ENNReal.ofReal_one]
      exact tsub_le_tsub_left (hq i) 1)
  simpa using this

/-- (2) applied to the elitist search with random candidates. -/
theorem measure_not_opt_le_pow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : X → ℝ) (C : ℕ → Ω → X) (x₀ : Ω → X)
    (hind : iIndepSet (fun i => {ω | IsOpt f (C i ω)}) μ)
    (hmeas : ∀ i, MeasurableSet {ω | IsOpt f (C i ω)})
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hq : ∀ i, ENNReal.ofReal q ≤ μ {ω | IsOpt f (C i ω)})
    (t : ℕ) :
    μ {ω | ¬ IsOpt f (best f (fun i => C i ω) (x₀ ω) t)} ≤ ENNReal.ofReal ((1 - q) ^ t) := by
  refine (measure_mono ?_).trans (measure_none_le_pow _ hind hmeas hq0 hq1 hq t)
  intro ω hω
  simp only [Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff, Set.mem_ofPred_eq]
  exact not_isOpt_cand_of_not_isOpt_best hω

/-- (3) -/
theorem pow_one_sub_tendsto_zero {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    Tendsto (fun t : ℕ => (1 - q) ^ t) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)

theorem measure_not_opt_tendsto_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : X → ℝ) (C : ℕ → Ω → X) (x₀ : Ω → X)
    (hind : iIndepSet (fun i => {ω | IsOpt f (C i ω)}) μ)
    (hmeas : ∀ i, MeasurableSet {ω | IsOpt f (C i ω)})
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hq : ∀ i, ENNReal.ofReal q ≤ μ {ω | IsOpt f (C i ω)}) :
    Tendsto (fun t : ℕ => μ {ω | ¬ IsOpt f (best f (fun i => C i ω) (x₀ ω) t)}) atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℕ => ENNReal.ofReal ((1 - q) ^ t)) atTop (𝓝 0) := by
    simpa using (ENNReal.tendsto_ofReal (pow_one_sub_tendsto_zero hq0 hq1))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) (fun t => measure_not_opt_le_pow f C x₀ hind hmeas hq0.le hq1 hq t)

end ElitistRatchetB
