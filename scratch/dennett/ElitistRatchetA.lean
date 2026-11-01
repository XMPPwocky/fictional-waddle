import Mathlib

/-!
# Elitist ratchet

An elitist search over `X` with fitness `f : X → ℝ` keeps the best point found so far:
`best (t+1) = if f (cand t) > f (best t) then cand t else best t`.

PROVED
* `fitness_best_monotone`: for every candidate sequence and every start point,
  `t ↦ f (best t)` is monotone nondecreasing.
* `fitness_cand_le_best_succ`, `isOptimal_best_of_cand`: once an optimal candidate has been
  proposed, the incumbent is optimal from then on.
* `notOptimal_subset_noneOptimal`: the event "best t is not optimal" is contained in the event
  "none of the candidates `0, …, t-1` was optimal".
* `exists_isOptimal`: on a finite nonempty `X` an optimal point exists.
* `prob_none_le`: for independent measurable events `A i` on a probability space with
  `q ≤ μ (A i)` for all `i`, `μ (⋂ i ∈ range t, (A i)ᶜ) ≤ (1 - q) ^ t`.
* `prob_best_not_optimal_le`: if the events "candidate `s` is optimal" are independent, measurable
  and each has probability at least `q`, then
  `μ {ω | best t is not optimal} ≤ (1 - q) ^ t`.
* `one_sub_pow_tendsto_zero` (real `q ∈ (0,1]`) and `one_sub_pow_tendsto_zero_ennreal`
  (`0 < q` in `ℝ≥0∞`; `q ≤ 1` is unnecessary there): `(1 - q) ^ t → 0`.
* `prob_best_not_optimal_tendsto_zero`: the failure probability tends to `0`.

INTERPRETED
* Keep what works (the elitist update never regresses) and keep trying (independent fresh
  candidates with a positive chance of being optimal) give failure probability at most
  `(1 - q) ^ t`, which tends to zero.
* Probabilities are `ℝ≥0∞`-valued measures. In `ℝ≥0∞` the bound needs no hypothesis on `q`
  and the limit needs only `0 < q` (any `q ≤ μ (A i)` is automatically `≤ 1`).
  The start point `init ω` and candidates `cand ω s` are arbitrary functions of the outcome `ω`;
  only the events "candidate `s` is optimal" are assumed independent.
-/

namespace ElitistRatchetA

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal Topology

variable {X : Type*}

/-- The incumbent after `t` steps of elitist search from `x0` with candidates `cand`. -/
noncomputable def best (f : X → ℝ) (cand : ℕ → X) (x0 : X) : ℕ → X
  | 0 => x0
  | t + 1 => if f (cand t) > f (best f cand x0 t) then cand t else best f cand x0 t

/-- `x` maximizes `f`. -/
def IsOptimal (f : X → ℝ) (x : X) : Prop := ∀ y, f y ≤ f x

theorem best_zero (f : X → ℝ) (cand : ℕ → X) (x0 : X) : best f cand x0 0 = x0 := rfl

theorem best_succ (f : X → ℝ) (cand : ℕ → X) (x0 : X) (t : ℕ) :
    best f cand x0 (t + 1) =
      if f (cand t) > f (best f cand x0 t) then cand t else best f cand x0 t := rfl

theorem fitness_best_le_succ (f : X → ℝ) (cand : ℕ → X) (x0 : X) (t : ℕ) :
    f (best f cand x0 t) ≤ f (best f cand x0 (t + 1)) := by
  rw [best_succ]
  split_ifs with h
  · exact le_of_lt h
  · exact le_rfl

theorem fitness_cand_le_best_succ (f : X → ℝ) (cand : ℕ → X) (x0 : X) (t : ℕ) :
    f (cand t) ≤ f (best f cand x0 (t + 1)) := by
  rw [best_succ]
  split_ifs with h
  · exact le_rfl
  · exact not_lt.mp h

/-- (1) Keep what works never regresses. -/
theorem fitness_best_monotone (f : X → ℝ) (cand : ℕ → X) (x0 : X) :
    Monotone (fun t => f (best f cand x0 t)) :=
  monotone_nat_of_le_succ (fitness_best_le_succ f cand x0)

theorem isOptimal_best_of_cand (f : X → ℝ) (cand : ℕ → X) (x0 : X) {s t : ℕ} (hst : s < t)
    (hs : IsOptimal f (cand s)) : IsOptimal f (best f cand x0 t) := by
  intro y
  calc f y ≤ f (cand s) := hs y
    _ ≤ f (best f cand x0 (s + 1)) := fitness_cand_le_best_succ f cand x0 s
    _ ≤ f (best f cand x0 t) := fitness_best_monotone f cand x0 (Nat.succ_le_of_lt hst)

theorem exists_isOptimal [Finite X] [Nonempty X] (f : X → ℝ) : ∃ x, IsOptimal f x :=
  Finite.exists_max f

/-- The failure event is contained in "no optimal candidate among the first `t`". -/
theorem notOptimal_subset_noneOptimal {Ω : Type*} (f : X → ℝ) (cand : Ω → ℕ → X)
    (init : Ω → X) (t : ℕ) :
    {ω | ¬ IsOptimal f (best f (cand ω) (init ω) t)} ⊆
      ⋂ s ∈ range t, {ω | IsOptimal f (cand ω s)}ᶜ := by
  intro ω hω
  simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_ofPred_eq, mem_range]
  intro s hs hopt
  exact hω (isOptimal_best_of_cand f (cand ω) (init ω) hs hopt)

/-- (2, probability core) For independent measurable events each of probability at least `q`,
the probability that none of the first `t` occurs is at most `(1 - q) ^ t`. -/
theorem prob_none_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {A : ℕ → Set Ω}
    (hind : iIndepSet A μ) (hmeas : ∀ i, MeasurableSet (A i)) {q : ℝ≥0∞}
    (hq : ∀ i, q ≤ μ (A i)) (t : ℕ) :
    μ (⋂ i ∈ range t, (A i)ᶜ) ≤ (1 - q) ^ t := by
  have := hind.isProbabilityMeasure
  have hprod : μ (⋂ i ∈ range t, (A i)ᶜ) = ∏ i ∈ range t, μ (A i)ᶜ :=
    (iIndepSet_iff A μ).1 hind (range t) (fun i _ =>
      (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton (A i))).compl)
  rw [hprod]
  calc ∏ i ∈ range t, μ (A i)ᶜ ≤ ∏ _i ∈ range t, (1 - q) := by
        apply Finset.prod_le_prod
        intro i _
        rw [prob_compl_eq_one_sub (hmeas i)]
        exact tsub_le_tsub_left (hq i) 1
    _ = (1 - q) ^ t := by rw [prod_const, card_range]

/-- (2) Elitist search with independent candidates, each optimal with probability at least `q`:
the probability that the incumbent is not optimal after `t` steps is at most `(1 - q) ^ t`. -/
theorem prob_best_not_optimal_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : X → ℝ) (cand : Ω → ℕ → X) (init : Ω → X)
    (hind : iIndepSet (fun s => {ω | IsOptimal f (cand ω s)}) μ)
    (hmeas : ∀ s, MeasurableSet {ω | IsOptimal f (cand ω s)}) {q : ℝ≥0∞}
    (hq : ∀ s, q ≤ μ {ω | IsOptimal f (cand ω s)}) (t : ℕ) :
    μ {ω | ¬ IsOptimal f (best f (cand ω) (init ω) t)} ≤ (1 - q) ^ t :=
  (measure_mono (notOptimal_subset_noneOptimal f cand init t)).trans
    (prob_none_le hind hmeas hq t)

/-- (3) `(1 - q) ^ t → 0` for real `q ∈ (0,1]`. -/
theorem one_sub_pow_tendsto_zero {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    Tendsto (fun t : ℕ => (1 - q) ^ t) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)

/-- (3) `(1 - q) ^ t → 0` for `0 < q` in `ℝ≥0∞` (truncated subtraction, so `q ≤ 1` is not
needed). -/
theorem one_sub_pow_tendsto_zero_ennreal {q : ℝ≥0∞} (hq0 : 0 < q) :
    Tendsto (fun t : ℕ => (1 - q) ^ t) atTop (𝓝 0) := by
  exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq0.ne')

/-- The failure probability of elitist search tends to zero. -/
theorem prob_best_not_optimal_tendsto_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : X → ℝ) (cand : Ω → ℕ → X) (init : Ω → X)
    (hind : iIndepSet (fun s => {ω | IsOptimal f (cand ω s)}) μ)
    (hmeas : ∀ s, MeasurableSet {ω | IsOptimal f (cand ω s)}) {q : ℝ≥0∞}
    (hq0 : 0 < q) (hq : ∀ s, q ≤ μ {ω | IsOptimal f (cand ω s)}) :
    Tendsto (fun t : ℕ => μ {ω | ¬ IsOptimal f (best f (cand ω) (init ω) t)}) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (one_sub_pow_tendsto_zero_ennreal hq0) (fun _ => bot_le)
    (prob_best_not_optimal_le f cand init hind hmeas hq)

end ElitistRatchetA
