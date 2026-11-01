import Mathlib

/-!
# Greedy locks in on the worse arm

Two-armed Bernoulli bandit. Arm `one` pays `1` with probability `p₁`, arm `two` with
probability `p₂`, `0 < p₁ < p₂ < 1`. A reward history is `ω : Arm × ℕ → Bool`, where
`ω (a, k)` is the reward of the `k`-th pull (0-indexed) of arm `a`. Greedy pulls arm `one` at
time 0, arm `two` at time 1, and at every time `t ≥ 2` pulls the arm with the strictly higher
empirical mean, ties going to arm `one`.

PROVED
* `mean_two_zero_le_mean_one`, `greedy_never_pulls_two` (deterministic, every `ω`): if arm
  `two`'s first pull paid `0`, then at every time `t ≥ 2` arm `two`'s empirical mean is `0`,
  arm `one`'s is `≥ 0`, and greedy pulls arm `one`.
* `greedy_never_pulls_two_streams`: the same, stated for arbitrary separate reward sequences
  `r₁ r₂ : ℕ → Bool` of the two arms with `r₂ 0 = false`.
* `reward_sum_of_lock`: on that history the total reward over times `0, …, T+1` equals the sum
  of the first `T+1` arm-`one` rewards.
* `prob_lock_event`: under the product law of independent Bernoulli rewards, the event
  `ω (two, 0) = false` has probability `1 - p₂`, which is `> 0`.
* `prob_always_worse_arm`: the probability that greedy pulls arm `one` at every `t ≥ 2` is at
  least `1 - p₂ > 0`.
* `cond_expected_average`: conditioned on that event, the expected average reward over the
  first `T+2` steps equals `(T+1)/(T+2) · p₁`; `cond_expected_average_lt` gives it is
  `≤ p₁ < p₂`.

INTERPRETED
* The randomness is the standard reward-table model: one i.i.d. Bernoulli stream per arm,
  all independent (`Measure.infinitePi` of `bernoulliMeasure true false`).
* "Average reward stays at most `p₁` in expectation" is the conditional expectation, given
  arm `two`'s first pull paid `0`, of the empirical average reward over a finite horizon.
-/

namespace GreedyLocksInA

open MeasureTheory ProbabilityTheory unitInterval

inductive Arm
  | one
  | two
  deriving DecidableEq

/-- Pull counts and reward sums per arm. -/
structure State where
  n : Arm → ℕ
  s : Arm → ℕ

/-- Empirical mean of arm `a` (`0` if never pulled, by `x / 0 = 0`). -/
def mean (st : State) (a : Arm) : ℚ := (st.s a : ℚ) / st.n a

/-- Greedy choice: arm `two` only if its empirical mean is strictly higher. -/
def greedy (st : State) : Arm := if mean st .one < mean st .two then .two else .one

/-- The arm pulled at time `t` given the state before time `t`. -/
def choice : ℕ → State → Arm
  | 0, _ => .one
  | 1, _ => .two
  | _ + 2, st => greedy st

/-- Pull arm `a`: it yields the next unused reward `ω (a, st.n a)` of that arm. -/
def pull (ω : Arm × ℕ → Bool) (st : State) (a : Arm) : State where
  n := fun b => if b = a then st.n b + 1 else st.n b
  s := fun b => if b = a then st.s b + (if ω (a, st.n a) then 1 else 0) else st.s b

/-- State before time `t`. -/
def stateAt (ω : Arm × ℕ → Bool) : ℕ → State
  | 0 => ⟨fun _ => 0, fun _ => 0⟩
  | t + 1 => pull ω (stateAt ω t) (choice t (stateAt ω t))

/-- Arm pulled at time `t`. -/
def armAt (ω : Arm × ℕ → Bool) (t : ℕ) : Arm := choice t (stateAt ω t)

/-- Reward received at time `t`. -/
def rewardAt (ω : Arm × ℕ → Bool) (t : ℕ) : Bool :=
  ω (armAt ω t, (stateAt ω t).n (armAt ω t))

lemma mean_nonneg (st : State) (a : Arm) : 0 ≤ mean st a := by
  unfold mean; positivity

lemma invariant (ω : Arm × ℕ → Bool) (h : ω (.two, 0) = false) (t : ℕ) :
    (stateAt ω (t + 2)).s .two = 0 ∧ (stateAt ω (t + 2)).n .two = 1 ∧
      (stateAt ω (t + 2)).n .one = t + 1 := by
  induction t with
  | zero => simp [stateAt, pull, choice, h]
  | succ t ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hg : greedy (stateAt ω (t + 2)) = .one := by
      have : mean (stateAt ω (t + 2)) .two = 0 := by simp [mean, h1]
      simp [greedy, this, mean_nonneg]
    rw [show t + 1 + 2 = (t + 2) + 1 by ring, stateAt, show choice (t + 2) = greedy from rfl, hg]
    simp [pull, h1, h2, h3]

/-- (1) Deterministic lock-in: after arm `two`'s first pull pays `0`, at every later time its
empirical mean is `0` and arm `one`'s is `≥ 0`. -/
theorem mean_two_zero_le_mean_one (ω : Arm × ℕ → Bool) (h : ω (.two, 0) = false)
    (t : ℕ) (ht : 2 ≤ t) :
    mean (stateAt ω t) .two = 0 ∧ 0 ≤ mean (stateAt ω t) .one := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le' ht
  exact ⟨by simp [mean, (invariant ω h u).1], mean_nonneg _ _⟩

/-- (1) Greedy never pulls arm `two` at any time `t ≥ 2`, for every reward history in which
arm `two`'s first pull paid `0`. -/
theorem greedy_never_pulls_two (ω : Arm × ℕ → Bool) (h : ω (.two, 0) = false)
    (t : ℕ) (ht : 2 ≤ t) : armAt ω t = .one := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le' ht
  obtain ⟨h0, -⟩ := mean_two_zero_le_mean_one ω h (u + 2) ht
  show greedy _ = _
  simp [greedy, h0, mean_nonneg]

/-- Reward history assembled from one reward sequence per arm. -/
def streams (r₁ r₂ : ℕ → Bool) : Arm × ℕ → Bool
  | (.one, k) => r₁ k
  | (.two, k) => r₂ k

/-- (1) For every sequence of arm-`one` rewards `r₁` and every arm-`two` sequence with
`r₂ 0 = false`, greedy pulls arm `one` at every time `t ≥ 2`. -/
theorem greedy_never_pulls_two_streams (r₁ r₂ : ℕ → Bool) (h : r₂ 0 = false)
    (t : ℕ) (ht : 2 ≤ t) : armAt (streams r₁ r₂) t = .one :=
  greedy_never_pulls_two _ h t ht

/-- Indicator of a Boolean reward as a real number. -/
def ind (b : Bool) : ℝ := if b then 1 else 0

theorem reward_sum_of_lock (ω : Arm × ℕ → Bool) (h : ω (.two, 0) = false) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 2), ind (rewardAt ω t) =
      ∑ k ∈ Finset.range (T + 1), ind (ω (.one, k)) := by
  induction T with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_one]
    cases hω : ω (Arm.one, 0) <;> simp [rewardAt, armAt, stateAt, choice, pull, h, ind, hω]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ _ (T + 1)]
    congr 1
    have ha := greedy_never_pulls_two ω h (T + 2) (by omega)
    simp [rewardAt, ha, (invariant ω h T).2.2]

/-- Bernoulli law of the reward of arm `a`. -/
noncomputable def armLaw (p₁ p₂ : I) : Arm → Measure Bool
  | .one => bernoulliMeasure true false p₁
  | .two => bernoulliMeasure true false p₂

instance (p₁ p₂ : I) (a : Arm) : IsProbabilityMeasure (armLaw p₁ p₂ a) := by
  cases a <;> simp only [armLaw] <;> infer_instance

/-- Law of the reward table: all rewards independent, arm `a`'s rewards `Ber(p_a)`. -/
noncomputable def law (p₁ p₂ : I) : Measure (Arm × ℕ → Bool) :=
  Measure.infinitePi (fun i : Arm × ℕ => armLaw p₁ p₂ i.1)

instance (p₁ p₂ : I) : IsProbabilityMeasure (law p₁ p₂) := by
  unfold law; infer_instance

/-- The event that arm `two`'s first pull paid `0`. -/
def lockEvent : Set (Arm × ℕ → Bool) := {ω | ω (.two, 0) = false}

lemma measurableSet_coord (i : Arm × ℕ) (b : Bool) :
    MeasurableSet {ω : Arm × ℕ → Bool | ω i = b} :=
  (measurableSet_singleton b).preimage (measurable_pi_apply i)

/-- (2) `P(arm two's first pull pays 0) = 1 - p₂ > 0`. -/
theorem prob_lock_event (p₁ p₂ : I) (h₂ : (p₂ : ℝ) < 1) :
    (law p₁ p₂).real lockEvent = 1 - p₂ ∧ 0 < (law p₁ p₂).real lockEvent := by
  have hE : (law p₁ p₂).real lockEvent = 1 - p₂ := by
    have : lockEvent = (fun ω : Arm × ℕ → Bool => ω (.two, 0)) ⁻¹' {false} := rfl
    rw [this, measureReal_def, law,
      (measurePreserving_eval_infinitePi (fun i : Arm × ℕ => armLaw p₁ p₂ i.1) (.two, 0)
        ).measure_preimage (measurableSet_singleton _).nullMeasurableSet]
    simp [armLaw]
  exact ⟨hE, by rw [hE]; linarith⟩

/-- (2) With probability at least `1 - p₂ > 0`, greedy pulls the worse arm at every time after
the second. -/
theorem prob_always_worse_arm (p₁ p₂ : I) (h₂ : (p₂ : ℝ) < 1) :
    1 - (p₂ : ℝ) ≤ (law p₁ p₂).real {ω | ∀ t, 2 ≤ t → armAt ω t = .one} ∧ 0 < 1 - (p₂ : ℝ) := by
  refine ⟨?_, by linarith⟩
  rw [← (prob_lock_event p₁ p₂ h₂).1]
  exact measureReal_mono (fun ω hω => greedy_never_pulls_two ω hω) (measure_ne_top _ _)

lemma prob_lock_inter (p₁ p₂ : I) (k : ℕ) :
    (law p₁ p₂).real (lockEvent ∩ {ω | ω (.one, k) = true}) = (1 - p₂) * p₁ := by
  classical
  set t : Arm × ℕ → Set Bool := fun i => if i = (.two, 0) then {false} else {true}
  have hset : lockEvent ∩ {ω : Arm × ℕ → Bool | ω (.one, k) = true} =
      Set.pi (↑({(.two, 0), (.one, k)} : Finset (Arm × ℕ))) t := by
    ext ω
    simp [lockEvent, t]
  rw [measureReal_def, hset, law, Measure.infinitePi_pi _ (fun i _ => by
    simp only [t]; split_ifs <;> exact measurableSet_singleton _)]
  rw [Finset.prod_pair (by simp)]
  simp [t, armLaw]

lemma ind_eq (i : Arm × ℕ) :
    (fun ω : Arm × ℕ → Bool => ind (ω i)) = {ω | ω i = true}.indicator 1 := by
  ext ω
  simp [ind, Set.indicator]

/-- (2) Conditioned on arm `two`'s first pull paying `0`, the expected average reward over the
first `T + 2` steps is `(T+1)/(T+2) · p₁`. -/
theorem cond_expected_average (p₁ p₂ : I) (h₂ : (p₂ : ℝ) < 1) (T : ℕ) :
    ∫ ω, (∑ t ∈ Finset.range (T + 2), ind (rewardAt ω t)) / (T + 2) ∂(law p₁ p₂)[|lockEvent] =
      (T + 1) / (T + 2) * p₁ := by
  have hE : MeasurableSet (lockEvent : Set (Arm × ℕ → Bool)) := measurableSet_coord _ _
  rw [integral_congr_ae (g := fun ω => (∑ k ∈ Finset.range (T + 1), ind (ω (.one, k))) / (T + 2))
    (by filter_upwards [ae_cond_mem hE] with ω hω; rw [reward_sum_of_lock ω hω])]
  have hk : ∀ k, ∫ ω, ind (ω (.one, k)) ∂(law p₁ p₂)[|lockEvent] = p₁ := by
    intro k
    rw [ind_eq, integral_indicator_one (measurableSet_coord _ _), measureReal_def,
      cond_apply hE, ENNReal.toReal_mul, ENNReal.toReal_inv, ← measureReal_def,
      ← measureReal_def, prob_lock_inter, (prob_lock_event p₁ p₂ h₂).1]
    have : (1 - (p₂ : ℝ)) ≠ 0 := by linarith
    field_simp
  rw [integral_div, integral_finsetSum]
  · simp only [hk, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  · intro k _
    rw [ind_eq]
    exact (integrable_const (1 : ℝ)).indicator (measurableSet_coord _ _)

/-- (2) That conditional expected average is at most `p₁`, hence strictly below `p₂`. -/
theorem cond_expected_average_lt (p₁ p₂ : I) (h₁ : (0 : ℝ) < p₁) (h₁₂ : (p₁ : ℝ) < p₂)
    (h₂ : (p₂ : ℝ) < 1) (T : ℕ) :
    ∫ ω, (∑ t ∈ Finset.range (T + 2), ind (rewardAt ω t)) / (T + 2) ∂(law p₁ p₂)[|lockEvent] ≤
        p₁ ∧ (p₁ : ℝ) < p₂ := by
  rw [cond_expected_average p₁ p₂ h₂ T]
  refine ⟨?_, h₁₂⟩
  have hT : (0 : ℝ) < T + 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hT]
  nlinarith

end GreedyLocksInA
