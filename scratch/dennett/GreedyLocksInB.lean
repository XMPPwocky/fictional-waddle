import Mathlib

/-!
# Greedy locks in on the worse arm of a two-armed Bernoulli bandit

Model. Rewards are a reward table: `r1 k` is the reward of the `k`-th pull of arm 1
and `r2 k` that of the `k`-th pull of arm 2 (0-indexed, values in `{0,1}` encoded as
`Bool`). The greedy rule pulls arm 1 at time 0, arm 2 at time 1, and at every time
`t ≥ 2` pulls arm 2 iff its empirical mean is strictly larger than arm 1's (ties go to
arm 1). Empirical means are `s / n` in `ℚ`.

For the probability part, rewards over a finite horizon `N` are an element of
`(Fin N → Bool) × (Fin N → Bool)` with product Bernoulli weights
(`p₁` per arm-1 entry, `p₂` per arm-2 entry).

PROVED
* `greedy_first_two`: greedy pulls arm 1 at time 0 and arm 2 at time 1.
* `state_of_first_zero`: if arm 2's first pull paid 0, then for every `t ≥ 2` the
  state is `n1 = t-1, n2 = 1, s1 = ∑_{k<t-1} r1 k, s2 = 0`.
* `never_pulls_two_again` (part 1): if arm 2's first pull paid 0 then for every arm-1
  reward sequence, greedy pulls arm 1 at every time `t ≥ 2`.
* `total_reward_of_first_zero`: on that event the total reward up to time `T ≥ 2` is
  `∑_{k<T-1} r1 k` (only arm-1 rewards, nothing from arm 2).
* `weight_total`: the product Bernoulli weights sum to 1.
* `prob_lock_in` (part 2): the event `r2 0 = 0` has probability `1 - p₂`, and this is `> 0`.
* `expected_reward_on_lock_in`: `E[total reward up to T ; r2 0 = 0] = (1 - p₂) (T - 1) p₁`
  for `2 ≤ T ≤ N`.
* `cond_avg_reward_lt`: the conditional expected average reward up to `T` given the
  event equals `((T-1)/T) p₁`, which is `≤ p₁ < p₂`.

INTERPRETED
* "Greedy never pulls arm 2 again at any later time" = `arm r1 r2 t = .one` for all `t ≥ 2`.
* "Average reward stays at most `p₁` in expectation" = conditional expectation, given the
  lock-in event, of (total reward up to time `T`)/`T`, under the finite-horizon product
  Bernoulli measure.
-/

namespace GreedyLocksInB

inductive Arm
  | one
  | two
  deriving DecidableEq

structure St where
  n1 : ℕ
  n2 : ℕ
  s1 : ℕ
  s2 : ℕ

/-- Numerical value of a `{0,1}` reward. -/
def val (b : Bool) : ℕ := if b then 1 else 0

lemma val_false : val false = 0 := rfl

/-- Empirical mean `s / n`. -/
def mean (s n : ℕ) : ℚ := (s : ℚ) / n

/-- Greedy choice at time `t` in state `st`. -/
def choose (t : ℕ) (st : St) : Arm :=
  if t = 0 then .one
  else if t = 1 then .two
  else if mean st.s1 st.n1 < mean st.s2 st.n2 then .two else .one

/-- Pull arm `a`: the reward is the next unused entry of that arm's reward sequence. -/
def pull (r1 r2 : ℕ → Bool) : Arm → St → St
  | .one, st => ⟨st.n1 + 1, st.n2, st.s1 + val (r1 st.n1), st.s2⟩
  | .two, st => ⟨st.n1, st.n2 + 1, st.s1, st.s2 + val (r2 st.n2)⟩

/-- State before time `t`. -/
def state (r1 r2 : ℕ → Bool) : ℕ → St
  | 0 => ⟨0, 0, 0, 0⟩
  | t + 1 => pull r1 r2 (choose t (state r1 r2 t)) (state r1 r2 t)

/-- Arm pulled at time `t`. -/
def arm (r1 r2 : ℕ → Bool) (t : ℕ) : Arm := choose t (state r1 r2 t)

/-- Reward received at time `t`. -/
def reward (r1 r2 : ℕ → Bool) (t : ℕ) : ℕ :=
  match arm r1 r2 t with
  | .one => val (r1 (state r1 r2 t).n1)
  | .two => val (r2 (state r1 r2 t).n2)

/-- Total reward over times `0, …, T-1`. -/
def total (r1 r2 : ℕ → Bool) (T : ℕ) : ℕ := ∑ t ∈ Finset.range T, reward r1 r2 t

theorem greedy_first_two (r1 r2 : ℕ → Bool) :
    arm r1 r2 0 = .one ∧ arm r1 r2 1 = .two := by
  simp [arm, choose]

theorem total_eq_sums (r1 r2 : ℕ → Bool) (T : ℕ) :
    total r1 r2 T = (state r1 r2 T).s1 + (state r1 r2 T).s2 := by
  induction T with
  | zero => simp [total, state]
  | succ T ih =>
    rw [total, Finset.sum_range_succ, ← total, ih]
    simp only [reward, arm, state]
    cases choose T (state r1 r2 T) <;> simp [pull] <;> ring

theorem state_of_first_zero (r1 r2 : ℕ → Bool) (h : r2 0 = false) (t : ℕ) :
    state r1 r2 (t + 2) = ⟨t + 1, 1, ∑ k ∈ Finset.range (t + 1), val (r1 k), 0⟩ := by
  induction t with
  | zero =>
    simp [state, choose, pull, h, val_false]
  | succ t ih =>
    show pull r1 r2 (choose (t + 2) (state r1 r2 (t + 2))) (state r1 r2 (t + 2)) = _
    have hc : choose (t + 2) (state r1 r2 (t + 2)) = .one := by
      rw [ih]
      have : ¬ mean (∑ k ∈ Finset.range (t + 1), val (r1 k)) (t + 1) < mean 0 1 := by
        simp only [mean, Nat.cast_zero, zero_div, not_lt]
        positivity
      simp [choose, this]
    rw [hc, ih]
    simp [pull, Finset.sum_range_succ]

/-- Part (1): after a zero first pull of arm 2, greedy pulls arm 1 at every time `t ≥ 2`,
for every arm-1 reward sequence. -/
theorem never_pulls_two_again (r1 r2 : ℕ → Bool) (h : r2 0 = false) :
    ∀ t, 2 ≤ t → arm r1 r2 t = .one := by
  intro t ht
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 2 := ⟨t - 2, by omega⟩
  have : ¬ mean (∑ k ∈ Finset.range (u + 1), val (r1 k)) (u + 1) < mean 0 1 := by
    simp only [mean, Nat.cast_zero, zero_div, not_lt]
    positivity
  simp [arm, state_of_first_zero r1 r2 h, choose, this]

theorem total_reward_of_first_zero (r1 r2 : ℕ → Bool) (h : r2 0 = false) (T : ℕ)
    (hT : 2 ≤ T) : total r1 r2 T = ∑ k ∈ Finset.range (T - 1), val (r1 k) := by
  obtain ⟨u, rfl⟩ : ∃ u, T = u + 2 := ⟨T - 2, by omega⟩
  rw [total_eq_sums, state_of_first_zero r1 r2 h]
  simp

/-! ### Probability part: finite horizon, product Bernoulli rewards -/

/-- Extend a finite reward table to a sequence (entries beyond the horizon are `false`). -/
def ext {N : ℕ} (x : Fin N → Bool) : ℕ → Bool :=
  fun k => if hk : k < N then x ⟨k, hk⟩ else false

/-- Bernoulli(`p`) weight of an outcome. -/
def w (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- Product Bernoulli weight of a reward table: `p₁` for arm 1 entries, `p₂` for arm 2. -/
def μ (p₁ p₂ : ℝ) {N : ℕ} (ω : (Fin N → Bool) × (Fin N → Bool)) : ℝ :=
  (∏ i, w p₁ (ω.1 i)) * (∏ i, w p₂ (ω.2 i))

/-- The lock-in event: arm 2's first pull pays 0. -/
def E {N : ℕ} (ω : (Fin N → Bool) × (Fin N → Bool)) : Prop := ext ω.2 0 = false

instance {N : ℕ} (ω : (Fin N → Bool) × (Fin N → Bool)) : Decidable (E ω) := by
  unfold E; infer_instance

lemma w_add (p : ℝ) : w p true + w p false = 1 := by
  simp [w]

lemma sum_w (p : ℝ) : ∑ b, w p b = 1 := by
  simp [w]

lemma sum_prod_w (p : ℝ) (N : ℕ) : ∑ x : Fin N → Bool, ∏ i, w p (x i) = 1 := by
  rw [← Fintype.prod_sum (fun _ b => w p b)]
  simp [w_add]

lemma sum_prod_w_mul (p : ℝ) {N : ℕ} (j : Fin N) (f : Bool → ℝ) :
    ∑ x : Fin N → Bool, (∏ i, w p (x i)) * f (x j) = ∑ b, w p b * f b := by
  have hpt : ∀ x : Fin N → Bool, (∏ i, w p (x i)) * f (x j)
      = ∏ i, (if i = j then w p (x i) * f (x i) else w p (x i)) := by
    intro x
    have : ∀ i, (if i = j then w p (x i) * f (x i) else w p (x i))
        = w p (x i) * (if i = j then f (x i) else 1) := by
      intro i; split_ifs <;> simp
    simp_rw [this, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [hpt]
  rw [← Fintype.prod_sum (fun i b => if i = j then w p b * f b else w p b)]
  have : ∀ i, (∑ b, if i = j then w p b * f b else w p b)
      = if i = j then ∑ b, w p b * f b else 1 := by
    intro i; split_ifs <;> simp [w_add]
  simp_rw [this, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

theorem weight_total (p₁ p₂ : ℝ) (N : ℕ) :
    ∑ ω : (Fin N → Bool) × (Fin N → Bool), μ p₁ p₂ ω = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [μ]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, sum_prod_w, one_mul]

lemma sum_E_arm2 (p₂ : ℝ) {N : ℕ} (hN : 0 < N) :
    ∑ y : Fin N → Bool, (∏ i, w p₂ (y i)) * (if ext y 0 = false then (1 : ℝ) else 0)
      = 1 - p₂ := by
  have : ∀ y : Fin N → Bool, ext y 0 = y ⟨0, hN⟩ := fun y => by simp [ext, hN]
  simp_rw [this]
  rw [sum_prod_w_mul p₂ ⟨0, hN⟩ (fun b => if b = false then (1 : ℝ) else 0)]
  simp [w]

/-- Part (2): the lock-in event has probability `1 - p₂ > 0`. -/
theorem prob_lock_in (p₁ p₂ : ℝ) (hp₂ : p₂ < 1) {N : ℕ} (hN : 0 < N) :
    (∑ ω : (Fin N → Bool) × (Fin N → Bool), if E ω then μ p₁ p₂ ω else 0) = 1 - p₂
      ∧ 0 < 1 - p₂ := by
  refine ⟨?_, by linarith⟩
  rw [Fintype.sum_prod_type]
  have : ∀ (x y : Fin N → Bool), (if E (x, y) then μ p₁ p₂ (x, y) else 0)
      = (∏ i, w p₁ (x i)) * ((∏ i, w p₂ (y i)) * (if ext y 0 = false then (1 : ℝ) else 0)) := by
    intro x y; simp only [E, μ]; split_ifs <;> ring
  simp_rw [this, ← Finset.mul_sum, sum_E_arm2 p₂ hN, ← Finset.sum_mul, sum_prod_w, one_mul]

lemma sum_arm1_rewards (p₁ : ℝ) {N : ℕ} (m : ℕ) (hm : m ≤ N) :
    ∑ x : Fin N → Bool, (∏ i, w p₁ (x i)) * (∑ k ∈ Finset.range m, (val (ext x k) : ℝ))
      = m * p₁ := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ k ∈ Finset.range m,
      ∑ x : Fin N → Bool, (∏ i, w p₁ (x i)) * (val (ext x k) : ℝ) = p₁ := by
    intro k hk
    have hkN : k < N := lt_of_lt_of_le (Finset.mem_range.mp hk) hm
    have : ∀ x : Fin N → Bool, ext x k = x ⟨k, hkN⟩ := fun x => by simp [ext, hkN]
    simp_rw [this]
    rw [sum_prod_w_mul p₁ ⟨k, hkN⟩ (fun b => (val b : ℝ))]
    simp [w, val]
  rw [Finset.sum_congr rfl this]
  simp

/-- Expected total reward up to time `T` on the lock-in event. -/
theorem expected_reward_on_lock_in (p₁ p₂ : ℝ) {N T : ℕ} (hT : 2 ≤ T) (hTN : T ≤ N) :
    (∑ ω : (Fin N → Bool) × (Fin N → Bool),
        if E ω then μ p₁ p₂ ω * (total (ext ω.1) (ext ω.2) T : ℝ) else 0)
      = (1 - p₂) * ((T - 1 : ℕ) * p₁) := by
  have hN : 0 < N := by omega
  rw [Fintype.sum_prod_type]
  have : ∀ (x y : Fin N → Bool),
      (if E (x, y) then μ p₁ p₂ (x, y) * (total (ext x) (ext y) T : ℝ) else 0)
      = ((∏ i, w p₂ (y i)) * (if ext y 0 = false then (1 : ℝ) else 0)) *
        ((∏ i, w p₁ (x i)) * (∑ k ∈ Finset.range (T - 1), (val (ext x k) : ℝ))) := by
    intro x y
    simp only [E, μ]
    split_ifs with h
    · rw [total_reward_of_first_zero (ext x) (ext y) h T hT]
      push_cast; ring
    · ring
  simp_rw [this, ← Finset.sum_mul]
  rw [sum_E_arm2 p₂ hN, ← Finset.mul_sum, sum_arm1_rewards p₁ (T - 1) (by omega)]

/-- Conditional expected average reward up to time `T`, given lock-in, is `((T-1)/T) p₁`,
hence at most `p₁` and strictly below `p₂`. -/
theorem cond_avg_reward_lt (p₁ p₂ : ℝ) (hp₁ : 0 < p₁) (h12 : p₁ < p₂) (hp₂ : p₂ < 1)
    {N T : ℕ} (hT : 2 ≤ T) (hTN : T ≤ N) :
    let P := ∑ ω : (Fin N → Bool) × (Fin N → Bool), if E ω then μ p₁ p₂ ω else 0
    let R := ∑ ω : (Fin N → Bool) × (Fin N → Bool),
        if E ω then μ p₁ p₂ ω * ((total (ext ω.1) (ext ω.2) T : ℝ) / T) else 0
    R / P = ((T - 1 : ℕ) / (T : ℝ)) * p₁ ∧ R / P ≤ p₁ ∧ R / P < p₂ := by
  intro P R
  have hN : 0 < N := by omega
  have hP : P = 1 - p₂ := (prob_lock_in p₁ p₂ hp₂ hN).1
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hR : R = (1 - p₂) * ((T - 1 : ℕ) * p₁) / T := by
    have : R = (∑ ω : (Fin N → Bool) × (Fin N → Bool),
        if E ω then μ p₁ p₂ ω * (total (ext ω.1) (ext ω.2) T : ℝ) else 0) / T := by
      simp only [R]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun ω _ => ?_)
      split_ifs <;> ring
    rw [this, expected_reward_on_lock_in p₁ p₂ hT hTN]
  have hq : 0 < 1 - p₂ := by linarith
  have hval : R / P = ((T - 1 : ℕ) / (T : ℝ)) * p₁ := by
    rw [hR, hP]; field_simp
  have hfrac : ((T - 1 : ℕ) / (T : ℝ)) ≤ 1 := by
    rw [div_le_one hTpos]; exact_mod_cast (by omega : T - 1 ≤ T)
  have hle : R / P ≤ p₁ := by
    rw [hval]; nlinarith
  exact ⟨hval, hle, lt_of_le_of_lt hle h12⟩

end GreedyLocksInB
