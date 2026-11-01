import Mathlib

/-!
# Averaged level-k play in matching pennies is the mixed equilibrium

Actions are `Bool`. The Matcher wins iff the two actions are equal. Level 0
for both players is `true`; a level-(k+1) Matcher plays what a level-k
Mismatcher plays; a level-(k+1) Mismatcher plays the negation of what a
level-k Matcher plays (the recursion of `scratch/yomi/YomiCycleA.lean`,
restated here).

PROVED
* `matcher_window_four`, `mismatcher_window_four`: for every `k`, among the
  levels `k, k+1, k+2, k+3` exactly 2 have action `true`, for each player.
* `matcher_count_four_mul`, `mismatcher_count_four_mul`: over the first `4m`
  levels the count of `true` is exactly `2m`;
  `matcher_freq_four_mul`, `mismatcher_freq_four_mul`: for `m ≠ 0` the
  empirical frequency `(count : ℝ) / (4m : ℝ)` equals `1/2`.
* `matcher_count_bound`, `mismatcher_count_bound`: over the first `N` levels,
  `|2 * count - N| ≤ 2` in `ℤ`;
  `matcher_freq_near_half`, `mismatcher_freq_near_half`: for `N ≠ 0`,
  `|(count : ℝ) / N - 1/2| ≤ 1/N`.
* `matcher_pure_strictly_better`: if the Mismatcher plays `true` with
  probability `q ≠ 1/2`, then for every mixing probability `p ∈ (0,1)` the
  pure action `decide (1/2 < q)` gives the Matcher a strictly higher expected
  payoff; `mismatcher_pure_strictly_better` is the symmetric statement with
  pure action `decide (p < 1/2)`.
* `isNash_half`: `(1/2, 1/2)` is a mixed Nash equilibrium;
  `isNash_iff`: `IsNash p q ↔ p = 1/2 ∧ q = 1/2`;
  `existsUnique_nash`: the equilibrium is unique.

INTERPRETED
* `trueCount f k n` is the number of `i < n` with `f (k + i) = true`, i.e. the
  number of `true` actions among levels `k, …, k+n-1`; `firstCount f N` is
  `trueCount f 0 N`. The empirical frequency is `firstCount f N / N` in `ℝ`.
* A mixed strategy is the probability of playing `true`. Expected payoff is
  the probability of winning: `matcherPayoff p q = p q + (1-p)(1-q)`,
  `mismatcherPayoff p q = p (1-q) + (1-p) q`. A pure action `b` is the
  probability `pureProb b ∈ {0,1}`.
* `IsNash p q`: both lie in `[0,1]` and neither player has a profitable
  unilateral deviation to any probability in `[0,1]`.
* Reading: endless mutual reading (the level-k recursion), averaged over
  levels, yields the mixed equilibrium `(1/2, 1/2)`, which a reflective oracle
  reaches in one step as its fixed point.
-/

namespace YomiAverageIsNashA

mutual
/-- Action of a level-`k` Matcher. -/
def matcher : ℕ → Bool
  | 0 => true
  | k + 1 => mismatcher k
/-- Action of a level-`k` Mismatcher. -/
def mismatcher : ℕ → Bool
  | 0 => true
  | k + 1 => !(matcher k)
end

@[simp] theorem matcher_zero : matcher 0 = true := by simp [matcher]
@[simp] theorem mismatcher_zero : mismatcher 0 = true := by simp [mismatcher]
@[simp] theorem matcher_succ (k : ℕ) : matcher (k + 1) = mismatcher k := by
  simp [matcher]
@[simp] theorem mismatcher_succ (k : ℕ) : mismatcher (k + 1) = !(matcher k) := by
  simp [mismatcher]

theorem matcher_add_two (k : ℕ) : matcher (k + 2) = !(matcher k) := by simp

theorem mismatcher_add_two (k : ℕ) : mismatcher (k + 2) = !(mismatcher k) := by simp

theorem matcher_add_four (k : ℕ) : matcher (k + 4) = matcher k := by simp

theorem mismatcher_add_four (k : ℕ) : mismatcher (k + 4) = mismatcher k := by simp

/-- Number of `i < n` with `f (k + i) = true`. -/
def trueCount (f : ℕ → Bool) (k n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun i => f (k + i) = true)).card

/-- Number of `true` actions among the first `N` levels. -/
def firstCount (f : ℕ → Bool) (N : ℕ) : ℕ := trueCount f 0 N

theorem trueCount_eq_sum (f : ℕ → Bool) (k n : ℕ) :
    trueCount f k n = ∑ i ∈ Finset.range n, if f (k + i) = true then 1 else 0 := by
  unfold trueCount
  rw [Finset.card_filter]

theorem trueCount_add (f : ℕ → Bool) (k a b : ℕ) :
    trueCount f k (a + b) = trueCount f k a + trueCount f (k + a) b := by
  simp only [trueCount_eq_sum, Finset.sum_range_add, add_assoc]

theorem window_four_of_add_two (f : ℕ → Bool) (h : ∀ k, f (k + 2) = !(f k)) (k : ℕ) :
    trueCount f k 4 = 2 := by
  rw [trueCount_eq_sum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have h2 : f (k + 2) = !(f k) := h k
  have h3 : f (k + 3) = !(f (k + 1)) := by
    have := h (k + 1); rwa [show k + 1 + 2 = k + 3 by ring] at this
  rw [h2, h3]
  cases f (k + 0) <;> cases f k <;> cases f (k + 1) <;> simp_all

/-- (1) Among any 4 consecutive Matcher levels, exactly 2 play `true`. -/
theorem matcher_window_four (k : ℕ) : trueCount matcher k 4 = 2 :=
  window_four_of_add_two matcher matcher_add_two k

/-- (1) Among any 4 consecutive Mismatcher levels, exactly 2 play `true`. -/
theorem mismatcher_window_four (k : ℕ) : trueCount mismatcher k 4 = 2 :=
  window_four_of_add_two mismatcher mismatcher_add_two k

theorem count_four_mul_of_add_two (f : ℕ → Bool) (h : ∀ k, f (k + 2) = !(f k)) (m : ℕ) :
    firstCount f (4 * m) = 2 * m := by
  induction m with
  | zero => simp [firstCount, trueCount]
  | succ m ih =>
    unfold firstCount at ih ⊢
    rw [show 4 * (m + 1) = 4 * m + 4 by ring, trueCount_add, ih,
      window_four_of_add_two f h]
    ring

/-- (2) Over the first `4m` levels the Matcher plays `true` exactly `2m` times. -/
theorem matcher_count_four_mul (m : ℕ) : firstCount matcher (4 * m) = 2 * m :=
  count_four_mul_of_add_two matcher matcher_add_two m

/-- (2) Over the first `4m` levels the Mismatcher plays `true` exactly `2m` times. -/
theorem mismatcher_count_four_mul (m : ℕ) : firstCount mismatcher (4 * m) = 2 * m :=
  count_four_mul_of_add_two mismatcher mismatcher_add_two m

/-- (2) The Matcher's empirical frequency of `true` over the first `4m` levels is `1/2`. -/
theorem matcher_freq_four_mul (m : ℕ) (hm : m ≠ 0) :
    ((firstCount matcher (4 * m) : ℕ) : ℝ) / ((4 * m : ℕ) : ℝ) = 1 / 2 := by
  rw [matcher_count_four_mul]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  push_cast
  field_simp
  ring

/-- (2) The Mismatcher's empirical frequency of `true` over the first `4m` levels is `1/2`. -/
theorem mismatcher_freq_four_mul (m : ℕ) (hm : m ≠ 0) :
    ((firstCount mismatcher (4 * m) : ℕ) : ℝ) / ((4 * m : ℕ) : ℝ) = 1 / 2 := by
  rw [mismatcher_count_four_mul]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  push_cast
  field_simp
  ring

theorem trueCount_shift_four_mul (f : ℕ → Bool) (h4 : ∀ k, f (k + 4) = f k) (q r : ℕ) :
    trueCount f (4 * q) r = trueCount f 0 r := by
  have hf : ∀ i, f (4 * q + i) = f i := by
    intro i
    induction q with
    | zero => simp
    | succ q ih => rw [show 4 * (q + 1) + i = (4 * q + i) + 4 by ring, h4, ih]
  unfold trueCount
  simp only [hf, zero_add]

theorem count_split (f : ℕ → Bool) (h : ∀ k, f (k + 2) = !(f k)) (N : ℕ) :
    firstCount f N = 2 * (N / 4) + trueCount f 0 (N % 4) := by
  have h4 : ∀ k, f (k + 4) = f k := by
    intro k; rw [show k + 4 = (k + 2) + 2 by ring, h, h]; simp
  conv_lhs => rw [← Nat.div_add_mod N 4]
  unfold firstCount
  rw [trueCount_add, zero_add, trueCount_shift_four_mul f h4]
  have := count_four_mul_of_add_two f h (N / 4)
  unfold firstCount at this
  rw [this]

/-- (2) Over the first `N` levels, `|2 · (Matcher's true count) - N| ≤ 2`. -/
theorem matcher_count_bound (N : ℕ) :
    |2 * (firstCount matcher N : ℤ) - N| ≤ 2 := by
  rw [count_split matcher matcher_add_two N]
  have hr : N % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hN : (N : ℤ) = 4 * ((N / 4 : ℕ) : ℤ) + ((N % 4 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod N 4).symm
  rw [hN]
  generalize N / 4 = q
  generalize hr' : N % 4 = r at hr ⊢
  have hc : r ≤ 2 * trueCount matcher 0 r + 2 ∧ 2 * trueCount matcher 0 r ≤ r + 2 := by
    interval_cases r <;>
      simp only [trueCount_eq_sum, Finset.sum_range_succ, Finset.sum_range_zero] <;> simp
  rw [abs_le]
  constructor <;> push_cast <;> omega

/-- (2) Over the first `N` levels, `|2 · (Mismatcher's true count) - N| ≤ 2`. -/
theorem mismatcher_count_bound (N : ℕ) :
    |2 * (firstCount mismatcher N : ℤ) - N| ≤ 2 := by
  rw [count_split mismatcher mismatcher_add_two N]
  have hr : N % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hN : (N : ℤ) = 4 * ((N / 4 : ℕ) : ℤ) + ((N % 4 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod N 4).symm
  rw [hN]
  generalize N / 4 = q
  generalize hr' : N % 4 = r at hr ⊢
  have hc : r ≤ 2 * trueCount mismatcher 0 r + 2 ∧ 2 * trueCount mismatcher 0 r ≤ r + 2 := by
    interval_cases r <;>
      simp only [trueCount_eq_sum, Finset.sum_range_succ, Finset.sum_range_zero] <;> simp
  rw [abs_le]
  constructor <;> push_cast <;> omega

theorem freq_near_half_of_bound (c N : ℕ) (hN : N ≠ 0) (h : |2 * (c : ℤ) - N| ≤ 2) :
    |(c : ℝ) / (N : ℝ) - 1 / 2| ≤ 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have h' : |2 * (c : ℝ) - N| ≤ 2 := by exact_mod_cast h
  have key : (c : ℝ) / N - 1 / 2 = (2 * c - N) / (2 * N) := by
    field_simp
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * N),
    div_le_div_iff₀ (by positivity) hNpos]
  nlinarith

/-- (2) The Matcher's empirical frequency over the first `N` levels is within `1/N` of `1/2`. -/
theorem matcher_freq_near_half (N : ℕ) (hN : N ≠ 0) :
    |((firstCount matcher N : ℕ) : ℝ) / (N : ℝ) - 1 / 2| ≤ 1 / (N : ℝ) :=
  freq_near_half_of_bound _ N hN (matcher_count_bound N)

/-- (2) The Mismatcher's empirical frequency over the first `N` levels is within `1/N`
of `1/2`. -/
theorem mismatcher_freq_near_half (N : ℕ) (hN : N ≠ 0) :
    |((firstCount mismatcher N : ℕ) : ℝ) / (N : ℝ) - 1 / 2| ≤ 1 / (N : ℝ) :=
  freq_near_half_of_bound _ N hN (mismatcher_count_bound N)

/-! ### Mixed strategies in matching pennies -/

/-- Probability that the Matcher wins when it plays `true` with probability `p` and the
Mismatcher plays `true` with probability `q`. -/
def matcherPayoff (p q : ℝ) : ℝ := p * q + (1 - p) * (1 - q)

/-- Probability that the Mismatcher wins. -/
def mismatcherPayoff (p q : ℝ) : ℝ := p * (1 - q) + (1 - p) * q

/-- The probability of `true` under the pure action `b`. -/
def pureProb (b : Bool) : ℝ := if b then 1 else 0

/-- Mixed Nash equilibrium of matching pennies. -/
def IsNash (p q : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1 ∧
  (∀ p', 0 ≤ p' → p' ≤ 1 → matcherPayoff p' q ≤ matcherPayoff p q) ∧
  (∀ q', 0 ≤ q' → q' ≤ 1 → mismatcherPayoff p q' ≤ mismatcherPayoff p q)

/-- (3) If the Mismatcher plays `true` with probability `q ≠ 1/2`, the pure action
`decide (1/2 < q)` is strictly better for the Matcher than any proper mixture. -/
theorem matcher_pure_strictly_better (q : ℝ) (hq : q ≠ 1 / 2) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) :
    matcherPayoff p q < matcherPayoff (pureProb (decide (1 / 2 < q))) q := by
  unfold matcherPayoff pureProb
  rcases lt_or_gt_of_ne hq with h | h
  · have : ¬ (1 / 2 < q) := not_lt.mpr h.le
    simp only [this, decide_false, Bool.false_eq_true, ite_false]
    nlinarith
  · simp only [h, decide_true, ite_true]
    nlinarith

/-- (3) If the Matcher plays `true` with probability `p ≠ 1/2`, the pure action
`decide (p < 1/2)` is strictly better for the Mismatcher than any proper mixture. -/
theorem mismatcher_pure_strictly_better (p : ℝ) (hp : p ≠ 1 / 2) (q : ℝ) (hq0 : 0 < q)
    (hq1 : q < 1) :
    mismatcherPayoff p q < mismatcherPayoff p (pureProb (decide (p < 1 / 2))) := by
  unfold mismatcherPayoff pureProb
  rcases lt_or_gt_of_ne hp with h | h
  · simp only [h, decide_true, ite_true]
    nlinarith
  · have : ¬ (p < 1 / 2) := not_lt.mpr h.le
    simp only [this, decide_false, Bool.false_eq_true, ite_false]
    nlinarith

/-- (3) `(1/2, 1/2)` is a mixed Nash equilibrium. -/
theorem isNash_half : IsNash (1 / 2) (1 / 2) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · intro p' _ _; unfold matcherPayoff; nlinarith
  · intro q' _ _; unfold mismatcherPayoff; nlinarith

/-- (3) The equilibrium conditions force both probabilities to `1/2`. -/
theorem isNash_iff (p q : ℝ) : IsNash p q ↔ p = 1 / 2 ∧ q = 1 / 2 := by
  constructor
  · rintro ⟨hp0, hp1, hq0, hq1, hM, hW⟩
    have a0 := hM 0 le_rfl zero_le_one
    have a1 := hM 1 zero_le_one le_rfl
    have b0 := hW 0 le_rfl zero_le_one
    have b1 := hW 1 zero_le_one le_rfl
    unfold matcherPayoff at a0 a1
    unfold mismatcherPayoff at b0 b1
    have hq : q = 1 / 2 := by
      rcases lt_trichotomy q (1 / 2) with h | h | h
      · exfalso
        have hp : p = 0 := by nlinarith
        subst hp
        nlinarith
      · exact h
      · exfalso
        have hp : p = 1 := by nlinarith
        subst hp
        nlinarith
    subst hq
    refine ⟨?_, rfl⟩
    rcases lt_trichotomy p (1 / 2) with h | h | h
    · exfalso; nlinarith
    · exact h
    · exfalso; nlinarith
  · rintro ⟨rfl, rfl⟩
    exact isNash_half

/-- (3) `(1/2, 1/2)` is the unique mixed Nash equilibrium of matching pennies. -/
theorem existsUnique_nash : ∃! pq : ℝ × ℝ, IsNash pq.1 pq.2 := by
  refine ⟨(1 / 2, 1 / 2), isNash_half, ?_⟩
  rintro ⟨p, q⟩ h
  obtain ⟨hp, hq⟩ := (isNash_iff p q).mp h
  simp [hp, hq]

end YomiAverageIsNashA
