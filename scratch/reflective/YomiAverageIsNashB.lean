import Mathlib

/-!
# Yomi levels average to the matching-pennies equilibrium

Matching pennies: the Matcher wins iff both actions are equal, the Mismatcher
wins iff they differ. Level 0 for both players is the fixed action `true`. A
level-(k+1) Matcher plays what a level-k Mismatcher plays; a level-(k+1)
Mismatcher plays the negation of what a level-k Matcher plays (the recursion of
`scratch/yomi/YomiCycleA.lean`, restated here).

PROVED
* `matcher_window_count`, `mismatcher_window_count`: over any 4 consecutive
  levels `k, …, k+3` each player plays `true` exactly 2 times
  (`((Finset.range 4).filter (fun i => f (k + i) = true)).card = 2`).
* `matcher_trueCount_four_mul`, `mismatcher_trueCount_four_mul`: among the first
  `4m` levels each player plays `true` exactly `2m` times;
  `matcher_freq_four_mul`, `mismatcher_freq_four_mul`: hence the empirical
  frequency `(count : ℝ) / (4m)` equals `1/2` for `m > 0`.
* `matcher_trueCount_dev`, `mismatcher_trueCount_dev`: for every `N`,
  `|2 · count N - N| ≤ 2` in `ℤ`; `matcher_freq_near_half`,
  `mismatcher_freq_near_half`: for `N > 0`,
  `|(count N : ℝ) / N - 1/2| ≤ 1/N`. `matcher_freq_bound_tight`: the bound is
  attained for the Matcher at `N = 2`.
* `matcherPayoff_eq`: with ±1 payoffs, the Matcher's expected payoff at mixed
  profile `(p, q)` is `(2p - 1)(2q - 1)`; the game is zero-sum.
* `isNash_half`: `(1/2, 1/2)` is a mixed Nash equilibrium.
* `matcher_pure_strictly_better`: if `q ≠ 1/2`, for every strictly mixed
  `p ∈ (0,1)` some pure Matcher action has strictly higher payoff;
  `mismatcher_pure_strictly_better`: symmetrically for the Mismatcher when
  `p ≠ 1/2`.
* `isNash_iff`: `IsNash p q ↔ p = 1/2 ∧ q = 1/2` (uniqueness of the mixed
  equilibrium).

INTERPRETED
* `p` (resp. `q`) is the probability that the Matcher (resp. Mismatcher) plays
  `true`; `IsNash p q` means both lie in `[0,1]` and neither player gains by any
  unilateral deviation to another probability in `[0,1]`.
* Payoffs: Matcher gets `+1` on equal actions and `-1` otherwise; the
  Mismatcher gets the negative.
* Reading: endless mutual reading of levels, averaged over levels, gives the
  equilibrium `(1/2, 1/2)` that a reflective oracle reaches in one step. This
  reading is not itself a theorem here.
-/

namespace YomiAverageIsNashB

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

/-! ## Window counts -/

/-- Number of `true`s among levels `k, …, k+3`. -/
def windowCount (f : ℕ → Bool) (k : ℕ) : ℕ :=
  ((Finset.range 4).filter (fun i => f (k + i) = true)).card

/-- Number of `true`s among the first `N` levels `0, …, N-1`. -/
def trueCount (f : ℕ → Bool) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun i => f i = true)).card

theorem windowCount_eq (f : ℕ → Bool) (k : ℕ) :
    windowCount f k = (if f k = true then 1 else 0) + (if f (k + 1) = true then 1 else 0)
      + (if f (k + 2) = true then 1 else 0) + (if f (k + 3) = true then 1 else 0) := by
  unfold windowCount
  rw [Finset.card_filter, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]

/-- (1) Over any 4 consecutive levels the Matcher plays `true` exactly twice. -/
theorem matcher_window_count (k : ℕ) :
    ((Finset.range 4).filter (fun i => matcher (k + i) = true)).card = 2 := by
  change windowCount matcher k = 2
  rw [windowCount_eq]
  simp only [matcher_succ, mismatcher_succ, show k + 2 = k + 1 + 1 from rfl,
    show k + 3 = k + 1 + 1 + 1 from rfl]
  cases matcher k <;> cases mismatcher k <;> rfl

/-- (1) Over any 4 consecutive levels the Mismatcher plays `true` exactly twice. -/
theorem mismatcher_window_count (k : ℕ) :
    ((Finset.range 4).filter (fun i => mismatcher (k + i) = true)).card = 2 := by
  change windowCount mismatcher k = 2
  rw [windowCount_eq]
  simp only [matcher_succ, mismatcher_succ, show k + 2 = k + 1 + 1 from rfl,
    show k + 3 = k + 1 + 1 + 1 from rfl, Bool.not_not]
  cases matcher k <;> cases mismatcher k <;> rfl

theorem trueCount_add_four (f : ℕ → Bool) (n : ℕ) :
    trueCount f (n + 4) = trueCount f n + windowCount f n := by
  unfold trueCount windowCount
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.sum_range_add]

theorem trueCount_four_mul_add (f : ℕ → Bool) (hf : ∀ k, windowCount f k = 2)
    (q r : ℕ) : trueCount f (4 * q + r) = 2 * q + trueCount f r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 4 * (q + 1) + r = (4 * q + r) + 4 by ring, trueCount_add_four, ih, hf]
    ring

/-! ## Empirical frequencies -/

/-- (2) Among the first `4m` levels the Matcher plays `true` exactly `2m` times. -/
theorem matcher_trueCount_four_mul (m : ℕ) : trueCount matcher (4 * m) = 2 * m := by
  simpa [trueCount] using trueCount_four_mul_add matcher matcher_window_count m 0

/-- (2) Among the first `4m` levels the Mismatcher plays `true` exactly `2m` times. -/
theorem mismatcher_trueCount_four_mul (m : ℕ) : trueCount mismatcher (4 * m) = 2 * m := by
  simpa [trueCount] using trueCount_four_mul_add mismatcher mismatcher_window_count m 0

theorem freq_of_count {c m : ℕ} (hm : 0 < m) (hc : c = 2 * m) :
    (c : ℝ) / (4 * m : ℕ) = 1 / 2 := by
  subst hc
  have : (0 : ℝ) < m := by exact_mod_cast hm
  push_cast
  field_simp
  ring

/-- (2) The Matcher's empirical frequency of `true` over the first `4m` levels is `1/2`. -/
theorem matcher_freq_four_mul (m : ℕ) (hm : 0 < m) :
    (trueCount matcher (4 * m) : ℝ) / (4 * m : ℕ) = 1 / 2 :=
  freq_of_count hm (matcher_trueCount_four_mul m)

/-- (2) The Mismatcher's empirical frequency of `true` over the first `4m` levels is `1/2`. -/
theorem mismatcher_freq_four_mul (m : ℕ) (hm : 0 < m) :
    (trueCount mismatcher (4 * m) : ℝ) / (4 * m : ℕ) = 1 / 2 :=
  freq_of_count hm (mismatcher_trueCount_four_mul m)

theorem trueCount_dev (f : ℕ → Bool) (hf : ∀ k, windowCount f k = 2)
    (h0 : |2 * (trueCount f 0 : ℤ) - 0| ≤ 2) (h1 : |2 * (trueCount f 1 : ℤ) - 1| ≤ 2)
    (h2 : |2 * (trueCount f 2 : ℤ) - 2| ≤ 2) (h3 : |2 * (trueCount f 3 : ℤ) - 3| ≤ 2)
    (N : ℕ) : |2 * (trueCount f N : ℤ) - N| ≤ 2 := by
  have hN := (Nat.div_add_mod N 4).symm
  have hr : N % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rw [hN, trueCount_four_mul_add f hf]
  have key : ∀ r, r < 4 → |2 * (trueCount f r : ℤ) - r| ≤ 2 := by
    intro r hr
    interval_cases r <;> assumption
  have := key (N % 4) hr
  push_cast
  calc |2 * ((2 : ℤ) * (N / 4 : ℕ) + (trueCount f (N % 4) : ℤ)) - (4 * (N / 4 : ℕ) + (N % 4 : ℕ))|
      = |2 * (trueCount f (N % 4) : ℤ) - (N % 4 : ℕ)| := by ring_nf
    _ ≤ 2 := this

/-- (2) For every `N`, `|2 · (# Matcher trues in first N levels) - N| ≤ 2`. -/
theorem matcher_trueCount_dev (N : ℕ) : |2 * (trueCount matcher N : ℤ) - N| ≤ 2 :=
  trueCount_dev matcher matcher_window_count (by decide) (by decide) (by decide)
    (by decide) N

/-- (2) For every `N`, `|2 · (# Mismatcher trues in first N levels) - N| ≤ 2`. -/
theorem mismatcher_trueCount_dev (N : ℕ) : |2 * (trueCount mismatcher N : ℤ) - N| ≤ 2 :=
  trueCount_dev mismatcher mismatcher_window_count (by decide) (by decide) (by decide)
    (by decide) N

theorem freq_near_half_of_dev {c N : ℕ} (hN : 0 < N) (h : |2 * (c : ℤ) - N| ≤ 2) :
    |(c : ℝ) / N - 1 / 2| ≤ 1 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hR : |2 * (c : ℝ) - N| ≤ 2 := by exact_mod_cast h
  have e : (c : ℝ) / N - 1 / 2 = (2 * (c : ℝ) - N) / (2 * N) := by
    field_simp
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * N)]
  rw [div_le_div_iff₀ (by positivity) hNr]
  nlinarith

/-- (2) For `N > 0`, the Matcher's empirical frequency of `true` over the first `N`
levels is within `1/N` of `1/2`. -/
theorem matcher_freq_near_half (N : ℕ) (hN : 0 < N) :
    |(trueCount matcher N : ℝ) / N - 1 / 2| ≤ 1 / N :=
  freq_near_half_of_dev hN (matcher_trueCount_dev N)

/-- (2) For `N > 0`, the Mismatcher's empirical frequency of `true` over the first `N`
levels is within `1/N` of `1/2`. -/
theorem mismatcher_freq_near_half (N : ℕ) (hN : 0 < N) :
    |(trueCount mismatcher N : ℝ) / N - 1 / 2| ≤ 1 / N :=
  freq_near_half_of_dev hN (mismatcher_trueCount_dev N)

/-- The `1/N` bound is attained by the Matcher at `N = 2` (levels 0 and 1 both play
`true`). -/
theorem matcher_freq_bound_tight :
    |(trueCount matcher 2 : ℝ) / (2 : ℕ) - 1 / 2| = 1 / (2 : ℕ) := by
  have : trueCount matcher 2 = 2 := by decide
  rw [this]
  norm_num

/-! ## Matching pennies -/

/-- Matcher's expected payoff (`+1` on equal actions, `-1` otherwise) when the Matcher
plays `true` with probability `p` and the Mismatcher with probability `q`. -/
def matcherPayoff (p q : ℝ) : ℝ :=
  (p * q + (1 - p) * (1 - q)) - (p * (1 - q) + (1 - p) * q)

/-- Mismatcher's expected payoff (zero-sum). -/
def mismatcherPayoff (p q : ℝ) : ℝ := -matcherPayoff p q

theorem matcherPayoff_eq (p q : ℝ) : matcherPayoff p q = (2 * p - 1) * (2 * q - 1) := by
  unfold matcherPayoff; ring

/-- Mixed Nash equilibrium of matching pennies. -/
def IsNash (p q : ℝ) : Prop :=
  (0 ≤ p ∧ p ≤ 1) ∧ (0 ≤ q ∧ q ≤ 1) ∧
  (∀ p', 0 ≤ p' → p' ≤ 1 → matcherPayoff p' q ≤ matcherPayoff p q) ∧
  (∀ q', 0 ≤ q' → q' ≤ 1 → mismatcherPayoff p q' ≤ mismatcherPayoff p q)

/-- Probability of `true` for a pure action. -/
def pure (b : Bool) : ℝ := if b then 1 else 0

theorem isNash_half : IsNash (1 / 2) (1 / 2) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
  · intro p' _ _; simp [matcherPayoff_eq]
  · intro q' _ _; simp [mismatcherPayoff, matcherPayoff_eq]

/-- (3) If the Mismatcher's probability `q` is not `1/2`, then against it every strictly
mixed Matcher strategy is strictly beaten by some pure Matcher action. -/
theorem matcher_pure_strictly_better (q : ℝ) (hq : q ≠ 1 / 2) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) : ∃ b : Bool, matcherPayoff p q < matcherPayoff (pure b) q := by
  rcases lt_or_gt_of_ne hq with h | h
  · refine ⟨false, ?_⟩
    simp only [pure, matcherPayoff_eq]
    norm_num
    nlinarith
  · refine ⟨true, ?_⟩
    simp only [pure, matcherPayoff_eq]
    norm_num
    nlinarith

/-- (3) If the Matcher's probability `p` is not `1/2`, then against it every strictly
mixed Mismatcher strategy is strictly beaten by some pure Mismatcher action. -/
theorem mismatcher_pure_strictly_better (p : ℝ) (hp : p ≠ 1 / 2) (q : ℝ) (hq0 : 0 < q)
    (hq1 : q < 1) : ∃ b : Bool, mismatcherPayoff p q < mismatcherPayoff p (pure b) := by
  rcases lt_or_gt_of_ne hp with h | h
  · refine ⟨true, ?_⟩
    simp only [pure, mismatcherPayoff, matcherPayoff_eq]
    norm_num
    nlinarith
  · refine ⟨false, ?_⟩
    simp only [pure, mismatcherPayoff, matcherPayoff_eq]
    norm_num
    nlinarith

/-- (3) `(1/2, 1/2)` is the unique mixed Nash equilibrium of matching pennies. -/
theorem isNash_iff (p q : ℝ) : IsNash p q ↔ p = 1 / 2 ∧ q = 1 / 2 := by
  constructor
  · rintro ⟨_, _, hM, hN⟩
    have a1 := hM 1 (by norm_num) le_rfl
    have a0 := hM 0 le_rfl (by norm_num)
    have b1 := hN 1 (by norm_num) le_rfl
    have b0 := hN 0 le_rfl (by norm_num)
    simp only [mismatcherPayoff, matcherPayoff_eq] at a1 a0 b1 b0
    set x := 2 * p - 1 with hx
    set y := 2 * q - 1 with hy
    have hyabs : |y| ≤ x * y := abs_le'.mpr ⟨by linarith, by linarith⟩
    have hxabs : |x| ≤ -(x * y) := abs_le'.mpr ⟨by linarith, by linarith⟩
    have hx0 : x = 0 := by
      have := abs_nonneg y; have := abs_nonneg x
      exact abs_eq_zero.mp (by linarith)
    have hy0 : y = 0 := by
      have := abs_nonneg y; have := abs_nonneg x
      exact abs_eq_zero.mp (by linarith)
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    exact isNash_half

end YomiAverageIsNashB
