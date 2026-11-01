import Mathlib

/-!
# Battle of the sexes: a public coin as a focal point

Two players choose `opera` or `football`. Payoffs: `(2,1)` at `(opera, opera)`,
`(1,2)` at `(football, football)`, `(0,0)` otherwise.

## PROVED

* `pureNash_iff`: the pure Nash equilibria are exactly `(opera, opera)` and
  `(football, football)`.
* `coin_expected_payoff1`, `coin_expected_payoff2`: under a public fair coin
  (heads → both opera, tails → both football) each player's expected payoff is `3/2`.
* `coin_obedient`: after each coin value, following the signal is a best response
  for each player (obedience conditional on the public signal).
* `coinDist_isCorrelatedEq`: the induced joint distribution
  (`1/2` on `(opera, opera)`, `1/2` on `(football, football)`) satisfies the standard
  correlated-equilibrium obedience inequalities; `coinDist_payoff1/2` give `3/2` each.
* `pureNash_payoff_ne`: no pure Nash equilibrium yields the payoff pair `(3/2, 3/2)`.
* `mixedNash_iff`: the mixed Nash equilibria (with `p` = P(player 1 plays opera),
  `q` = P(player 2 plays opera), over all real `p, q ∈ [0,1]`) are exactly
  `(1,1)`, `(0,0)` and `(2/3, 1/3)`.
* `mixedNash_fully_mixed`: the unique fully mixed equilibrium is `p = 2/3`, `q = 1/3`.
* `mixed_eq_payoff1`, `mixed_eq_payoff2`: it gives each player `2/3`;
  `mixed_eq_payoff_lt`: `2/3 < 3/2`.
* `mixedNash_payoff_ne`: no Nash equilibrium, pure or mixed, yields `(3/2, 3/2)`.
* `independent_payoff_ne`: no pair of independent mixed strategies at all
  (any real `p, q`) yields `(3/2, 3/2)`; the fair efficient outcome requires correlation.

## INTERPRETED (not formalized)

A shared, predictable boundary (a clock tick, a coin both see) acts as a focal point:
conditioning on it makes coordination both fair (equal expected payoffs) and efficient
(total payoff 3, versus 4/3 at the symmetric mixed equilibrium), which no uncorrelated
play achieves.
-/

namespace FocalPointPublicSignalA

/-- The two actions. -/
inductive Choice
  | opera
  | football
  deriving DecidableEq, Repr

open Choice

/-- Payoff of player 1 (first argument is player 1's action). -/
def u1 : Choice → Choice → ℝ
  | opera, opera => 2
  | football, football => 1
  | _, _ => 0

/-- Payoff of player 2. -/
def u2 : Choice → Choice → ℝ
  | opera, opera => 1
  | football, football => 2
  | _, _ => 0

/-- Pure Nash equilibrium. -/
def IsPureNash (a b : Choice) : Prop :=
  (∀ a', u1 a' b ≤ u1 a b) ∧ (∀ b', u2 a b' ≤ u2 a b)

/-! ## (1) Pure Nash equilibria -/

theorem pureNash_iff (a b : Choice) :
    IsPureNash a b ↔ (a = opera ∧ b = opera) ∨ (a = football ∧ b = football) := by
  constructor
  · rintro ⟨h1, h2⟩
    cases a <;> cases b
    · exact Or.inl ⟨rfl, rfl⟩
    · have := h1 football; simp [u1] at this; norm_num at this
    · have := h1 opera; simp [u1] at this; norm_num at this
    · exact Or.inr ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨fun a' => ?_, fun b' => ?_⟩
      · cases a' <;> norm_num [u1]
      · cases b' <;> norm_num [u2]
    · refine ⟨fun a' => ?_, fun b' => ?_⟩
      · cases a' <;> norm_num [u1]
      · cases b' <;> norm_num [u2]

/-! ## (2) Public fair coin -/

/-- The public signal: heads (`true`) → both opera; tails (`false`) → both football. -/
def signal : Bool → Choice × Choice
  | true => (opera, opera)
  | false => (football, football)

/-- Expected payoff of player 1 when both follow a fair public coin. -/
noncomputable def coinPayoff1 : ℝ :=
  (1 / 2) * u1 (signal true).1 (signal true).2 + (1 / 2) * u1 (signal false).1 (signal false).2

/-- Expected payoff of player 2 when both follow a fair public coin. -/
noncomputable def coinPayoff2 : ℝ :=
  (1 / 2) * u2 (signal true).1 (signal true).2 + (1 / 2) * u2 (signal false).1 (signal false).2

theorem coin_expected_payoff1 : coinPayoff1 = 3 / 2 := by
  norm_num [coinPayoff1, signal, u1]

theorem coin_expected_payoff2 : coinPayoff2 = 3 / 2 := by
  norm_num [coinPayoff2, signal, u2]

/-- After each signal value, following the signal is a best response for each player,
given that the other follows it. -/
theorem coin_obedient (s : Bool) :
    (∀ a', u1 a' (signal s).2 ≤ u1 (signal s).1 (signal s).2) ∧
    (∀ b', u2 (signal s).1 b' ≤ u2 (signal s).1 (signal s).2) := by
  cases s
  · exact ⟨fun a' => by cases a' <;> norm_num [signal, u1],
      fun b' => by cases b' <;> norm_num [signal, u2]⟩
  · exact ⟨fun a' => by cases a' <;> norm_num [signal, u1],
      fun b' => by cases b' <;> norm_num [signal, u2]⟩

/-- Sum over the two actions. -/
def sumC (f : Choice → ℝ) : ℝ := f opera + f football

/-- Correlated equilibrium for a joint distribution `μ` on action profiles:
a probability distribution satisfying the obedience inequalities for both players. -/
def IsCorrelatedEq (μ : Choice → Choice → ℝ) : Prop :=
  (∀ a b, 0 ≤ μ a b) ∧ sumC (fun a => sumC (fun b => μ a b)) = 1 ∧
  (∀ a a', 0 ≤ sumC (fun b => μ a b * (u1 a b - u1 a' b))) ∧
  (∀ b b', 0 ≤ sumC (fun a => μ a b * (u2 a b - u2 a b')))

/-- The joint distribution induced by the public fair coin. -/
noncomputable def coinDist : Choice → Choice → ℝ
  | opera, opera => 1 / 2
  | football, football => 1 / 2
  | _, _ => 0

theorem coinDist_isCorrelatedEq : IsCorrelatedEq coinDist := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b; cases a <;> cases b <;> norm_num [coinDist]
  · norm_num [sumC, coinDist]
  · intro a a'; cases a <;> cases a' <;> norm_num [sumC, coinDist, u1]
  · intro b b'; cases b <;> cases b' <;> norm_num [sumC, coinDist, u2]

theorem coinDist_payoff1 : sumC (fun a => sumC (fun b => coinDist a b * u1 a b)) = 3 / 2 := by
  norm_num [sumC, coinDist, u1]

theorem coinDist_payoff2 : sumC (fun a => sumC (fun b => coinDist a b * u2 a b)) = 3 / 2 := by
  norm_num [sumC, coinDist, u2]

/-! ## (3) No Nash equilibrium reaches `(3/2, 3/2)` -/

theorem pureNash_payoff_ne (a b : Choice) (h : IsPureNash a b) :
    (u1 a b, u2 a b) ≠ ((3 : ℝ) / 2, (3 : ℝ) / 2) := by
  rcases (pureNash_iff a b).1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · intro h'; simp [u1] at h'; norm_num at h'
  · intro h'; simp [u1] at h'; norm_num at h'

/-- Expected payoff of player 1 when player 1 plays opera with probability `p`
and player 2 independently plays opera with probability `q`. -/
def U1 (p q : ℝ) : ℝ :=
  p * q * u1 opera opera + p * (1 - q) * u1 opera football +
  (1 - p) * q * u1 football opera + (1 - p) * (1 - q) * u1 football football

/-- Expected payoff of player 2 under independent mixing. -/
def U2 (p q : ℝ) : ℝ :=
  p * q * u2 opera opera + p * (1 - q) * u2 opera football +
  (1 - p) * q * u2 football opera + (1 - p) * (1 - q) * u2 football football

theorem U1_eq (p q : ℝ) : U1 p q = 2 * p * q + (1 - p) * (1 - q) := by
  simp [U1, u1]; ring

theorem U2_eq (p q : ℝ) : U2 p q = p * q + 2 * (1 - p) * (1 - q) := by
  simp [U2, u2]; ring

/-- Mixed Nash equilibrium in probabilities of playing opera. -/
def IsMixedNash (p q : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1 ∧
  (∀ p', 0 ≤ p' → p' ≤ 1 → U1 p' q ≤ U1 p q) ∧
  (∀ q', 0 ≤ q' → q' ≤ 1 → U2 p q' ≤ U2 p q)

theorem mixedNash_iff (p q : ℝ) :
    IsMixedNash p q ↔ (p = 1 ∧ q = 1) ∨ (p = 0 ∧ q = 0) ∨ (p = 2 / 3 ∧ q = 1 / 3) := by
  constructor
  · rintro ⟨hp0, hp1, hq0, hq1, h1, h2⟩
    have a0 := h1 0 le_rfl zero_le_one
    have a1 := h1 1 zero_le_one le_rfl
    have b0 := h2 0 le_rfl zero_le_one
    have b1 := h2 1 zero_le_one le_rfl
    rw [U1_eq, U1_eq] at a0 a1
    rw [U2_eq, U2_eq] at b0 b1
    -- a0 : 0 ≤ p (3q-1); a1 : 0 ≤ (p-1)(3q-1); b0 : 0 ≤ q (3p-2); b1 : 0 ≤ (q-1)(3p-2)
    have a1' : 0 ≤ (p - 1) * (3 * q - 1) := by nlinarith
    have b1' : 0 ≤ (q - 1) * (3 * p - 2) := by nlinarith
    have a0' : 0 ≤ p * (3 * q - 1) := by nlinarith
    have b0' : 0 ≤ q * (3 * p - 2) := by nlinarith
    rcases lt_trichotomy (3 * q - 1) 0 with hq | hq | hq
    · -- p = 0, then q = 0
      have hp : p = 0 := by
        by_contra hne
        have : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hne)
        have : p * (3 * q - 1) < 0 := mul_neg_of_pos_of_neg this hq
        linarith
      subst hp
      have hq' : q = 0 := by
        by_contra hne
        have : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hne)
        have : q * (3 * 0 - 2) < 0 := mul_neg_of_pos_of_neg this (by norm_num)
        linarith
      exact Or.inr (Or.inl ⟨rfl, hq'⟩)
    · have hq' : q = 1 / 3 := by linarith
      subst hq'
      have hp : 3 * p - 2 = 0 := by
        rcases lt_trichotomy (3 * p - 2) 0 with h | h | h
        · nlinarith
        · exact h
        · nlinarith
      exact Or.inr (Or.inr ⟨by linarith, rfl⟩)
    · have hp : p = 1 := by
        by_contra hne
        have : p - 1 < 0 := by
          have : p < 1 := lt_of_le_of_ne hp1 hne
          linarith
        have : (p - 1) * (3 * q - 1) < 0 := mul_neg_of_neg_of_pos this hq
        linarith
      subst hp
      have hq' : q = 1 := by
        by_contra hne
        have : q - 1 < 0 := by
          have : q < 1 := lt_of_le_of_ne hq1 hne
          linarith
        have : (q - 1) * (3 * 1 - 2) < 0 := mul_neg_of_neg_of_pos this (by norm_num)
        linarith
      exact Or.inl ⟨rfl, hq'⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨by norm_num, le_rfl, by norm_num, le_rfl, ?_, ?_⟩
      · intro p' _ hp'; rw [U1_eq, U1_eq]; nlinarith
      · intro q' _ hq'; rw [U2_eq, U2_eq]; nlinarith
    · refine ⟨le_rfl, by norm_num, le_rfl, by norm_num, ?_, ?_⟩
      · intro p' hp' _; rw [U1_eq, U1_eq]; nlinarith
      · intro q' hq' _; rw [U2_eq, U2_eq]; nlinarith
    · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
      · intro p' _ _; rw [U1_eq, U1_eq]; nlinarith
      · intro q' _ _; rw [U2_eq, U2_eq]; nlinarith

/-- The unique fully mixed equilibrium: player 1 plays opera with probability `2/3`,
player 2 with probability `1/3`. -/
theorem mixedNash_fully_mixed (p q : ℝ) (hp : 0 < p ∧ p < 1) (_hq : 0 < q ∧ q < 1) :
    IsMixedNash p q ↔ p = 2 / 3 ∧ q = 1 / 3 := by
  rw [mixedNash_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | h)
    · exact absurd h (ne_of_lt hp.2)
    · exact absurd h (ne_of_gt hp.1)
    · exact h
  · exact fun h => Or.inr (Or.inr h)

theorem mixed_eq_payoff1 : U1 (2 / 3) (1 / 3) = 2 / 3 := by
  rw [U1_eq]; norm_num

theorem mixed_eq_payoff2 : U2 (2 / 3) (1 / 3) = 2 / 3 := by
  rw [U2_eq]; norm_num

theorem mixed_eq_payoff_lt : (2 : ℝ) / 3 < 3 / 2 := by norm_num

/-- No pair of independent mixed strategies (any real `p, q`) yields `(3/2, 3/2)`. -/
theorem independent_payoff_ne (p q : ℝ) :
    (U1 p q, U2 p q) ≠ ((3 : ℝ) / 2, (3 : ℝ) / 2) := by
  intro h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [U1_eq] at h1
  rw [U2_eq] at h2
  have hpq : p * q = 1 / 2 := by linarith
  have hsum : p + q = 1 := by nlinarith
  have : q = 1 - p := by linarith
  subst this
  nlinarith [sq_nonneg (2 * p - 1)]

/-- No Nash equilibrium, pure or mixed, yields `(3/2, 3/2)`. -/
theorem mixedNash_payoff_ne (p q : ℝ) (_h : IsMixedNash p q) :
    (U1 p q, U2 p q) ≠ ((3 : ℝ) / 2, (3 : ℝ) / 2) :=
  independent_payoff_ne p q

end FocalPointPublicSignalA
