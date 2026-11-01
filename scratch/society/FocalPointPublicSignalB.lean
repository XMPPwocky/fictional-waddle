import Mathlib

/-!
# Battle of the sexes: a public fair coin as a focal point

Two players choose `Opera` or `Football`. Payoffs are `(2,1)` at `(Opera, Opera)`,
`(1,2)` at `(Football, Football)`, and `(0,0)` otherwise.

PROVED
* `pureNash_iff`: the pure Nash equilibria are exactly `(Opera, Opera)` and
  `(Football, Football)`.
* `coin_expected_payoff1`, `coin_expected_payoff2`: under the public fair coin
  (heads → both Opera, tails → both Football) each player's expected payoff is `3/2`.
* `coin_follow_best_response1`, `coin_follow_best_response2`: after each signal value,
  following the recommendation is a best response to the other player following it.
* `coin_follow_best_strategy1`, `coin_follow_best_strategy2`: no signal-contingent
  deviation `Bool → Act` improves a player's expected payoff (ex-ante form).
* `coin_isCorrelatedEq`: the induced distribution (1/2 on `(O,O)`, 1/2 on `(F,F)`)
  satisfies the standard correlated-equilibrium inequalities; `coinDist_eq` shows it is
  the law of the coin's recommendation, and `coinDist_payoffs` gives expected payoffs `3/2`.
* `no_pureNash_fair`: no pure Nash equilibrium yields payoffs `(3/2, 3/2)`.
* `mixedNash_iff`: the (independently) mixed Nash equilibria, with `p` = probability
  player 1 plays Opera and `q` = probability player 2 plays Opera, are exactly
  `(1,1)`, `(0,0)` and `(2/3, 1/3)`.
* `mixedNash_interior`: the unique completely mixed equilibrium is `p = 2/3, q = 1/3`.
* `mixed_eq_payoffs`: at that equilibrium each player gets `2/3`.
* `no_mixedNash_fair`: no mixed Nash equilibrium (pure ones included) yields `(3/2, 3/2)`.
* `no_independent_fair`: no independent mixed profile at all, equilibrium or not,
  yields `(3/2, 3/2)`; the fair efficient payoff requires correlation.

INTERPRETED (not formalized)
* A shared, predictable boundary (a clock tick, a coin both see) is a focal point that
  makes coordination fair and efficient: the public signal achieves the symmetric
  efficient payoff `(3/2, 3/2)`, which no independent randomization, and in particular
  no Nash equilibrium, achieves.
-/

namespace FocalPointPublicSignalB

noncomputable section

inductive Act
  | opera
  | football
  deriving DecidableEq, Repr

instance : Fintype Act where
  elems := {Act.opera, Act.football}
  complete := fun x => by cases x <;> simp

open Act

/-- Payoff to player 1 (row) when player 1 plays `a` and player 2 plays `b`. -/
def u1 : Act → Act → ℝ
  | opera, opera => 2
  | football, football => 1
  | _, _ => 0

/-- Payoff to player 2 (column) when player 1 plays `a` and player 2 plays `b`. -/
def u2 : Act → Act → ℝ
  | opera, opera => 1
  | football, football => 2
  | _, _ => 0

/-- Pure Nash equilibrium. -/
def IsPureNash (a b : Act) : Prop :=
  (∀ a', u1 a' b ≤ u1 a b) ∧ (∀ b', u2 a b' ≤ u2 a b)

theorem pureNash_iff (a b : Act) :
    IsPureNash a b ↔ (a = opera ∧ b = opera) ∨ (a = football ∧ b = football) := by
  constructor
  · rintro ⟨h1, h2⟩
    cases a <;> cases b
    · simp
    · have := h1 football; norm_num [u1] at this
    · have := h1 opera; norm_num [u1] at this
    · simp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨?_, ?_⟩ <;> intro x <;> cases x <;> norm_num [u1, u2]
    · refine ⟨?_, ?_⟩ <;> intro x <;> cases x <;> norm_num [u1, u2]

/-! ## The public fair coin -/

/-- Recommendation after the public signal: heads (`true`) → both Opera,
tails (`false`) → both Football. -/
def coinRec : Bool → Act × Act
  | true => (opera, opera)
  | false => (football, football)

/-- Expected value of `f` under a fair coin. -/
def coinExp (f : Bool → ℝ) : ℝ := (1 / 2) * f true + (1 / 2) * f false

theorem coin_expected_payoff1 :
    coinExp (fun s => u1 (coinRec s).1 (coinRec s).2) = 3 / 2 := by
  norm_num [coinExp, coinRec, u1]

theorem coin_expected_payoff2 :
    coinExp (fun s => u2 (coinRec s).1 (coinRec s).2) = 3 / 2 := by
  norm_num [coinExp, coinRec, u2]

theorem coin_follow_best_response1 (s : Bool) (a' : Act) :
    u1 a' (coinRec s).2 ≤ u1 (coinRec s).1 (coinRec s).2 := by
  cases s <;> cases a' <;> norm_num [coinRec, u1]

theorem coin_follow_best_response2 (s : Bool) (b' : Act) :
    u2 (coinRec s).1 b' ≤ u2 (coinRec s).1 (coinRec s).2 := by
  cases s <;> cases b' <;> norm_num [coinRec, u2]

theorem coin_follow_best_strategy1 (φ : Bool → Act) :
    coinExp (fun s => u1 (φ s) (coinRec s).2) ≤
      coinExp (fun s => u1 (coinRec s).1 (coinRec s).2) := by
  unfold coinExp
  have h1 := coin_follow_best_response1 true (φ true)
  have h2 := coin_follow_best_response1 false (φ false)
  linarith

theorem coin_follow_best_strategy2 (ψ : Bool → Act) :
    coinExp (fun s => u2 (coinRec s).1 (ψ s)) ≤
      coinExp (fun s => u2 (coinRec s).1 (coinRec s).2) := by
  unfold coinExp
  have h1 := coin_follow_best_response2 true (ψ true)
  have h2 := coin_follow_best_response2 false (ψ false)
  linarith

/-- Standard correlated equilibrium for a distribution `μ` on action profiles. -/
def IsCorrelatedEq (μ : Act × Act → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ (∑ x, μ x = 1) ∧
  (∀ a a', ∑ b, μ (a, b) * (u1 a' b - u1 a b) ≤ 0) ∧
  (∀ b b', ∑ a, μ (a, b) * (u2 a b' - u2 a b) ≤ 0)

/-- Distribution on profiles induced by the public fair coin. -/
def coinDist : Act × Act → ℝ
  | (opera, opera) => 1 / 2
  | (football, football) => 1 / 2
  | _ => 0

theorem coinDist_eq (x : Act × Act) :
    coinDist x = coinExp (fun s => if coinRec s = x then 1 else 0) := by
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;> norm_num [coinDist, coinExp, coinRec]

theorem sum_action (f : Act → ℝ) : ∑ a, f a = f opera + f football := by
  have : (Finset.univ : Finset Act) = {opera, football} := by
    ext x; cases x <;> simp
  rw [this, Finset.sum_pair (by decide)]

theorem coin_isCorrelatedEq : IsCorrelatedEq coinDist := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨a, b⟩; cases a <;> cases b <;> norm_num [coinDist]
  · rw [Fintype.sum_prod_type]
    simp only [sum_action]
    norm_num [coinDist]
  · intro a a'
    rw [sum_action]
    cases a <;> cases a' <;> norm_num [coinDist, u1]
  · intro b b'
    rw [sum_action]
    cases b <;> cases b' <;> norm_num [coinDist, u2]

theorem coinDist_payoffs :
    (∑ x, coinDist x * u1 x.1 x.2) = 3 / 2 ∧ (∑ x, coinDist x * u2 x.1 x.2) = 3 / 2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [sum_action]
  norm_num [coinDist, u1, u2]

/-! ## No Nash equilibrium is fair and efficient -/

theorem no_pureNash_fair :
    ¬ ∃ a b, IsPureNash a b ∧ u1 a b = 3 / 2 ∧ u2 a b = 3 / 2 := by
  rintro ⟨a, b, hN, h1, -⟩
  rcases (pureNash_iff a b).1 hN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num [u1] at h1

/-- Expected payoff to player 1 when player 1 plays Opera with probability `p`
and player 2 independently plays Opera with probability `q`. -/
def U1 (p q : ℝ) : ℝ :=
  p * q * u1 opera opera + p * (1 - q) * u1 opera football +
    (1 - p) * q * u1 football opera + (1 - p) * (1 - q) * u1 football football

/-- Expected payoff to player 2 under the same independent mixed profile. -/
def U2 (p q : ℝ) : ℝ :=
  p * q * u2 opera opera + p * (1 - q) * u2 opera football +
    (1 - p) * q * u2 football opera + (1 - p) * (1 - q) * u2 football football

theorem U1_eq (p q : ℝ) : U1 p q = p * (3 * q - 1) + (1 - q) := by
  simp only [U1, u1]; ring

theorem U2_eq (p q : ℝ) : U2 p q = q * (3 * p - 2) + 2 * (1 - p) := by
  simp only [U2, u2]; ring

/-- Mixed Nash equilibrium in independent mixed strategies. -/
def IsMixedNash (p q : ℝ) : Prop :=
  p ∈ Set.Icc (0 : ℝ) 1 ∧ q ∈ Set.Icc (0 : ℝ) 1 ∧
  (∀ p' ∈ Set.Icc (0 : ℝ) 1, U1 p' q ≤ U1 p q) ∧
  (∀ q' ∈ Set.Icc (0 : ℝ) 1, U2 p q' ≤ U2 p q)

theorem mixedNash_iff (p q : ℝ) :
    IsMixedNash p q ↔
      (p = 1 ∧ q = 1) ∨ (p = 0 ∧ q = 0) ∨ (p = 2 / 3 ∧ q = 1 / 3) := by
  constructor
  · rintro ⟨⟨hp0, hp1⟩, ⟨hq0, hq1⟩, h1, h2⟩
    have a0 := h1 0 ⟨le_refl _, zero_le_one⟩
    have a1 := h1 1 ⟨zero_le_one, le_refl _⟩
    have b0 := h2 0 ⟨le_refl _, zero_le_one⟩
    have b1 := h2 1 ⟨zero_le_one, le_refl _⟩
    rw [U1_eq, U1_eq] at a0 a1
    rw [U2_eq, U2_eq] at b0 b1
    rcases lt_trichotomy (3 * q - 1) 0 with hq | hq | hq
    · have hp : p = 0 := by nlinarith
      subst hp
      have : q = 0 := by nlinarith
      exact Or.inr (Or.inl ⟨rfl, this⟩)
    · have hq' : q = 1 / 3 := by linarith
      subst hq'
      have : p = 2 / 3 := by nlinarith
      exact Or.inr (Or.inr ⟨this, rfl⟩)
    · have hp : p = 1 := by nlinarith
      subst hp
      have : q = 1 := by nlinarith
      exact Or.inl ⟨rfl, this⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals
      refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
      · rintro x ⟨hx0, hx1⟩; rw [U1_eq, U1_eq]; nlinarith
      · rintro x ⟨hx0, hx1⟩; rw [U2_eq, U2_eq]; nlinarith

theorem mixedNash_interior (p q : ℝ) (hp : 0 < p ∧ p < 1) :
    IsMixedNash p q ↔ (p = 2 / 3 ∧ q = 1 / 3) := by
  rw [mixedNash_iff]
  constructor
  · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩ | h)
    · exact absurd hp.2 (lt_irrefl _)
    · exact absurd hp.1 (lt_irrefl _)
    · exact h
  · exact fun h => Or.inr (Or.inr h)

theorem mixedNash_two_thirds : IsMixedNash (2 / 3) (1 / 3) :=
  (mixedNash_iff _ _).2 (Or.inr (Or.inr ⟨rfl, rfl⟩))

theorem mixed_eq_payoffs : U1 (2 / 3) (1 / 3) = 2 / 3 ∧ U2 (2 / 3) (1 / 3) = 2 / 3 := by
  rw [U1_eq, U2_eq]; constructor <;> norm_num

theorem no_mixedNash_fair :
    ¬ ∃ p q, IsMixedNash p q ∧ U1 p q = 3 / 2 ∧ U2 p q = 3 / 2 := by
  rintro ⟨p, q, hN, h1, -⟩
  rw [U1_eq] at h1
  rcases (mixedNash_iff p q).1 hN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num at h1

theorem no_independent_fair (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) : ¬ (U1 p q = 3 / 2 ∧ U2 p q = 3 / 2) := by
  rintro ⟨h1, h2⟩
  rw [U1_eq] at h1
  rw [U2_eq] at h2
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  have hsum : p * (1 - q) + (1 - p) * q = 0 := by nlinarith
  have e1 : 0 ≤ p * (1 - q) := mul_nonneg hp0 (by linarith)
  have e2 : 0 ≤ (1 - p) * q := mul_nonneg (by linarith) hq0
  have ha : p * (1 - q) = 0 := by linarith
  have hb : (1 - p) * q = 0 := by linarith
  rcases mul_eq_zero.1 ha with h | h
  · subst h
    have : q = 0 := by simpa using hb
    subst this; norm_num at h1
  · have hq' : q = 1 := by linarith
    subst hq'
    have : p = 1 := by linarith [show (1 - p) * 1 = 1 - p by ring]
    subst this; norm_num at h1

end

end FocalPointPublicSignalB
