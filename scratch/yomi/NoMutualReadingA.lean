import Mathlib

/-!
# NoMutualReadingA

Matching pennies: the Matcher (row, action `a : Bool`) is paid `1` when `a = b`, the
Mismatcher (column, action `b : Bool`) is paid `1` when `a ≠ b`.

PROVED
* `no_mutually_read`: no pair `(a, b)` satisfies `a = b ∧ b = !a`.
* `mutualBR_iff_pureNash`: for any two-player game with finite action sets, a pair in
  which each action is a best response to the other is exactly a pure Nash equilibrium
  (no player has a strictly profitable unilateral deviation).
* `mp_isBR₁_iff`, `mp_isBR₂_iff`: in matching pennies the Matcher's best responses to `b`
  are exactly `a = b`, and the Mismatcher's best responses to `a` are exactly `b = !a`.
* `mp_mutualBR_iff_mutuallyRead`: hence "each best-responds to the other" in matching
  pennies is exactly the stated mutual-reading condition.
* `mp_no_pure_nash`: matching pennies has no pure Nash equilibrium.
* `matcher_win_half`: if the Mismatcher's action is a fair coin, independent of a signal
  `s : S` with arbitrary weights `p` summing to `1` (everything the Matcher can see,
  including its own private randomness), then every Matcher rule `f : S → Bool` wins with
  probability exactly `1/2`. Nonnegativity of `p` is not needed.
* `matcher_win_half_randomized`: the same with the Matcher's input split into an observed
  signal and private randomness `ω : Ω`, with an arbitrary (possibly correlated) joint law
  on `S × Ω`.
* `mismatcher_win_half`: under the same hypotheses the Mismatcher also wins with
  probability exactly `1/2`.

INTERPRETED (not formal content)
* At most one player can be reading the other at any moment: if both actions were best
  responses to each other the pair would be a pure Nash equilibrium, and there is none.
* A fair coin makes you unreadable: against an independent fair coin no rule, however
  informed by what the Matcher can see, does better or worse than `1/2`.
-/

namespace NoMutualReadingA

open Finset

/-- The Matcher's payoff in matching pennies. -/
noncomputable def matcherPayoff (a b : Bool) : ℝ := if a = b then 1 else 0

/-- The Mismatcher's payoff in matching pennies. -/
noncomputable def mismatcherPayoff (a b : Bool) : ℝ := if a = b then 0 else 1

/-- The stated mutual-reading condition: the Matcher best-responds to `b` (`a = b`) and the
Mismatcher best-responds to `a` (`b = !a`). -/
def MutuallyRead (a b : Bool) : Prop := a = b ∧ b = !a

/-- (1) No pair of pure actions is mutually read. -/
theorem no_mutually_read (a b : Bool) : ¬ MutuallyRead a b := by
  rintro ⟨h1, h2⟩
  subst h1
  cases a <;> simp at h2

/-- A two-player game in normal form with real payoffs. -/
structure Game (α β : Type*) where
  u₁ : α → β → ℝ
  u₂ : α → β → ℝ

variable {α β : Type*}

/-- `a` is a best response of player 1 to `b`. -/
def IsBR₁ (G : Game α β) (a : α) (b : β) : Prop := ∀ a', G.u₁ a' b ≤ G.u₁ a b

/-- `b` is a best response of player 2 to `a`. -/
def IsBR₂ (G : Game α β) (a : α) (b : β) : Prop := ∀ b', G.u₂ a b' ≤ G.u₂ a b

/-- Each action is a best response to the other. -/
def MutualBR (G : Game α β) (a : α) (b : β) : Prop := IsBR₁ G a b ∧ IsBR₂ G a b

/-- Pure Nash equilibrium: no player has a strictly profitable unilateral deviation. -/
def IsPureNash (G : Game α β) (a : α) (b : β) : Prop :=
  (¬ ∃ a', G.u₁ a b < G.u₁ a' b) ∧ (¬ ∃ b', G.u₂ a b < G.u₂ a b')

/-- (2a) In any two-player game on finite action sets, mutual best response is exactly
pure Nash equilibrium. -/
theorem mutualBR_iff_pureNash [Fintype α] [Fintype β] (G : Game α β) (a : α) (b : β) :
    MutualBR G a b ↔ IsPureNash G a b := by
  simp only [MutualBR, IsBR₁, IsBR₂, IsPureNash, not_exists, not_lt]

/-- Matching pennies as a game. -/
noncomputable def matchingPennies : Game Bool Bool := ⟨matcherPayoff, mismatcherPayoff⟩

theorem mp_isBR₁_iff (a b : Bool) : IsBR₁ matchingPennies a b ↔ a = b := by
  cases a <;> cases b <;>
    norm_num [IsBR₁, matchingPennies, matcherPayoff, Bool.forall_bool]

theorem mp_isBR₂_iff (a b : Bool) : IsBR₂ matchingPennies a b ↔ b = !a := by
  cases a <;> cases b <;>
    norm_num [IsBR₂, matchingPennies, mismatcherPayoff, Bool.forall_bool]

/-- In matching pennies, mutual best response is exactly the stated mutual-reading
condition. -/
theorem mp_mutualBR_iff_mutuallyRead (a b : Bool) :
    MutualBR matchingPennies a b ↔ MutuallyRead a b := by
  rw [MutualBR, mp_isBR₁_iff, mp_isBR₂_iff, MutuallyRead]

/-- (2b) Matching pennies has no pure Nash equilibrium. -/
theorem mp_no_pure_nash (a b : Bool) : ¬ IsPureNash matchingPennies a b := by
  rw [← mutualBR_iff_pureNash, mp_mutualBR_iff_mutuallyRead]
  exact no_mutually_read a b

theorem sum_matcherPayoff (x : Bool) : ∑ c : Bool, matcherPayoff x c = 1 := by
  cases x <;> simp [matcherPayoff]

theorem sum_mismatcherPayoff (x : Bool) : ∑ c : Bool, mismatcherPayoff x c = 1 := by
  cases x <;> simp [mismatcherPayoff]

/-- (3) The Matcher sees `s : S` with law `p`; the Mismatcher plays an independent fair coin
`c`. Every rule `f : S → Bool` wins with probability exactly `1/2`. -/
theorem matcher_win_half {S : Type*} [Fintype S] (p : S → ℝ) (hp : ∑ s, p s = 1)
    (f : S → Bool) :
    ∑ s, ∑ c : Bool, p s * (1 / 2) * matcherPayoff (f s) c = 1 / 2 := by
  simp_rw [← Finset.mul_sum, sum_matcherPayoff, mul_one, ← Finset.sum_mul, hp, one_mul]

/-- (3, randomized form) The Matcher sees a signal `s : S` and private randomness `ω : Ω`
with an arbitrary joint law `π` on `S × Ω`; the Mismatcher plays a fair coin independent of
`(s, ω)`. Every randomized rule `f : S → Ω → Bool` wins with probability exactly `1/2`. -/
theorem matcher_win_half_randomized {S Ω : Type*} [Fintype S] [Fintype Ω]
    (π : S → Ω → ℝ) (hπ : ∑ s, ∑ ω, π s ω = 1) (f : S → Ω → Bool) :
    ∑ s, ∑ ω, ∑ c : Bool, π s ω * (1 / 2) * matcherPayoff (f s ω) c = 1 / 2 := by
  simp_rw [← Finset.mul_sum, sum_matcherPayoff, mul_one, ← Finset.sum_mul, hπ, one_mul]

/-- Under the same hypotheses as `matcher_win_half`, the Mismatcher wins with probability
exactly `1/2`. -/
theorem mismatcher_win_half {S : Type*} [Fintype S] (p : S → ℝ) (hp : ∑ s, p s = 1)
    (f : S → Bool) :
    ∑ s, ∑ c : Bool, p s * (1 / 2) * mismatcherPayoff (f s) c = 1 / 2 := by
  simp_rw [← Finset.mul_sum, sum_mismatcherPayoff, mul_one, ← Finset.sum_mul, hp, one_mul]

end NoMutualReadingA
