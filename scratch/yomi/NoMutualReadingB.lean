import Mathlib

/-!
# NoMutualReadingB

Matching pennies: the Matcher (row player, action `a : Bool`) wins iff `a = b`; the
Mismatcher (column player, action `b : Bool`) wins iff `a ≠ b`. Payoffs are `1` for a win
and `0` for a loss.

PROVED
* `no_mutually_read_concrete`: there are no `a b : Bool` with `a = b` and `b = !a`.
* `matcher_bestResponse_iff`, `mismatcher_bestResponse_iff`: in the payoff game `mp`,
  "`a` is a best response to `b`" is exactly `a = b`, and "`b` is a best response to `a`"
  is exactly `b = !a`; hence `no_mutually_read` (no pair is mutually read in `mp`).
* `mutuallyRead_iff_isPureNash`: for any two-player game (on any action sets, in particular
  finite ones), a pair in which each action is a best response to the other is exactly a pure
  Nash equilibrium (no player has a strictly profitable unilateral deviation).
  `no_pure_nash`: matching pennies has no pure Nash equilibrium.
* `winProb_fair_coin`: if the Matcher's rule is any function `f : S → Bool` of a private
  signal `s` with distribution `p` on a finite type `S`, and the Mismatcher plays a fair coin
  independent of `s` (joint law `p s * 1/2`), the Matcher wins with probability exactly `1/2`.
  `winProb_deterministic` is the case `S = Unit`.
  `winProb_conditionally_fair` is the stronger form: any joint law `μ` on `S × Bool` with total
  mass `1` under which the Mismatcher's action is fair conditional on each signal value
  (`μ (s, true) = μ (s, false)`) gives win probability exactly `1/2`.
* `exists_rule_beating_unfair_coin`: conversely, if the Mismatcher's independent coin has
  `P(true) = q ≠ 1/2`, some constant Matcher rule wins with probability strictly above `1/2`.

INTERPRETED (not formal content)
* Calling a best response "reading" the opponent, the first group says at most one player can
  be reading the other at any moment in matching pennies: both reading at once would be a pure
  Nash equilibrium, and there is none.
* The second group says a fair coin, independent of what the opponent can see, makes a player
  unreadable: no rule, deterministic or randomized, does better or worse than `1/2`; and only
  the fair coin has this property.
-/

namespace NoMutualReadingB

open Finset

/-- A two-player game in normal form with real payoffs `u₁` (row) and `u₂` (column). -/
structure Game (A B : Type*) where
  u₁ : A → B → ℝ
  u₂ : A → B → ℝ

variable {A B : Type*}

/-- `a` is a best response of player 1 to `b`. -/
def BestResponse₁ (G : Game A B) (a : A) (b : B) : Prop :=
  ∀ a' : A, G.u₁ a' b ≤ G.u₁ a b

/-- `b` is a best response of player 2 to `a`. -/
def BestResponse₂ (G : Game A B) (a : A) (b : B) : Prop :=
  ∀ b' : B, G.u₂ a b' ≤ G.u₂ a b

/-- Each action is a best response to the other. -/
def MutuallyRead (G : Game A B) (a : A) (b : B) : Prop :=
  BestResponse₁ G a b ∧ BestResponse₂ G a b

/-- Pure Nash equilibrium: no player has a strictly profitable unilateral deviation. -/
def IsPureNash (G : Game A B) (a : A) (b : B) : Prop :=
  (¬ ∃ a' : A, G.u₁ a b < G.u₁ a' b) ∧ (¬ ∃ b' : B, G.u₂ a b < G.u₂ a b')

theorem mutuallyRead_iff_isPureNash (G : Game A B) (a : A) (b : B) :
    MutuallyRead G a b ↔ IsPureNash G a b := by
  simp only [MutuallyRead, BestResponse₁, BestResponse₂, IsPureNash, not_exists, not_lt]

/-- The finite-action-set form of `mutuallyRead_iff_isPureNash`. -/
theorem mutuallyRead_iff_isPureNash_fintype [Fintype A] [Fintype B]
    (G : Game A B) (a : A) (b : B) :
    MutuallyRead G a b ↔ IsPureNash G a b :=
  mutuallyRead_iff_isPureNash G a b

/-- Matching pennies: the Matcher scores `1` iff the Bools agree, the Mismatcher iff they differ. -/
def mp : Game Bool Bool where
  u₁ a b := if a = b then 1 else 0
  u₂ a b := if a = b then 0 else 1

/-- The concrete statement: no `a, b` satisfy both `a = b` and `b = !a`. -/
theorem no_mutually_read_concrete : ¬ ∃ a b : Bool, a = b ∧ b = !a := by
  decide

theorem matcher_bestResponse_iff (a b : Bool) : BestResponse₁ mp a b ↔ a = b := by
  cases a <;> cases b <;> norm_num [BestResponse₁, mp, Bool.forall_bool]

theorem mismatcher_bestResponse_iff (a b : Bool) : BestResponse₂ mp a b ↔ b = !a := by
  cases a <;> cases b <;> norm_num [BestResponse₂, mp, Bool.forall_bool]

theorem mutuallyRead_mp_iff (a b : Bool) : MutuallyRead mp a b ↔ (a = b ∧ b = !a) := by
  rw [MutuallyRead, matcher_bestResponse_iff, mismatcher_bestResponse_iff]

theorem no_mutually_read (a b : Bool) : ¬ MutuallyRead mp a b := by
  rw [mutuallyRead_mp_iff]
  exact fun h => no_mutually_read_concrete ⟨a, b, h⟩

theorem no_pure_nash (a b : Bool) : ¬ IsPureNash mp a b := by
  rw [← mutuallyRead_iff_isPureNash]
  exact no_mutually_read a b

/-- Probability that the Matcher wins when the signal/Mismatcher-action pair has joint law `μ`
on `S × Bool` and the Matcher plays `f s` on signal `s`. -/
noncomputable def winProb {S : Type*} [Fintype S] (μ : S × Bool → ℝ) (f : S → Bool) : ℝ :=
  ∑ x : S × Bool, μ x * mp.u₁ (f x.1) x.2

/-- Conditional fairness suffices: if `μ (s, true) = μ (s, false)` for every signal `s` and `μ`
has total mass `1`, every Matcher rule wins with probability exactly `1/2`. -/
theorem winProb_conditionally_fair {S : Type*} [Fintype S] (μ : S × Bool → ℝ)
    (hμ : ∑ x : S × Bool, μ x = 1) (hfair : ∀ s : S, μ (s, true) = μ (s, false))
    (f : S → Bool) : winProb μ f = 1 / 2 := by
  have hinner : ∀ s : S, ∑ b : Bool, μ (s, b) * mp.u₁ (f s) b = μ (s, true) := by
    intro s
    rw [Fintype.sum_bool]
    cases f s <;> simp [mp, hfair s]
  have htot : ∑ s : S, 2 * μ (s, true) = 1 := by
    rw [← hμ, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Fintype.sum_bool, ← hfair s]
    ring
  have : ∑ s : S, μ (s, true) = 1 / 2 := by
    rw [← Finset.mul_sum] at htot
    linarith
  unfold winProb
  rw [Fintype.sum_prod_type]
  simp_rw [hinner]
  exact this

/-- A fair coin independent of the Matcher's private signal: every Matcher rule, i.e. every
function `f` of a private signal with distribution `p`, wins with probability exactly `1/2`. -/
theorem winProb_fair_coin {S : Type*} [Fintype S] (p : S → ℝ) (hp : ∑ s : S, p s = 1)
    (f : S → Bool) : winProb (fun x : S × Bool => p x.1 * (1 / 2)) f = 1 / 2 := by
  refine winProb_conditionally_fair _ ?_ (fun _ => rfl) f
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  calc ∑ s : S, (p s * (1 / 2) + p s * (1 / 2)) = ∑ s : S, p s :=
        Finset.sum_congr rfl fun s _ => by ring
    _ = 1 := hp

/-- Deterministic Matcher (`S = Unit`) against a fair coin. -/
theorem winProb_deterministic (a : Bool) :
    winProb (fun _ : Unit × Bool => (1 / 2 : ℝ)) (fun _ => a) = 1 / 2 := by
  have h := winProb_fair_coin (S := Unit) (fun _ => 1) (by simp) (fun _ => a)
  simpa using h

/-- Converse: against an independent coin with `P(true) = q ≠ 1/2`, some constant Matcher rule
wins with probability strictly greater than `1/2`. -/
theorem exists_rule_beating_unfair_coin (q : ℝ) (hq : q ≠ 1 / 2) :
    ∃ a : Bool,
      1 / 2 < winProb (fun x : Unit × Bool => if x.2 then q else 1 - q) (fun _ => a) := by
  have key : ∀ a : Bool, winProb (fun x : Unit × Bool => if x.2 then q else 1 - q)
      (fun _ => a) = if a then q else 1 - q := by
    intro a
    unfold winProb
    rw [Fintype.sum_prod_type]
    cases a <;> simp [mp]
  rcases lt_or_gt_of_ne hq with h | h
  · exact ⟨false, by rw [key]; simp; linarith⟩
  · exact ⟨true, by rw [key]; simpa using h⟩

end NoMutualReadingB
