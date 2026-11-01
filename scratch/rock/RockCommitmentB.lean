import Mathlib

/-!
# Commitment in Chicken, Rock-paper-scissors, and the yomi recursion

PROVED

(1) Chicken, actions `swerve` / `straight`, payoffs (row, column):
  (Sw,Sw) = (0,0), (Sw,St) = (-1,1), (St,Sw) = (1,-1), (St,St) = (-10,-10).
  * `commit_straight_br_iff`: against a row committed to `straight`, the column's unique
    best response is `swerve`; `commit_straight_payoff`: row then gets `1`;
    `row_le_one`: `1` is the highest payoff row can receive in any cell.
  * `pure_nash_iff`: the pure Nash equilibria are exactly (Straight,Swerve) and (Swerve,Straight).
  * Mixed strategies are parametrised by the probability `p ∈ [0,1]` of `straight`.
    `mixed_nash_iff`: the mixed Nash equilibria are exactly
    `(1,0)`, `(0,1)` and `(1/10,1/10)`; `symmetric_mixed_nash_iff`: the unique symmetric one
    is `p = q = 1/10`, and `symmetric_mixed_payoff`: its expected row payoff is `-1/10`.
  * CORRECTION TO THE TARGET: the target asserted the symmetric mixed equilibrium is
    "Straight with probability 1/11, expected payoff -1/11". With the stated payoffs this is
    false: `not_mixed_nash_one_eleventh` proves `(1/11,1/11)` is not an equilibrium, and
    `rowExp_one_eleventh` computes the payoff there as `-10/121`, not `-1/11`.
    The indifference condition is `-q = 1 - 11 q`, i.e. `q = 1/10`.
  * `commitment_beats_mixed`: committing first to `straight` gives row `1 > -1/10`, the
    symmetric mixed equilibrium payoff (`commitment_beats_stated_mixed` also records `1 > -1/11`).

(2) Rock-paper-scissors, payoff `1` win, `-1` loss, `0` tie.
  * `rps_br_rock_iff`: the unique best response to `rock` is `paper`;
    `committed_rock_every_round`: against any opponent who best-responds in every round, the
    committed-Rock player gets `-1` in every round and `-n` over `n` rounds;
    `rps_min`: `-1` is the minimum possible payoff.
  * `uniform_guarantees_zero`: the uniform mixture earns expected payoff exactly `0`
    against every (pure or mixed, indeed any weighting) opponent strategy; in particular
    `uniform_ge_zero` it guarantees at least `0` against every mixed strategy.

(3) Yomi recursion: `matcher 0 = mismatcher 0 = true`, `matcher (k+1) = mismatcher k`,
  `mismatcher (k+1) = !matcher k`.
  * `matcher_four`, `mismatcher_four`: `matcher 4 = matcher 0`, `mismatcher 4 = mismatcher 0`.
  * `matcher_period`, `mismatcher_period`: period 4 at every level `k`.

INTERPRETED (docstring only, not formalised)
  Commitment wins coordination-type games (Chicken: the committed player gets its best
  possible payoff, above the mixed equilibrium) and loses outguessing games
  (Rock-paper-scissors: a committed player is held to its worst payoff, while the
  uncommitted uniform mixture secures the value 0). The yomi tower is periodic with period 4,
  so the top of the tower is level 0 again.
-/

namespace RockCommitmentB

/-! ## (1) Chicken -/

inductive Act
  | swerve
  | straight
  deriving DecidableEq, Repr

open Act

instance : Fintype Act := ⟨{swerve, straight}, by intro x; cases x <;> simp⟩

/-- Row player's payoff. -/
def rowPay : Act → Act → ℚ
  | swerve, swerve => 0
  | swerve, straight => -1
  | straight, swerve => 1
  | straight, straight => -10

/-- Column player's payoff, with the row action first. -/
def colPay : Act → Act → ℚ
  | swerve, swerve => 0
  | swerve, straight => 1
  | straight, swerve => -1
  | straight, straight => -10

/-- `c` is a best response of the column player to row action `r`. -/
def ColBR (r c : Act) : Prop := ∀ c', colPay r c' ≤ colPay r c

/-- `r` is a best response of the row player to column action `c`. -/
def RowBR (c r : Act) : Prop := ∀ r', rowPay r' c ≤ rowPay r c

/-- Pure Nash equilibrium. -/
def PureNash (r c : Act) : Prop := RowBR c r ∧ ColBR r c

instance (r c : Act) : Decidable (ColBR r c) := by unfold ColBR; infer_instance
instance (c r : Act) : Decidable (RowBR c r) := by unfold RowBR; infer_instance
instance (r c : Act) : Decidable (PureNash r c) := by unfold PureNash; infer_instance

theorem commit_straight_br_iff (c : Act) : ColBR straight c ↔ c = swerve := by
  cases c <;> decide

theorem commit_straight_payoff (c : Act) (h : ColBR straight c) : rowPay straight c = 1 := by
  rw [(commit_straight_br_iff c).1 h]; rfl

theorem row_le_one (r c : Act) : rowPay r c ≤ 1 := by
  cases r <;> cases c <;> norm_num [rowPay]

theorem pure_nash_iff (r c : Act) :
    PureNash r c ↔ (r, c) = (straight, swerve) ∨ (r, c) = (swerve, straight) := by
  cases r <;> cases c <;> decide

/-- Row's expected payoff when row plays `straight` with probability `p` and column plays
`straight` with probability `q`. -/
def rowExp (p q : ℚ) : ℚ :=
  (1 - p) * (1 - q) * rowPay swerve swerve + (1 - p) * q * rowPay swerve straight
    + p * (1 - q) * rowPay straight swerve + p * q * rowPay straight straight

/-- Column's expected payoff for the same mixed profile. -/
def colExp (p q : ℚ) : ℚ :=
  (1 - p) * (1 - q) * colPay swerve swerve + (1 - p) * q * colPay swerve straight
    + p * (1 - q) * colPay straight swerve + p * q * colPay straight straight

/-- Mixed Nash equilibrium (probabilities of `straight`). -/
def MixedNash (p q : ℚ) : Prop :=
  (0 ≤ p ∧ p ≤ 1) ∧ (0 ≤ q ∧ q ≤ 1) ∧
  (∀ p', 0 ≤ p' → p' ≤ 1 → rowExp p' q ≤ rowExp p q) ∧
  (∀ q', 0 ≤ q' → q' ≤ 1 → colExp p q' ≤ colExp p q)

theorem rowExp_eq (p q : ℚ) : rowExp p q = -q + p * (1 - 10 * q) := by
  simp only [rowExp, rowPay]; ring

theorem colExp_eq (p q : ℚ) : colExp p q = -p + q * (1 - 10 * p) := by
  simp only [colExp, colPay]; ring

theorem mixed_nash_iff (p q : ℚ) :
    MixedNash p q ↔ (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) ∨ (p = 1 / 10 ∧ q = 1 / 10) := by
  constructor
  · rintro ⟨⟨hp0, hp1⟩, ⟨hq0, hq1⟩, hr, hc⟩
    simp only [rowExp_eq, colExp_eq] at hr hc
    have r0 := hr 0 le_rfl zero_le_one
    have r1 := hr 1 zero_le_one le_rfl
    have c0 := hc 0 le_rfl zero_le_one
    have c1 := hc 1 zero_le_one le_rfl
    rcases lt_trichotomy q (1 / 10) with hq | hq | hq
    · have hp : p = 1 := by nlinarith
      subst hp
      left; constructor
      · rfl
      · nlinarith
    · subst hq
      rcases lt_trichotomy p (1 / 10) with hp | hp | hp
      · exfalso; nlinarith
      · right; right; exact ⟨hp, rfl⟩
      · exfalso; nlinarith
    · have hp : p = 0 := by nlinarith
      subst hp
      right; left; constructor
      · rfl
      · nlinarith
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ?_, ?_⟩ <;>
      intro x hx0 hx1 <;> simp only [rowExp_eq, colExp_eq] <;> nlinarith

theorem symmetric_mixed_nash_iff (p : ℚ) : MixedNash p p ↔ p = 1 / 10 := by
  rw [mixed_nash_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩)
    · rw [h1] at h2; norm_num at h2
    · rw [h1] at h2; norm_num at h2
    · exact h1
  · rintro rfl; right; right; exact ⟨rfl, rfl⟩

theorem symmetric_mixed_payoff : rowExp (1 / 10) (1 / 10) = -1 / 10 := by
  rw [rowExp_eq]; norm_num

theorem not_mixed_nash_one_eleventh : ¬ MixedNash (1 / 11) (1 / 11) := by
  rw [symmetric_mixed_nash_iff]; norm_num

theorem rowExp_one_eleventh : rowExp (1 / 11) (1 / 11) = -10 / 121 := by
  rw [rowExp_eq]; norm_num

theorem rowExp_one_eleventh_ne : rowExp (1 / 11) (1 / 11) ≠ -1 / 11 := by
  rw [rowExp_one_eleventh]; norm_num

/-- Committing to `straight` (column best-responds) beats the symmetric mixed equilibrium. -/
theorem commitment_beats_mixed (c : Act) (h : ColBR straight c) (p : ℚ) (hp : MixedNash p p) :
    rowExp p p < rowPay straight c := by
  rw [commit_straight_payoff c h, (symmetric_mixed_nash_iff p).1 hp, symmetric_mixed_payoff]
  norm_num

theorem commitment_beats_stated_mixed (c : Act) (h : ColBR straight c) :
    (-1 / 11 : ℚ) < rowPay straight c := by
  rw [commit_straight_payoff c h]; norm_num

/-! ## (2) Rock-paper-scissors -/

inductive RPS
  | rock
  | paper
  | scissors
  deriving DecidableEq, Repr

open RPS

instance : Fintype RPS := ⟨{rock, paper, scissors}, by intro x; cases x <;> simp⟩

theorem rps_univ : (Finset.univ : Finset RPS) = {rock, paper, scissors} := rfl

/-- Payoff to the player choosing `a` against `b`. -/
def pay : RPS → RPS → ℚ
  | rock, rock => 0
  | rock, paper => -1
  | rock, scissors => 1
  | paper, rock => 1
  | paper, paper => 0
  | paper, scissors => -1
  | scissors, rock => -1
  | scissors, paper => 1
  | scissors, scissors => 0

/-- `b` is a best response to `a` (the responder's payoff is `pay b a`). -/
def RpsBR (a b : RPS) : Prop := ∀ b', pay b' a ≤ pay b a

instance (a b : RPS) : Decidable (RpsBR a b) := by unfold RpsBR; infer_instance

theorem rps_br_rock_iff (b : RPS) : RpsBR rock b ↔ b = paper := by
  cases b <;> decide

theorem rps_min (a b : RPS) : -1 ≤ pay a b := by
  cases a <;> cases b <;> norm_num [pay]

theorem committed_rock_every_round (opp : ℕ → RPS) (h : ∀ n, RpsBR rock (opp n)) :
    (∀ n, pay rock (opp n) = -1) ∧
    ∀ n, ∑ i ∈ Finset.range n, pay rock (opp i) = -(n : ℚ) := by
  have h1 : ∀ n, pay rock (opp n) = -1 := fun n => by
    rw [(rps_br_rock_iff _).1 (h n)]; rfl
  refine ⟨h1, fun n => ?_⟩
  simp [h1]

/-- Expected payoff of mixture `x` against mixture `y`. -/
def mixPay (x y : RPS → ℚ) : ℚ := ∑ a, ∑ b, x a * y b * pay a b

theorem uniform_guarantees_zero (y : RPS → ℚ) : mixPay (fun _ => 1 / 3) y = 0 := by
  simp [mixPay, rps_univ, pay]
  ring

theorem uniform_ge_zero (y : RPS → ℚ) (_hy0 : ∀ b, 0 ≤ y b) (_hy1 : ∑ b, y b = 1) :
    0 ≤ mixPay (fun _ => 1 / 3) y := by
  rw [uniform_guarantees_zero]

theorem uniform_vs_pure (b : RPS) : ∑ a, (1 / 3 : ℚ) * pay a b = 0 := by
  cases b <;> simp [rps_univ, pay]

/-! ## (3) Yomi recursion -/

mutual
def matcher : ℕ → Bool
  | 0 => true
  | k + 1 => mismatcher k
def mismatcher : ℕ → Bool
  | 0 => true
  | k + 1 => !matcher k
end

theorem matcher_four : matcher 4 = matcher 0 := by decide

theorem mismatcher_four : mismatcher 4 = mismatcher 0 := by decide

theorem matcher_period (k : ℕ) : matcher (k + 4) = matcher k := by
  simp [matcher, mismatcher]

theorem mismatcher_period (k : ℕ) : mismatcher (k + 4) = mismatcher k := by
  simp [matcher, mismatcher]

end RockCommitmentB
