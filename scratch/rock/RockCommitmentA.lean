import Mathlib

/-!
# Commitment in Chicken and in rock-paper-scissors; the yomi tower

PROVED

(1) Chicken, actions `Swerve`, `Straight`, payoffs (row, column)
    (Sw,Sw) = (0,0), (Sw,St) = (-1,1), (St,Sw) = (1,-1), (St,St) = (-10,-10).
  * `colBR_straight_iff` : the column best responses to `Straight` are exactly `Swerve`.
  * `commit_straight` : if row commits to `Straight` and column best-responds, column
    swerves and row gets `1`.
  * `rowPay_le_one` : `1` is the highest row payoff in the matrix.
  * `pureNash_iff` : the pure Nash equilibria are exactly (Straight,Swerve) and
    (Swerve,Straight).
  * `rowU_eq` : with `p`, `q` the probabilities of `Straight`, the row expected payoff is
    `p - q - 10 p q`.
  * `symMixedNash_iff` : for `p ∈ [0,1]`, `(p,p)` is a mixed Nash equilibrium iff
    `p = 1/10`.
  * `symMixedNash_payoff` : its payoff to each player is `-1/10`.
  * `commit_beats_mixed` : `1 > -1/10`, i.e. committing first to `Straight` gives row strictly
    more than the symmetric mixed equilibrium payoff.

  CORRECTION. The target's values "probability 1/11, payoff -1/11" are false. Indifference
  of row against `q` reads `-q = 1 - 11 q`, so `q = 1/10`, and the payoff is
  `-10 (1/10)^2 = -1/10`. Proved negations:
  * `not_symMixedNash_one_eleventh` : `(1/11, 1/11)` is not a mixed Nash equilibrium.
  * `rowU_one_eleventh` : the payoff at `(1/11,1/11)` is `-10/121`, not `-1/11`.
  * `symMixedNash_payoff_ne` : the equilibrium payoff is not `-1/11`.
  The strict comparison with commitment survives (`1 > -1/10`, and also `1 > -1/11`).

(2) Rock-paper-scissors, win `1`, loss `-1`, tie `0` (zero-sum).
  * `rpsBR_rock_iff` : the best responses to `Rock` are exactly `Paper`.
  * `rock_every_round` : against any sequence of best responses to `Rock`, the committed
    `Rock` player gets `-1` in every round.
  * `rpsPay_ge_neg_one` : `-1` is the minimum payoff.
  * `uniform_guarantees_zero` : the uniform mixture has expected payoff exactly `0` against
    every opponent mixture `q : RPS → ℚ` (no normalisation of `q` is needed).

(3) Yomi recursion: `matcher 0 = mismatcher 0 = true`, `matcher (k+1) = mismatcher k`,
    `mismatcher (k+1) = !matcher k`.
  * `matcher_four`, `mismatcher_four` : level 4 equals level 0.
  * `matcher_add_four`, `mismatcher_add_four` : period 4 at every level.

INTERPRETED (not formal content)
  Commitment wins coordination-type games such as Chicken, where a visible fixed action
  forces the other side to accommodate it, and loses outguessing games such as
  rock-paper-scissors, where a fixed action is exactly what a best responder exploits.
  The yomi tower is periodic with period 4: the top of the tower is level 0 again.
-/

namespace RockCommitmentA

/-! ## (1) Chicken -/

inductive Act
  | swerve
  | straight
  deriving DecidableEq, Repr

open Act

theorem Act.forall_iff (P : Act → Prop) : (∀ a, P a) ↔ P swerve ∧ P straight :=
  ⟨fun h => ⟨h _, h _⟩, fun h a => by cases a; exacts [h.1, h.2]⟩

/-- Row payoff. -/
def rowPay : Act → Act → ℚ
  | swerve, swerve => 0
  | swerve, straight => -1
  | straight, swerve => 1
  | straight, straight => -10

/-- Column payoff. -/
def colPay : Act → Act → ℚ
  | swerve, swerve => 0
  | swerve, straight => 1
  | straight, swerve => -1
  | straight, straight => -10

/-- `b` is a column best response to the row action `a`. -/
def ColBR (a b : Act) : Prop := ∀ b', colPay a b' ≤ colPay a b

/-- `a` is a row best response to the column action `b`. -/
def RowBR (b a : Act) : Prop := ∀ a', rowPay a' b ≤ rowPay a b

/-- Pure Nash equilibrium. -/
def PureNash (a b : Act) : Prop := RowBR b a ∧ ColBR a b

theorem colBR_straight_iff (b : Act) : ColBR straight b ↔ b = swerve := by
  unfold ColBR
  constructor
  · intro h
    cases b
    · rfl
    · have := h swerve; norm_num [colPay] at this
  · rintro rfl b'
    cases b' <;> simp [colPay]

theorem commit_straight (b : Act) (h : ColBR straight b) :
    b = swerve ∧ rowPay straight b = 1 := by
  have hb := (colBR_straight_iff b).1 h
  subst hb
  exact ⟨rfl, rfl⟩

theorem rowPay_le_one (a b : Act) : rowPay a b ≤ 1 := by
  cases a <;> cases b <;> norm_num [rowPay]

theorem pureNash_iff (a b : Act) :
    PureNash a b ↔ (a = straight ∧ b = swerve) ∨ (a = swerve ∧ b = straight) := by
  unfold PureNash RowBR ColBR
  rw [Act.forall_iff, Act.forall_iff]
  cases a <;> cases b <;> norm_num [rowPay, colPay]

/-- Expectation of a payoff matrix when row plays `Straight` with probability `p` and column
plays `Straight` with probability `q`. -/
def expect (f : Act → Act → ℚ) (p q : ℚ) : ℚ :=
  (1 - p) * (1 - q) * f swerve swerve + (1 - p) * q * f swerve straight
    + p * (1 - q) * f straight swerve + p * q * f straight straight

def rowU (p q : ℚ) : ℚ := expect rowPay p q
def colU (p q : ℚ) : ℚ := expect colPay p q

/-- Mixed Nash equilibrium; strategies are probabilities of `Straight`. -/
def MixedNash (p q : ℚ) : Prop :=
  (0 ≤ p ∧ p ≤ 1) ∧ (0 ≤ q ∧ q ≤ 1) ∧
  (∀ p', 0 ≤ p' → p' ≤ 1 → rowU p' q ≤ rowU p q) ∧
  (∀ q', 0 ≤ q' → q' ≤ 1 → colU p q' ≤ colU p q)

theorem rowU_eq (p q : ℚ) : rowU p q = p - q - 10 * p * q := by
  simp [rowU, expect, rowPay]; ring

theorem colU_eq (p q : ℚ) : colU p q = q - p - 10 * p * q := by
  simp [colU, expect, colPay]; ring

theorem symMixedNash_iff (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    MixedNash p p ↔ p = 1 / 10 := by
  constructor
  · rintro ⟨_, _, hr, _⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hr 1 (by norm_num) le_rfl
      rw [rowU_eq, rowU_eq] at this
      nlinarith
    · have := hr 0 le_rfl (by norm_num)
      rw [rowU_eq, rowU_eq] at this
      nlinarith
  · rintro rfl
    refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
    · intro p' _ _
      rw [rowU_eq, rowU_eq]; linarith
    · intro q' _ _
      rw [colU_eq, colU_eq]; linarith

theorem symMixedNash_payoff : rowU (1 / 10) (1 / 10) = -1 / 10 ∧
    colU (1 / 10) (1 / 10) = -1 / 10 := by
  rw [rowU_eq, colU_eq]; norm_num

theorem commit_beats_mixed (b : Act) (h : ColBR straight b) :
    rowU (1 / 10) (1 / 10) < rowPay straight b := by
  rw [(commit_straight b h).2, symMixedNash_payoff.1]; norm_num

theorem not_symMixedNash_one_eleventh : ¬ MixedNash (1 / 11) (1 / 11) := by
  intro h
  have := (symMixedNash_iff (1 / 11) (by norm_num) (by norm_num)).1 h
  norm_num at this

theorem rowU_one_eleventh : rowU (1 / 11) (1 / 11) = -10 / 121 ∧
    rowU (1 / 11) (1 / 11) ≠ -1 / 11 := by
  rw [rowU_eq]; norm_num

theorem symMixedNash_payoff_ne : rowU (1 / 10) (1 / 10) ≠ -1 / 11 := by
  rw [symMixedNash_payoff.1]; norm_num

/-! ## (2) Rock-paper-scissors -/

inductive RPS
  | rock
  | paper
  | scissors
  deriving DecidableEq, Repr

open RPS

instance : Fintype RPS :=
  ⟨{rock, paper, scissors}, fun x => by cases x <;> decide⟩

/-- Row payoff; the column payoff is its negative. -/
def rpsPay : RPS → RPS → ℚ
  | rock, rock => 0
  | rock, paper => -1
  | rock, scissors => 1
  | paper, rock => 1
  | paper, paper => 0
  | paper, scissors => -1
  | scissors, rock => -1
  | scissors, paper => 1
  | scissors, scissors => 0

/-- `b` is a best response (as column, payoff `-rpsPay a b`) to `a`. -/
def RpsBR (a b : RPS) : Prop := ∀ b', -rpsPay a b' ≤ -rpsPay a b

theorem rpsBR_rock_iff (b : RPS) : RpsBR rock b ↔ b = paper := by
  unfold RpsBR
  constructor
  · intro h
    have := h paper
    cases b <;> simp [rpsPay] at this ⊢ <;> norm_num at this
  · rintro rfl b'
    cases b' <;> simp [rpsPay]

theorem rock_every_round (s : ℕ → RPS) (hs : ∀ n, RpsBR rock (s n)) (n : ℕ) :
    s n = paper ∧ rpsPay rock (s n) = -1 := by
  have := (rpsBR_rock_iff (s n)).1 (hs n)
  rw [this]; exact ⟨rfl, rfl⟩

theorem rpsPay_ge_neg_one (a b : RPS) : -1 ≤ rpsPay a b := by
  cases a <;> cases b <;> simp [rpsPay]

theorem univ_RPS : (Finset.univ : Finset RPS) = {rock, paper, scissors} := rfl

theorem uniform_guarantees_zero (q : RPS → ℚ) :
    ∑ a : RPS, ∑ b : RPS, (1 / 3 : ℚ) * q b * rpsPay a b = 0 := by
  simp [univ_RPS, rpsPay]
  ring

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

theorem matcher_add_four (k : ℕ) : matcher (k + 4) = matcher k := by
  simp [matcher, mismatcher]

theorem mismatcher_add_four (k : ℕ) : mismatcher (k + 4) = mismatcher k := by
  simp [matcher, mismatcher]

end RockCommitmentA
