import Mathlib

/-!
# Tit-for-tat echo vs. win-stay-lose-shift recovery

Actions are `Bool`, with `true` = cooperate (C) and `false` = defect (D).
A deterministic memory-one strategy is a map `(my previous action, opponent's previous action) ↦
my next action`. Play is the sequence of action pairs `(player 1, player 2)` obtained by iterating
`step` from a start pair.

PROVED
* `tft_echo` : TFT vs TFT from (C,D): the pair at step `n` is (C,D) for even `n` and (D,C) for
  odd `n`, for all `n`.
* `tft_never_recovers` : TFT vs TFT from (C,D) never reaches (C,C).
* `wsls_step_one`, `wsls_step_two`, `wsls_recovers` : WSLS vs WSLS from (C,D) is (D,D) at step 1,
  (C,C) at step 2, and (C,C) at every step `n ≥ 2`.
* `tft_sustains`, `wsls_sustains` : from (C,C) each strategy against itself stays at (C,C) for
  all `n`.

INTERPRETED
* "Without another error" is modelled by error-free deterministic iteration of `step`; the single
  error is encoded as the start pair (C,D).
* Step 0 is the start pair itself.
-/

namespace TitForTatEchoA

/-- `true` = cooperate, `false` = defect. -/
abbrev Action := Bool

/-- A deterministic memory-one strategy: (my last action, opponent's last action) ↦ my action. -/
abbrev Strategy := Action → Action → Action

/-- Tit-for-tat: play the opponent's previous action. -/
def tft : Strategy := fun _ opp => opp

/-- Win-stay-lose-shift: cooperate iff both players played the same action last round. -/
def wsls : Strategy := fun me opp => decide (me = opp)

/-- One round: each player applies its strategy to its own view of the previous pair. -/
def step (s₁ s₂ : Strategy) (p : Action × Action) : Action × Action :=
  (s₁ p.1 p.2, s₂ p.2 p.1)

/-- The action pair at step `n` from start pair `start`. -/
def play (s₁ s₂ : Strategy) (start : Action × Action) : ℕ → Action × Action
  | 0 => start
  | n + 1 => step s₁ s₂ (play s₁ s₂ start n)

/-- (C,D) -/
def CD : Action × Action := (true, false)
/-- (D,C) -/
def DC : Action × Action := (false, true)
/-- (C,C) -/
def CC : Action × Action := (true, true)
/-- (D,D) -/
def DD : Action × Action := (false, false)

theorem tft_echo (n : ℕ) :
    play tft tft CD n = if Even n then CD else DC := by
  induction n with
  | zero => simp [play]
  | succ n ih =>
    rw [play, ih]
    by_cases h : Even n
    · have h' : ¬ Even (n + 1) := Nat.not_even_iff_odd.mpr h.add_one
      simp [h, h', step, tft, CD, DC]
    · have h' : Even (n + 1) := (Nat.not_even_iff_odd.mp h).add_one
      simp [h, h', step, tft, CD, DC]

theorem tft_echo_even (k : ℕ) : play tft tft CD (2 * k) = CD := by
  rw [tft_echo]; simp

theorem tft_echo_odd (k : ℕ) : play tft tft CD (2 * k + 1) = DC := by
  rw [tft_echo]
  have : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)
  simp [this]

theorem tft_never_recovers (n : ℕ) : play tft tft CD n ≠ CC := by
  rw [tft_echo]
  split_ifs <;> decide

theorem wsls_step_one : play wsls wsls CD 1 = DD := by decide

theorem wsls_step_two : play wsls wsls CD 2 = CC := by decide

theorem wsls_recovers (n : ℕ) (hn : 2 ≤ n) : play wsls wsls CD n = CC := by
  induction n, hn using Nat.le_induction with
  | base => exact wsls_step_two
  | succ n _ ih => rw [play, ih]; decide

theorem tft_sustains (n : ℕ) : play tft tft CC n = CC := by
  induction n with
  | zero => rfl
  | succ n ih => rw [play, ih]; decide

theorem wsls_sustains (n : ℕ) : play wsls wsls CC n = CC := by
  induction n with
  | zero => rfl
  | succ n ih => rw [play, ih]; decide

end TitForTatEchoA
