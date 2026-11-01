import Mathlib

/-!
# Tit-for-tat echo vs. win-stay-lose-shift recovery (deterministic memory-one IPD)

Actions are `Bool`, `true` = cooperate (C), `false` = defect (D).
A memory-one strategy is a map `(my last action, opponent's last action) ↦ my next action`.
Play between two strategies is the sequence of action pairs obtained by iterating the joint
update from a start pair; `play s t start n` is the pair at step `n` (step 0 = `start`).

PROVED
* `tft_echo` : TFT vs TFT from (C,D): the pair at step `n` is (C,D) for even `n`
  and (D,C) for odd `n`, for all `n`.
* `tft_echo_even`, `tft_echo_odd` : the two parity cases separately.
* `tft_echo_never_cc` : TFT vs TFT from (C,D) never reaches (C,C) at any step.
* `wsls_step_one`, `wsls_step_two` : WSLS vs WSLS from (C,D) is (D,D) at step 1, (C,C) at step 2.
* `wsls_recovers` : WSLS vs WSLS from (C,D) is (C,C) at every step `n ≥ 2`.
* `tft_sustains_cc`, `wsls_sustains_cc` : from (C,C) each strategy, played against itself,
  stays at (C,C) at every step.
All "for all n" statements are proved by induction on `n`.

INTERPRETED
* "Without another error" is modelled by the error-free deterministic dynamics `play`:
  the only error is the one encoded in the start pair (C,D).
* Player 1's pair component is the first coordinate; the opponent sees the pair swapped.
-/

namespace TitForTatEchoB

/-- `true` = cooperate, `false` = defect. -/
abbrev Action := Bool

/-- Cooperate. -/
abbrev C : Action := true
/-- Defect. -/
abbrev D : Action := false

/-- A deterministic memory-one strategy: (my last action, opponent's last action) ↦ next action. -/
abbrev Strategy := Action → Action → Action

/-- Tit-for-tat: play the opponent's previous action. -/
def tft : Strategy := fun _ theirs => theirs

/-- Win-stay-lose-shift (Pavlov): cooperate iff both played the same action last round. -/
def wsls : Strategy := fun mine theirs => decide (mine = theirs)

/-- One round of joint play: player 1 uses `s`, player 2 uses `t`. -/
def step (s t : Strategy) (p : Action × Action) : Action × Action :=
  (s p.1 p.2, t p.2 p.1)

/-- The action pair at step `n` of play from `start`. -/
def play (s t : Strategy) (start : Action × Action) : ℕ → Action × Action
  | 0 => start
  | n + 1 => step s t (play s t start n)

@[simp] lemma play_zero (s t : Strategy) (start : Action × Action) :
    play s t start 0 = start := rfl

@[simp] lemma play_succ (s t : Strategy) (start : Action × Action) (n : ℕ) :
    play s t start (n + 1) = step s t (play s t start n) := rfl

/-- (1) TFT vs TFT from (C,D): (C,D) at even steps, (D,C) at odd steps. -/
theorem tft_echo (n : ℕ) :
    play tft tft (C, D) n = if Even n then (C, D) else (D, C) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [play_succ, ih]
    by_cases h : Even n
    · have h' : ¬ Even (n + 1) := by simpa [Nat.even_add_one] using h
      simp [h, h', step, tft]
    · have h' : Even (n + 1) := by simpa [Nat.even_add_one] using h
      simp [h, h', step, tft]

theorem tft_echo_even (k : ℕ) : play tft tft (C, D) (2 * k) = (C, D) := by
  rw [tft_echo]; simp

theorem tft_echo_odd (k : ℕ) : play tft tft (C, D) (2 * k + 1) = (D, C) := by
  rw [tft_echo]
  have : ¬ Even (2 * k + 1) := by simp
  simp [this]

/-- (1) Mutual cooperation never returns under TFT vs TFT after a single error. -/
theorem tft_echo_never_cc (n : ℕ) : play tft tft (C, D) n ≠ (C, C) := by
  rw [tft_echo]
  split_ifs <;> simp

/-- (2) WSLS vs WSLS from (C,D): (D,D) at step 1. -/
theorem wsls_step_one : play wsls wsls (C, D) 1 = (D, D) := by decide

/-- (2) WSLS vs WSLS from (C,D): (C,C) at step 2. -/
theorem wsls_step_two : play wsls wsls (C, D) 2 = (C, C) := by decide

/-- (3) WSLS sustains mutual cooperation from (C,C). -/
theorem wsls_sustains_cc (n : ℕ) : play wsls wsls (C, C) n = (C, C) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [play_succ, ih]; decide

/-- (3) TFT sustains mutual cooperation from (C,C). -/
theorem tft_sustains_cc (n : ℕ) : play tft tft (C, C) n = (C, C) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [play_succ, ih]; rfl

/-- Shifting the start: play from step `m` onward is play from the pair at step `m`. -/
theorem play_add (s t : Strategy) (start : Action × Action) (m k : ℕ) :
    play s t start (m + k) = play s t (play s t start m) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, play_succ, ih, play_succ]

/-- (2) WSLS vs WSLS from (C,D) is (C,C) at every step `n ≥ 2`. -/
theorem wsls_recovers (n : ℕ) (hn : 2 ≤ n) : play wsls wsls (C, D) n = (C, C) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [play_add, wsls_step_two, wsls_sustains_cc]

end TitForTatEchoB
