import Mathlib

/-!
# Level-k reasoning in matching pennies

Actions are `Bool`. The Matcher wins iff the two actions are equal; the Mismatcher wins iff
they differ. Level 0 of both players is the fixed action `true`. A level-(k+1) Matcher copies
what a level-k Mismatcher plays; a level-(k+1) Mismatcher plays the negation of what a level-k
Matcher plays.

PROVED:
* `matcher_add_four`, `mismatcher_add_four`: `matcher (k+4) = matcher k`,
  `mismatcher (k+4) = mismatcher k` for all `k`.
* `matcher_mod_four`, `mismatcher_mod_four`: both depend only on `k % 4`.
* `matcher_period_not_two`, `mismatcher_period_not_two`: there is `k` with
  `matcher (k+2) ≠ matcher k` (resp. for `mismatcher`); hence neither period is 1 or 2.
* `matcher_period_not_one`, `mismatcher_period_not_one`: there is `k` with
  `matcher (k+1) ≠ matcher k` (resp. for `mismatcher`).
* `minimal_period_matcher`, `minimal_period_mismatcher`: for every `p`,
  `(∀ k, f (k+p) = f k) ↔ 4 ∣ p`, so the least positive period is exactly 4.
* `matcherWins_mod_four`: `matcherWins k j = matcherWins (k % 4) (j % 4)`.
* `winTable`: the full 4×4 table of `matcherWins` over `Fin 4 × Fin 4`, by `decide`;
  `matcherWins_iff_table`: `matcherWins k j = winRow (k % 4) (j % 4)` with the explicit table
  `winRow`.
* `matcher_succ_beats`: a level-(j+1) Matcher beats a level-j Mismatcher.
* `mismatcher_succ_beats`: a level-(k+1) Mismatcher beats a level-k Matcher.

INTERPRETED:
* "Level-k Matcher beats level-j Mismatcher" is `matcherWins k j := matcher k = mismatcher j`
  (as a `Bool` via `==`); "Mismatcher beats Matcher" is its negation, `matcher k ≠ mismatcher j`.
* "Period exactly 4 (not 1 or 2)" is stated both as the requested witnesses and as the
  characterization of all periods: positive `p` is a period iff `4 ∣ p`.
-/

namespace YomiCycleB

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
@[simp] theorem matcher_succ (k : ℕ) : matcher (k + 1) = mismatcher k := by simp [matcher]
@[simp] theorem mismatcher_succ (k : ℕ) : mismatcher (k + 1) = !(matcher k) := by
  simp [mismatcher]

theorem matcher_add_two (k : ℕ) : matcher (k + 2) = !(matcher k) := by
  simp

theorem mismatcher_add_two (k : ℕ) : mismatcher (k + 2) = !(mismatcher k) := by
  simp

/-- (1) The Matcher's yomi layers cycle with period 4. -/
theorem matcher_add_four (k : ℕ) : matcher (k + 4) = matcher k := by
  rw [show k + 4 = (k + 2) + 2 by omega, matcher_add_two, matcher_add_two, Bool.not_not]

/-- (1) The Mismatcher's yomi layers cycle with period 4. -/
theorem mismatcher_add_four (k : ℕ) : mismatcher (k + 4) = mismatcher k := by
  rw [show k + 4 = (k + 2) + 2 by omega, mismatcher_add_two, mismatcher_add_two, Bool.not_not]

theorem matcher_add_mul_four (k n : ℕ) : matcher (k + 4 * n) = matcher k := by
  induction n with
  | zero => simp
  | succ n ih => rw [show k + 4 * (n + 1) = (k + 4 * n) + 4 by ring, matcher_add_four, ih]

theorem mismatcher_add_mul_four (k n : ℕ) : mismatcher (k + 4 * n) = mismatcher k := by
  induction n with
  | zero => simp
  | succ n ih => rw [show k + 4 * (n + 1) = (k + 4 * n) + 4 by ring, mismatcher_add_four, ih]

theorem matcher_mod_four (k : ℕ) : matcher k = matcher (k % 4) := by
  conv_lhs => rw [← Nat.mod_add_div k 4]
  exact matcher_add_mul_four _ _

theorem mismatcher_mod_four (k : ℕ) : mismatcher k = mismatcher (k % 4) := by
  conv_lhs => rw [← Nat.mod_add_div k 4]
  exact mismatcher_add_mul_four _ _

/-- (2) The Matcher's period is not 2 (hence not 1). -/
theorem matcher_period_not_two : ∃ k, matcher (k + 2) ≠ matcher k :=
  ⟨0, by decide⟩

/-- (2) The Mismatcher's period is not 2 (hence not 1). -/
theorem mismatcher_period_not_two : ∃ k, mismatcher (k + 2) ≠ mismatcher k :=
  ⟨0, by decide⟩

/-- (2) The Matcher's period is not 1. -/
theorem matcher_period_not_one : ∃ k, matcher (k + 1) ≠ matcher k :=
  ⟨1, by decide⟩

/-- (2) The Mismatcher's period is not 1. -/
theorem mismatcher_period_not_one : ∃ k, mismatcher (k + 1) ≠ mismatcher k :=
  ⟨0, by decide⟩

/-- If `f (k+2) = !f k` and `f` is not 1-periodic, then the periods of `f` are exactly the
multiples of 4. -/
private theorem period_iff_aux (f : ℕ → Bool) (h2 : ∀ k, f (k + 2) = !(f k))
    (h1 : ∃ k, f (k + 1) ≠ f k) (p : ℕ) :
    (∀ k, f (k + p) = f k) ↔ 4 ∣ p := by
  have h4 : ∀ k, f (k + 4) = f k := fun k => by
    rw [show k + 4 = (k + 2) + 2 by omega, h2, h2, Bool.not_not]
  have hmul : ∀ k n, f (k + 4 * n) = f k := by
    intro k n
    induction n with
    | zero => simp
    | succ n ih => rw [show k + 4 * (n + 1) = (k + 4 * n) + 4 by ring, h4, ih]
  constructor
  · intro hp
    obtain ⟨k0, hk0⟩ := h1
    have hr : ∀ k, f (k + p % 4) = f k := by
      intro k
      have := hp k
      rw [← Nat.mod_add_div p 4, ← add_assoc, hmul] at this
      exact this
    have hlt := Nat.mod_lt p (show 0 < 4 by norm_num)
    interval_cases hm : p % 4
    · exact Nat.dvd_of_mod_eq_zero hm
    · exact absurd (hr k0) hk0
    · exfalso
      have := hr k0
      rw [h2] at this
      cases hf : f k0 <;> simp [hf] at this
    · exfalso
      have e1 := hr (k0 + 1)
      have e2 : f (k0 + 1 + 3) = f (k0 + 4) := by congr 1
      rw [e2, h4] at e1
      exact hk0 e1.symm
  · rintro ⟨n, rfl⟩ k
    exact hmul k n

/-- (2) The periods of `matcher` are exactly the multiples of 4. -/
theorem minimal_period_matcher (p : ℕ) : (∀ k, matcher (k + p) = matcher k) ↔ 4 ∣ p :=
  period_iff_aux matcher matcher_add_two matcher_period_not_one p

/-- (2) The periods of `mismatcher` are exactly the multiples of 4. -/
theorem minimal_period_mismatcher (p : ℕ) :
    (∀ k, mismatcher (k + p) = mismatcher k) ↔ 4 ∣ p :=
  period_iff_aux mismatcher mismatcher_add_two mismatcher_period_not_one p

/-- A level-`k` Matcher beats a level-`j` Mismatcher iff their actions agree. -/
def matcherWins (k j : ℕ) : Bool := matcher k == mismatcher j

/-- (3) The outcome depends only on `k % 4` and `j % 4`. -/
theorem matcherWins_mod_four (k j : ℕ) : matcherWins k j = matcherWins (k % 4) (j % 4) := by
  unfold matcherWins
  rw [matcher_mod_four k, mismatcher_mod_four j]

theorem matcherWins_add_four_left (k j : ℕ) : matcherWins (k + 4) j = matcherWins k j := by
  simp only [matcherWins, matcher_add_four]

theorem matcherWins_add_four_right (k j : ℕ) : matcherWins k (j + 4) = matcherWins k j := by
  simp only [matcherWins, mismatcher_add_four]

/-- The explicit win table: `winRow k j = true` iff a level-`k` Matcher beats a
level-`j` Mismatcher (indices mod 4). Rows are Matcher levels, columns Mismatcher levels. -/
def winRow : Fin 4 → Fin 4 → Bool
  | 0, 0 => true  | 0, 1 => false | 0, 2 => false | 0, 3 => true
  | 1, 0 => true  | 1, 1 => false | 1, 2 => false | 1, 3 => true
  | 2, 0 => false | 2, 1 => true  | 2, 2 => true  | 2, 3 => false
  | 3, 0 => false | 3, 1 => true  | 3, 2 => true  | 3, 3 => false

/-- (4) The full 4×4 win table, by `decide`. -/
theorem winTable : ∀ a b : Fin 4, matcherWins a.val b.val = winRow a b := by
  decide

/-- (4) The win table governs all levels. -/
theorem matcherWins_iff_table (k j : ℕ) :
    matcherWins k j = winRow ⟨k % 4, Nat.mod_lt _ (by norm_num)⟩ ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩ := by
  rw [matcherWins_mod_four]
  exact winTable ⟨k % 4, _⟩ ⟨j % 4, _⟩

/-- (4) The table, written out entry by entry. -/
theorem winTable_explicit :
    matcherWins 0 0 = true  ∧ matcherWins 0 1 = false ∧ matcherWins 0 2 = false ∧ matcherWins 0 3 = true ∧
    matcherWins 1 0 = true  ∧ matcherWins 1 1 = false ∧ matcherWins 1 2 = false ∧ matcherWins 1 3 = true ∧
    matcherWins 2 0 = false ∧ matcherWins 2 1 = true  ∧ matcherWins 2 2 = true  ∧ matcherWins 2 3 = false ∧
    matcherWins 3 0 = false ∧ matcherWins 3 1 = true  ∧ matcherWins 3 2 = true  ∧ matcherWins 3 3 = false := by
  decide

/-- (5) A level-(j+1) Matcher always beats a level-j Mismatcher. -/
theorem matcher_succ_beats (j : ℕ) : matcherWins (j + 1) j = true := by
  simp [matcherWins]

/-- (5) A level-(k+1) Mismatcher always beats a level-k Matcher. -/
theorem mismatcher_succ_beats (k : ℕ) : matcherWins k (k + 1) = false := by
  simp [matcherWins]

/-- (5) Prop form: one level deeper wins, for either role. -/
theorem deeper_wins (k : ℕ) :
    matcher (k + 1) = mismatcher k ∧ mismatcher (k + 1) ≠ matcher k := by
  refine ⟨matcher_succ k, ?_⟩
  rw [mismatcher_succ]
  cases matcher k <;> decide

end YomiCycleB
