import Mathlib

/-!
# Level-k reasoning in matching pennies

Actions are `Bool`. The Matcher wins iff the two actions are equal; the
Mismatcher wins iff they differ. Level 0 for both players is the fixed action
`true`. A level-(k+1) Matcher plays what a level-k Mismatcher plays; a
level-(k+1) Mismatcher plays the negation of what a level-k Matcher plays.

PROVED
* `matcher_add_four`, `mismatcher_add_four`: both level sequences have period 4.
* `matcher_period_not_two`, `mismatcher_period_not_two`: there is `k` with
  `matcher (k+2) ≠ matcher k` (resp. `mismatcher`), so the minimal period is
  not 1 or 2; `matcher_period_not_one`, `mismatcher_period_not_one` also
  exhibit a failure of period 1 directly.
* `matcherWins_mod_four`, `matcherWins_congr_mod_four`: whether a level-k
  Matcher beats a level-j Mismatcher depends only on `k % 4` and `j % 4`.
* `matcherWins_table`: the full 4×4 table over `Fin 4`, by `decide`;
  `matcherWins_iff_table`: the table determines the outcome for all `k j`.
* `matcher_succ_beats`: a level-(j+1) Matcher beats a level-j Mismatcher;
  `mismatcher_succ_beats`: a level-(k+1) Mismatcher beats a level-k Matcher.

INTERPRETED
* "The Matcher at level k beats the Mismatcher at level j" is the proposition
  `matcher k = mismatcher j` (`matcherWins k j`); the Mismatcher wins exactly
  when this fails (`mismatcherWins k j := matcher k ≠ mismatcher j`).
* The table `winTable : Fin 4 → Fin 4 → Bool` lists rows indexed by the
  Matcher's level mod 4 and columns by the Mismatcher's level mod 4.
-/

namespace YomiCycleA

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

/-- The Matcher (level `k`) beats the Mismatcher (level `j`). -/
def matcherWins (k j : ℕ) : Prop := matcher k = mismatcher j

/-- The Mismatcher (level `j`) beats the Matcher (level `k`). -/
def mismatcherWins (k j : ℕ) : Prop := matcher k ≠ mismatcher j

instance (k j : ℕ) : Decidable (matcherWins k j) :=
  inferInstanceAs (Decidable (matcher k = mismatcher j))

instance (k j : ℕ) : Decidable (mismatcherWins k j) :=
  inferInstanceAs (Decidable (matcher k ≠ mismatcher j))

theorem matcher_add_two (k : ℕ) : matcher (k + 2) = !(matcher k) := by
  simp

theorem mismatcher_add_two (k : ℕ) : mismatcher (k + 2) = !(mismatcher k) := by
  simp

/-- (1) Matcher levels cycle with period 4. -/
theorem matcher_add_four (k : ℕ) : matcher (k + 4) = matcher k := by
  simp

/-- (1) Mismatcher levels cycle with period 4. -/
theorem mismatcher_add_four (k : ℕ) : mismatcher (k + 4) = mismatcher k := by
  simp

theorem matcher_mod_four (k : ℕ) : matcher k = matcher (k % 4) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k 4 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
      rw [matcher_add_four, ih m (by omega), Nat.add_mod_right]

theorem mismatcher_mod_four (k : ℕ) : mismatcher k = mismatcher (k % 4) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k 4 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
      rw [mismatcher_add_four, ih m (by omega), Nat.add_mod_right]

/-- (2) The Matcher sequence does not have period 2. -/
theorem matcher_period_not_two : ∃ k, matcher (k + 2) ≠ matcher k :=
  ⟨0, by simp⟩

/-- (2) The Mismatcher sequence does not have period 2. -/
theorem mismatcher_period_not_two : ∃ k, mismatcher (k + 2) ≠ mismatcher k :=
  ⟨0, by simp⟩

/-- (2) The Matcher sequence does not have period 1. -/
theorem matcher_period_not_one : ∃ k, matcher (k + 1) ≠ matcher k :=
  ⟨1, by simp⟩

/-- (2) The Mismatcher sequence does not have period 1. -/
theorem mismatcher_period_not_one : ∃ k, mismatcher (k + 1) ≠ mismatcher k :=
  ⟨0, by simp⟩

/-- (2) Every period of the Matcher sequence is a multiple of 4 (no period
`p` with `0 < p` and `4 ∤ p`); in particular the minimal period is exactly 4. -/
theorem matcher_period_dvd (p : ℕ) (hp : ∀ k, matcher (k + p) = matcher k) :
    4 ∣ p := by
  have h0 := hp 0
  have h1 := hp 1
  rw [matcher_mod_four (0 + p)] at h0
  rw [matcher_mod_four (1 + p)] at h1
  have : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have e0 : (0 + p) % 4 = p % 4 := by omega
  have e1 : (1 + p) % 4 = (1 + p % 4) % 4 := by omega
  rw [e0] at h0
  rw [e1] at h1
  interval_cases hr : p % 4
  · exact Nat.dvd_of_mod_eq_zero hr
  all_goals simp at h0 h1

/-- (2) Every period of the Mismatcher sequence is a multiple of 4. -/
theorem mismatcher_period_dvd (p : ℕ) (hp : ∀ k, mismatcher (k + p) = mismatcher k) :
    4 ∣ p := by
  have h0 := hp 0
  have h1 := hp 1
  rw [mismatcher_mod_four (0 + p)] at h0
  rw [mismatcher_mod_four (1 + p)] at h1
  have : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have e0 : (0 + p) % 4 = p % 4 := by omega
  have e1 : (1 + p) % 4 = (1 + p % 4) % 4 := by omega
  rw [e0] at h0
  rw [e1] at h1
  interval_cases hr : p % 4
  · exact Nat.dvd_of_mod_eq_zero hr
  all_goals simp at h0 h1

/-- (3) The outcome depends only on the levels mod 4. -/
theorem matcherWins_mod_four (k j : ℕ) :
    matcherWins k j ↔ matcherWins (k % 4) (j % 4) := by
  unfold matcherWins
  rw [matcher_mod_four k, mismatcher_mod_four j]

/-- (3) Levels congruent mod 4 give the same outcome. -/
theorem matcherWins_congr_mod_four {k k' j j' : ℕ}
    (hk : k % 4 = k' % 4) (hj : j % 4 = j' % 4) :
    matcherWins k j ↔ matcherWins k' j' := by
  rw [matcherWins_mod_four k j, matcherWins_mod_four k' j', hk, hj]

/-- The win table: `winTable a b = true` iff a Matcher at level ≡ a (mod 4)
beats a Mismatcher at level ≡ b (mod 4). Rows: Matcher level; columns:
Mismatcher level. -/
def winTable : Fin 4 → Fin 4 → Bool
  | 0, 0 => true  | 0, 1 => false | 0, 2 => false | 0, 3 => true
  | 1, 0 => true  | 1, 1 => false | 1, 2 => false | 1, 3 => true
  | 2, 0 => false | 2, 1 => true  | 2, 2 => true  | 2, 3 => false
  | 3, 0 => false | 3, 1 => true  | 3, 2 => true  | 3, 3 => false

/-- (4) The full 4×4 win table, checked by `decide`. -/
theorem matcherWins_table :
    ∀ a b : Fin 4, (matcherWins a.val b.val ↔ winTable a b = true) := by
  decide

/-- (4) The table determines the outcome at all levels. -/
theorem matcherWins_iff_table (k j : ℕ) :
    matcherWins k j ↔
      winTable ⟨k % 4, Nat.mod_lt _ (by norm_num)⟩
        ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩ = true := by
  rw [matcherWins_mod_four]
  exact matcherWins_table ⟨k % 4, _⟩ ⟨j % 4, _⟩

/-- (4) Actions at levels 0..3. -/
theorem actions_table :
    (matcher 0, matcher 1, matcher 2, matcher 3) = (true, true, false, false) ∧
    (mismatcher 0, mismatcher 1, mismatcher 2, mismatcher 3) =
      (true, false, false, true) := by
  decide

/-- (5) A level-(j+1) Matcher beats a level-j Mismatcher. -/
theorem matcher_succ_beats (j : ℕ) : matcherWins (j + 1) j := by
  simp [matcherWins]

/-- (5) A level-(k+1) Mismatcher beats a level-k Matcher. -/
theorem mismatcher_succ_beats (k : ℕ) : mismatcherWins k (k + 1) := by
  simp [mismatcherWins]

end YomiCycleA
