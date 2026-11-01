import Mathlib

/-!
# Tic-tac-toe is the game "pick three numbers summing to 15", and what a side channel is

Number the cells 0–8 row by row and write the Lo Shu magic square on them:
```
4 9 2
3 5 7
8 1 6
```
PROVED:
* `loShu_bij`: the labels are exactly 1–9, each once.
* `line_iff_fifteen`: three distinct cells form a line (row, column or diagonal) iff their labels sum to 15.
* `win_iff_fifteen`: a set of cells contains a line iff it contains three distinct labels summing to 15. So
  tic-tac-toe and "take turns picking numbers 1–9; first to hold three that sum to 15 wins" are the same game in two
  encodings.
* `rot_preserves_lines`: the quarter turn of the board maps lines to lines, so "contains a line" is a property of the
  game, not of the encoding.
* `label_not_invariant`: the quarter turn changes the label on a cell, so the number you see is a property of the
  encoding: an observer who can read it learns which of the equivalent encodings is in use, not anything about the
  game. That is the shape of a side channel.
* `parity_invariant`: the parity of the label is invariant under the quarter turn (corners even, edges odd, centre 5),
  so parity, unlike magnitude, is a property of the game.
INTERPRETED (not formalized): a phonetic pun reads a property of the encoding (the sound), which synonym substitution
does not preserve; a semantic pun reads a property of the meaning, which it does.
-/

namespace LoShu

def lo : Fin 9 → ℕ := ![4, 9, 2, 3, 5, 7, 8, 1, 6]

def lines : List (ℕ × ℕ × ℕ) :=
  [(0, 1, 2), (3, 4, 5), (6, 7, 8), (0, 3, 6), (1, 4, 7), (2, 5, 8), (0, 4, 8), (2, 4, 6)]

def inLine (l : ℕ × ℕ × ℕ) (x : ℕ) : Bool := x == l.1 || x == l.2.1 || x == l.2.2

def isLine (a b c : Fin 9) : Bool := lines.any fun l => inLine l a.val && inLine l b.val && inLine l c.val

def rot : Fin 9 → Fin 9 := ![2, 5, 8, 1, 4, 7, 0, 3, 6]

theorem loShu_bij : Function.Injective lo ∧ ∀ c, 1 ≤ lo c ∧ lo c ≤ 9 := by
  refine ⟨?_, ?_⟩
  · intro a b h; revert a b; decide
  · decide

theorem line_iff_fifteen : ∀ a b c : Fin 9, a ≠ b → b ≠ c → a ≠ c →
    (isLine a b c = true ↔ lo a + lo b + lo c = 15) := by
  decide

theorem win_iff_fifteen (S : Finset (Fin 9)) :
    (∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ isLine a b c = true) ↔
      (∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ lo a + lo b + lo c = 15) := by
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, h1, h2, h3, h⟩
    exact ⟨a, ha, b, hb, c, hc, h1, h2, h3, (line_iff_fifteen a b c h1 h2 h3).1 h⟩
  · rintro ⟨a, ha, b, hb, c, hc, h1, h2, h3, h⟩
    exact ⟨a, ha, b, hb, c, hc, h1, h2, h3, (line_iff_fifteen a b c h1 h2 h3).2 h⟩

theorem rot_preserves_lines : ∀ a b c : Fin 9, isLine (rot a) (rot b) (rot c) = isLine a b c := by
  decide

theorem label_not_invariant : lo (rot 0) ≠ lo 0 := by decide

theorem parity_invariant : ∀ c : Fin 9, lo (rot c) % 2 = lo c % 2 := by decide

end LoShu
