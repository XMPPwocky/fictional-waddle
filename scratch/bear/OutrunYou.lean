import Mathlib

/-!
# You only have to outrun the other hiker

Two hikers with speeds `a` and `b`; the bear catches the slower one.

PROVED:
* `survives_iff_faster`: hiker 1 escapes iff `b < a`; the bear's own speed never enters.
* `relative_only`: applying any strictly increasing transformation to both speeds (everyone trains, everyone gets
  shoes) changes nothing about who escapes.
* `zero_sum_escape`: with distinct speeds, exactly one hiker escapes, whatever the speeds; speeding up can only move
  the escape from the other hiker to you.
INTERPRETED (not formalized): benchmarks as outrunning the other hiker, deployment as outrunning the bear.
-/

namespace OutrunYou

def escapes (mine theirs : ℝ) : Prop := theirs < mine

theorem survives_iff_faster (a b : ℝ) : escapes a b ↔ b < a := Iff.rfl

theorem relative_only (f : ℝ → ℝ) (hf : StrictMono f) (a b : ℝ) : escapes (f a) (f b) ↔ escapes a b :=
  hf.lt_iff_lt

theorem zero_sum_escape (a b : ℝ) (h : a ≠ b) : (escapes a b ∧ ¬ escapes b a) ∨ (escapes b a ∧ ¬ escapes a b) := by
  unfold escapes
  rcases lt_or_gt_of_ne h with h' | h'
  · right; exact ⟨h', not_lt.mpr h'.le⟩
  · left; exact ⟨h', not_lt.mpr h'.le⟩

end OutrunYou
