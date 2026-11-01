import Mathlib

/-!
# Fame credit: a reinforcing urn with a quality term

Two kinds of idea, counts `a` and `b`. Each round one more copy is made: an existing copy is chosen with probability
proportional to its kind's attention weight (`wA` or `wB`) times how many copies there are, and a new copy of the
chosen kind is added. Pure fame is `wA = wB` (copy what is already copied); a quality term makes the weights differ.

PROVED:
* `weighted_urn_drift`: the expected change in A's share after one copy is exactly
  `a * b * (wA - wB) / ((a + b) * (a + b + 1) * (a * wA + b * wB))`.
* `pure_fame_selects_nothing`: with equal weights the expected share does not move (the Pólya martingale).
* `quality_is_selected_iff`: with positive counts and weights, A's expected share rises if and only if `wA > wB`.
* `drift_fades`: the per-round drift is at most `|wA - wB| / (4 (a + b + 1) min wA wB)`, so selection per copy
  fades like `1/N` as the population grows; the early rounds are where both luck and quality do their work.
INTERPRETED (not formalized): attention as the host's logit weight `exp (u/τ)`; citations and imitation as copies.
-/

namespace FameCredit

noncomputable def nextShare (a b wA wB : ℝ) : ℝ :=
  (a * wA * ((a + 1) / (a + b + 1)) + b * wB * (a / (a + b + 1))) / (a * wA + b * wB)

theorem weighted_urn_drift (a b wA wB : ℝ) (ha : 0 < a) (hb : 0 < b) (hA : 0 < wA) (hB : 0 < wB) :
    nextShare a b wA wB - a / (a + b) = a * b * (wA - wB) / ((a + b) * (a + b + 1) * (a * wA + b * wB)) := by
  unfold nextShare
  have h1 : 0 < a + b := by linarith
  have h2 : 0 < a + b + 1 := by linarith
  have h3 : 0 < a * wA + b * wB := by positivity
  field_simp
  ring

theorem pure_fame_selects_nothing (a b w : ℝ) (ha : 0 < a) (hb : 0 < b) (hw : 0 < w) :
    nextShare a b w w = a / (a + b) := by
  have := weighted_urn_drift a b w w ha hb hw hw
  simp at this
  linarith

theorem quality_is_selected_iff (a b wA wB : ℝ) (ha : 0 < a) (hb : 0 < b) (hA : 0 < wA) (hB : 0 < wB) :
    a / (a + b) < nextShare a b wA wB ↔ wB < wA := by
  have hd := weighted_urn_drift a b wA wB ha hb hA hB
  have hden : 0 < (a + b) * (a + b + 1) * (a * wA + b * wB) := by positivity
  rw [← sub_pos, hd, div_pos_iff_of_pos_right hden, mul_pos_iff_of_pos_left (mul_pos ha hb), sub_pos]

theorem drift_fades (a b wA wB : ℝ) (ha : 0 < a) (hb : 0 < b) (hA : 0 < wA) (hB : 0 < wB) :
    |nextShare a b wA wB - a / (a + b)| ≤ |wA - wB| / (4 * (a + b + 1) * min wA wB) := by
  rw [weighted_urn_drift a b wA wB ha hb hA hB]
  have hm : 0 < min wA wB := lt_min hA hB
  have hmA : min wA wB ≤ wA := min_le_left _ _
  have hmB : min wA wB ≤ wB := min_le_right _ _
  have hS : (a + b) * min wA wB ≤ a * wA + b * wB := by nlinarith
  have hab4 : 4 * (a * b) ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have hden : 0 < (a + b) * (a + b + 1) * (a * wA + b * wB) := by positivity
  rw [abs_div, abs_mul, abs_of_pos (mul_pos ha hb), abs_of_pos hden, div_le_div_iff₀ hden (by positivity)]
  have key : 4 * (a * b) * min wA wB ≤ (a + b) * (a * wA + b * wB) := by
    nlinarith [mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ a + b)]
  nlinarith [mul_le_mul_of_nonneg_left key (mul_nonneg (abs_nonneg (wA - wB)) (by positivity : (0 : ℝ) ≤ a + b + 1))]

end FameCredit
