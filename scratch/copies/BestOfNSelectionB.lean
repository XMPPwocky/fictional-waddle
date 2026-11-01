import Mathlib

/-!
# Best-of-N selection with uniform finite scores

Model: an outcome of N independent copies is a function `f : Fin N → Fin m`; copy `i`
has score `(f i).val + 1 ∈ {1, …, m}`. The uniform product measure is counting
measure on `Fin N → Fin m` divided by `m ^ N`. The best score is
`maxScore f = sup_i ((f i).val + 1)` (equal to `0` when `N = 0`).

PROVED
* `mem_maxScore_le_iff`: the maximum is at most `j` iff every copy scores at most `j`.
* `maxScore_le_top`: the maximum never exceeds `m`.
* `filter_maxScore_le_eq`: the event {max ≤ j} is the product set of {x | x.val < j}.
* `card_outcomes`: there are `m ^ N` outcomes.
* `card_maxScore_le_min`: for any `j`, the number of outcomes with maximum `≤ j` is
  `(min m j) ^ N`.
* `card_maxScore_le`: for `j ≤ m`, that number is `j ^ N`.
* `card_maxScore_eq_top`: for `0 < m`, the number of outcomes whose best copy scores `m`
  is `m ^ N - (m - 1) ^ N`.
* `prob_maxScore_le`: for `j ≤ m`, P(max ≤ j) = (j/m)^N (in `ℚ`).
* `prob_best_reaches_top`: for `0 < m`, P(max = m) = 1 - ((m-1)/m)^N (in `ℚ`).
* `prob_maxScore_le_real`, `prob_best_reaches_top_real`: the same two identities in `ℝ`.

The hypothesis `0 < m` in `card_maxScore_eq_top` is needed: for `m = 0, N = 0` there is one
outcome, its maximum is `0 = m`, but `0 ^ 0 - (0 - 1) ^ 0 = 0` in `ℕ`.
-/

namespace BestOfNSelectionB

open Finset

/-- The best score among the N copies; copy `i` scores `(f i).val + 1`. -/
def maxScore {N m : ℕ} (f : Fin N → Fin m) : ℕ :=
  Finset.univ.sup (fun i => (f i).val + 1)

theorem mem_maxScore_le_iff {N m : ℕ} (f : Fin N → Fin m) (j : ℕ) :
    maxScore f ≤ j ↔ ∀ i, (f i).val + 1 ≤ j := by
  simp [maxScore, Finset.sup_le_iff]

theorem maxScore_le_top {N m : ℕ} (f : Fin N → Fin m) : maxScore f ≤ m := by
  rw [mem_maxScore_le_iff]
  intro i
  exact (f i).isLt

theorem filter_maxScore_le_eq {N m : ℕ} (j : ℕ) :
    (Finset.univ.filter (fun f : Fin N → Fin m => maxScore f ≤ j)) =
      Fintype.piFinset (fun _ : Fin N => Finset.univ.filter (fun x : Fin m => x.val < j)) := by
  ext f
  simp [mem_maxScore_le_iff, Fintype.mem_piFinset]

theorem card_maxScore_le_min (N m j : ℕ) :
    (Finset.univ.filter (fun f : Fin N → Fin m => maxScore f ≤ j)).card = (min m j) ^ N := by
  rw [filter_maxScore_le_eq, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  exact Fin.card_filter_val_lt

theorem card_maxScore_le (N : ℕ) {m j : ℕ} (hj : j ≤ m) :
    (Finset.univ.filter (fun f : Fin N → Fin m => maxScore f ≤ j)).card = j ^ N := by
  rw [card_maxScore_le_min, min_eq_right hj]

theorem card_maxScore_eq_top (N : ℕ) {m : ℕ} (hm : 0 < m) :
    (Finset.univ.filter (fun f : Fin N → Fin m => maxScore f = m)).card =
      m ^ N - (m - 1) ^ N := by
  have hset : (Finset.univ.filter (fun f : Fin N → Fin m => maxScore f = m)) =
      (Finset.univ.filter (fun f : Fin N → Fin m => maxScore f ≤ m)) \
        (Finset.univ.filter (fun f : Fin N → Fin m => maxScore f ≤ m - 1)) := by
    ext f
    have h := maxScore_le_top f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    omega
  have hsub : (Finset.univ.filter (fun f : Fin N → Fin m => maxScore f ≤ m - 1)) ⊆
      (Finset.univ.filter (fun f : Fin N → Fin m => maxScore f ≤ m)) := by
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    omega
  rw [hset, Finset.card_sdiff_of_subset hsub, card_maxScore_le N le_rfl,
    card_maxScore_le N (Nat.sub_le m 1)]

theorem card_outcomes (N m : ℕ) : Fintype.card (Fin N → Fin m) = m ^ N := by
  simp

theorem prob_maxScore_le (N : ℕ) {m j : ℕ} (hj : j ≤ m) :
    ((Finset.univ.filter (fun f : Fin N → Fin m => maxScore f ≤ j)).card : ℚ) /
        (Fintype.card (Fin N → Fin m) : ℚ) = ((j : ℚ) / m) ^ N := by
  rw [card_maxScore_le N hj, card_outcomes, div_pow]
  push_cast
  rfl

theorem prob_best_reaches_top (N : ℕ) {m : ℕ} (hm : 0 < m) :
    ((Finset.univ.filter (fun f : Fin N → Fin m => maxScore f = m)).card : ℚ) /
        (Fintype.card (Fin N → Fin m) : ℚ) = 1 - (((m : ℚ) - 1) / m) ^ N := by
  have hle : (m - 1) ^ N ≤ m ^ N := Nat.pow_le_pow_left (Nat.sub_le m 1) N
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpow : ((m : ℚ)) ^ N ≠ 0 := pow_ne_zero N hmq
  rw [card_maxScore_eq_top N hm, card_outcomes, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hm.ne'), div_pow, sub_div, div_self hpow]
  push_cast
  rfl

theorem prob_maxScore_le_real (N : ℕ) {m j : ℕ} (hj : j ≤ m) :
    ((Finset.univ.filter (fun f : Fin N → Fin m => maxScore f ≤ j)).card : ℝ) /
        (Fintype.card (Fin N → Fin m) : ℝ) = ((j : ℝ) / m) ^ N := by
  have h := prob_maxScore_le N hj
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  push_cast at h'
  exact h'

theorem prob_best_reaches_top_real (N : ℕ) {m : ℕ} (hm : 0 < m) :
    ((Finset.univ.filter (fun f : Fin N → Fin m => maxScore f = m)).card : ℝ) /
        (Fintype.card (Fin N → Fin m) : ℝ) = 1 - (((m : ℝ) - 1) / m) ^ N := by
  have h := prob_best_reaches_top N hm
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  push_cast at h'
  exact h'

end BestOfNSelectionB
