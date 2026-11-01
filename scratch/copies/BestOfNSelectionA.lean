import Mathlib

/-!
# Best-of-N selection with uniform finite scores

Model: N independent copies, each producing a score uniform on `{1, …, m}`.
An outcome is a function `f : Fin N → Fin m`; copy `i` scores `(f i).val + 1`.
All `m ^ N` outcomes are equally likely, so a probability is a count divided by `m ^ N`.
The best score is `bestScore f = sup_i ((f i).val + 1)` (equal to `0` when `N = 0`).

PROVED
* `card_score_le` : for `j ≤ m`, exactly `j` of the `m` scores are `≤ j`.
* `card_bestScore_le` : for `j ≤ m`, the number of outcomes whose best score is `≤ j` is `j ^ N`.
* `card_bestScore_le_of_ge` : for `m ≤ j`, every one of the `m ^ N` outcomes has best score `≤ j`.
* `prob_bestScore_le` : for `j ≤ m`, `P(best ≤ j) = (j / m) ^ N`.
* `bestScore_le_top` : the best score never exceeds `m`.
* `card_bestScore_eq_top` : for `0 < m`, the number of outcomes whose best score equals `m`
  is `m ^ N - (m - 1) ^ N`.
* `prob_bestScore_eq_top` : for `0 < m`, `P(best = m) = 1 - ((m - 1) / m) ^ N`.

INTERPRETED
* "Independent uniform scores on {1,…,m}" is interpreted as the uniform (counting) measure on
  functions `Fin N → Fin m`, with the score shifted by one; probability = count / `m ^ N`.
* The hypothesis `0 < m` is needed for the top-score statement: for `m = 0` and `N = 0` the
  single empty outcome has best score `0 = m`, while `m ^ 0 - (m - 1) ^ 0 = 0`.
-/

namespace BestOfNSelectionA

open Finset

/-- Score of a value `x : Fin m`, taking values in `{1, …, m}`. -/
def score {m : ℕ} (x : Fin m) : ℕ := x.val + 1

/-- Best score among the `N` copies (`0` if there are no copies). -/
def bestScore {N m : ℕ} (f : Fin N → Fin m) : ℕ := univ.sup fun i => score (f i)

theorem card_score_le {m j : ℕ} (hj : j ≤ m) :
    (univ.filter fun x : Fin m => score x ≤ j).card = j := by
  have h : (univ.filter fun x : Fin m => score x ≤ j) =
      (univ : Finset (Fin j)).map (Fin.castLEEmb hj) := by
    ext x
    rw [mem_filter, mem_map]
    simp only [mem_univ, true_and, Fin.castLEEmb_apply]
    constructor
    · intro hx
      exact ⟨⟨x.val, by unfold score at hx; omega⟩, Fin.ext rfl⟩
    · rintro ⟨y, rfl⟩
      unfold score
      rw [Fin.val_castLE]
      omega
  rw [h, card_map, card_univ, Fintype.card_fin]

theorem bestScore_le_iff {N m j : ℕ} (f : Fin N → Fin m) :
    bestScore f ≤ j ↔ ∀ i, score (f i) ≤ j := by
  simp [bestScore, Finset.sup_le_iff]

theorem filter_bestScore_le (N m j : ℕ) :
    (univ.filter fun f : Fin N → Fin m => bestScore f ≤ j) =
      Fintype.piFinset fun _ : Fin N => univ.filter fun x : Fin m => score x ≤ j := by
  ext f
  simp [bestScore_le_iff, Fintype.mem_piFinset]

theorem card_bestScore_le {N m j : ℕ} (hj : j ≤ m) :
    (univ.filter fun f : Fin N → Fin m => bestScore f ≤ j).card = j ^ N := by
  rw [filter_bestScore_le, Fintype.card_piFinset, card_score_le hj, prod_const, card_univ,
    Fintype.card_fin]

theorem bestScore_le_top {N m : ℕ} (f : Fin N → Fin m) : bestScore f ≤ m := by
  rw [bestScore_le_iff]
  intro i
  have := (f i).isLt
  simp only [score]
  omega

theorem card_bestScore_le_of_ge {N m j : ℕ} (hj : m ≤ j) :
    (univ.filter fun f : Fin N → Fin m => bestScore f ≤ j).card = m ^ N := by
  rw [filter_true_of_mem (fun f _ => (bestScore_le_top f).trans hj), card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

theorem prob_bestScore_le {N m j : ℕ} (hj : j ≤ m) :
    ((univ.filter fun f : Fin N → Fin m => bestScore f ≤ j).card : ℚ) /
        (Fintype.card (Fin N → Fin m) : ℚ) = ((j : ℚ) / m) ^ N := by
  rw [card_bestScore_le hj, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, div_pow]
  push_cast
  rfl

theorem card_bestScore_eq_top {N m : ℕ} (hm : 0 < m) :
    (univ.filter fun f : Fin N → Fin m => bestScore f = m).card = m ^ N - (m - 1) ^ N := by
  have hsplit : (univ.filter fun f : Fin N → Fin m => bestScore f = m) =
      univ.filter fun f : Fin N → Fin m => ¬ bestScore f ≤ m - 1 := by
    ext f
    have := bestScore_le_top f
    simp only [mem_filter, mem_univ, true_and]
    omega
  rw [hsplit, filter_not, card_sdiff_of_subset (filter_subset _ _), card_bestScore_le (by omega),
    card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

theorem prob_bestScore_eq_top {N m : ℕ} (hm : 0 < m) :
    ((univ.filter fun f : Fin N → Fin m => bestScore f = m).card : ℚ) /
        (Fintype.card (Fin N → Fin m) : ℚ) = 1 - (((m : ℚ) - 1) / m) ^ N := by
  have hle : (m - 1) ^ N ≤ m ^ N := Nat.pow_le_pow_left (Nat.sub_le m 1) N
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [card_bestScore_eq_top hm, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one,
    div_pow, sub_div, div_self (pow_ne_zero N hm')]

end BestOfNSelectionA
