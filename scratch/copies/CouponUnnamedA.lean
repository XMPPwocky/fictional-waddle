import Mathlib

/-!
# Expected number of undiscovered planets

Model: `k` discoveries, each an element of `Fin n` (the planet found); a discovery history
is a function `f : Fin k → Fin n`, all `n ^ k` histories equally likely. The number of
planets never discovered under `f` is `undiscovered f = #{i | ∀ j, f j ≠ i}`.

PROVED
* `card_avoiding` : for each planet `i`, the number of histories that never
  discover `i` is `(n - 1) ^ k`.
* `card_histories` : there are `n ^ k` histories.
* `sum_undiscovered` : summing the undiscovered count over all histories gives
  `n * (n - 1) ^ k` (linearity: swap the two sums and use `card_avoiding`).
* `expected_undiscovered` : for `n ≥ 1`, the uniform average of `undiscovered` over all
  histories, `(∑ f, undiscovered f) / n ^ k`, equals `n * (1 - 1/n) ^ k` in `ℝ`.
-/

namespace CouponUnnamedA

open Finset

/-- Number of planets never discovered in the history `f`. -/
def undiscovered {n k : ℕ} (f : Fin k → Fin n) : ℕ :=
  #(univ.filter fun i : Fin n => ∀ j, f j ≠ i)

theorem card_avoiding (n k : ℕ) (i : Fin n) :
    #(univ.filter fun f : Fin k → Fin n => ∀ j, f j ≠ i) = (n - 1) ^ k := by
  have h : (univ.filter fun f : Fin k → Fin n => ∀ j, f j ≠ i) =
      Fintype.piFinset (fun _ : Fin k => univ.erase i) := by
    ext f
    simp [Fintype.mem_piFinset, Finset.mem_erase]
  rw [h, Fintype.card_piFinset]
  simp [Finset.card_erase_of_mem]

theorem card_histories (n k : ℕ) : Fintype.card (Fin k → Fin n) = n ^ k := by
  simp

theorem sum_undiscovered (n k : ℕ) :
    ∑ f : Fin k → Fin n, undiscovered f = n * (n - 1) ^ k := by
  unfold undiscovered
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  simp_rw [← Finset.card_filter, card_avoiding]
  simp

theorem expected_undiscovered (n k : ℕ) (hn : 1 ≤ n) :
    ((∑ f : Fin k → Fin n, undiscovered f : ℕ) : ℝ) / (n : ℝ) ^ k
      = n * (1 - 1 / (n : ℝ)) ^ k := by
  rw [sum_undiscovered]
  have hn' : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; simp
  push_cast [hsub]
  rw [one_sub_div hn', div_pow]
  field_simp

end CouponUnnamedA
