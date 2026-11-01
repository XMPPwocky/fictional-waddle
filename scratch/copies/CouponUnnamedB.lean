import Mathlib

/-!
# Expected number of undiscovered planets

Model: `n` planets indexed by `Fin n`; `k` independent uniform discoveries form a sequence
`f : Fin k → Fin n`, every one of the `n ^ k` sequences being equally likely. The number of
planets never discovered by `f` is `undiscovered f`.

PROVED
* `card_avoiding`: for a fixed planet `p`, exactly `(n - 1) ^ k` sequences never hit `p`.
* `sum_undiscovered`: summed over all `n ^ k` sequences, the number of undiscovered planets
  totals `n * (n - 1) ^ k` (linearity: swap the sum over sequences and over planets).
* `expected_undiscovered`: for `n ≥ 1`, the uniform average of `undiscovered` over all
  sequences equals `n * (1 - 1 / n) ^ k` (as a real number).

INTERPRETED
* "Expected value under k independent uniform discoveries" is the uniform average over the
  `n ^ k` sequences `Fin k → Fin n`, which is the product of `k` uniform distributions.
-/

namespace CouponUnnamedB

open Finset

/-- Number of planets not hit by the discovery sequence `f`. -/
def undiscovered {n k : ℕ} (f : Fin k → Fin n) : ℕ :=
  (univ.filter (fun p : Fin n => ∀ i, f i ≠ p)).card

theorem card_avoiding (n k : ℕ) (p : Fin n) :
    (univ.filter (fun f : Fin k → Fin n => ∀ i, f i ≠ p)).card = (n - 1) ^ k := by
  have h : univ.filter (fun f : Fin k → Fin n => ∀ i, f i ≠ p)
      = Fintype.piFinset (fun _ : Fin k => univ.erase p) := by
    ext f
    simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]
  simp [Finset.card_erase_of_mem]

theorem sum_undiscovered (n k : ℕ) :
    ∑ f : Fin k → Fin n, undiscovered f = n * (n - 1) ^ k := by
  unfold undiscovered
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  simp_rw [← Finset.card_filter, card_avoiding]
  simp

theorem expected_undiscovered (n k : ℕ) (hn : 1 ≤ n) :
    (∑ f : Fin k → Fin n, (undiscovered f : ℝ)) / (Fintype.card (Fin k → Fin n) : ℝ)
      = n * (1 - 1 / (n : ℝ)) ^ k := by
  have hsum : (∑ f : Fin k → Fin n, (undiscovered f : ℝ)) = ((n * (n - 1) ^ k : ℕ) : ℝ) := by
    rw [← sum_undiscovered]; push_cast; rfl
  rw [hsum]
  simp only [Fintype.card_fun, Fintype.card_fin]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hn, Nat.cast_one]
  rw [one_sub_div hn0, div_pow, mul_div_assoc]
