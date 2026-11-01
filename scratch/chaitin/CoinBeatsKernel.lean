import Mathlib

/-!
# Coins diagonalize against every short description at once

A description language is any decoder from short bit strings (length below `n − k`) to `n`-bit strings.

PROVED:
* `short_descriptions_card`: there are exactly `2^(n−k) − 1` bit strings shorter than `n − k`.
* `few_compressible`: so any decoder hits fewer than `2^(n−k)` of the `2^n` strings of length `n`; at most a
  `2^(−k)` fraction of `n`-bit strings can be compressed by `k` or more bits, whatever the decoder.
* `incompressible_exists`: some `n`-bit string has no description shorter than `n` (take `k = 0`).
INTERPRETED (not formalized): flipping `n` coins produces, with probability above `1 − 2^(−k)`, a string that no
description shorter than `n − k` produces. By Chaitin's incompleteness theorem a fixed proof system can certify
incompressibility only up to a constant depending on the system, so coins beat the kernel in what is true with
high probability, not in what is provable.
-/

namespace CoinBeatsKernel

abbrev Short (m : ℕ) := Σ j : Fin m, (Fin j → Bool)

theorem short_descriptions_card (m : ℕ) : Fintype.card (Short m) = 2 ^ m - 1 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun j => 2 ^ j) m, Nat.geomSum_eq (le_refl 2)]
  simp

theorem few_compressible (n k : ℕ) (dec : Short (n - k) → (Fin n → Bool)) :
    (Finset.univ.image dec).card < 2 ^ (n - k) := by
  calc (Finset.univ.image dec).card ≤ Fintype.card (Short (n - k)) := Finset.card_image_le
    _ = 2 ^ (n - k) - 1 := short_descriptions_card _
    _ < 2 ^ (n - k) := Nat.sub_lt (pow_pos (by norm_num) _) (by norm_num)

theorem few_compressible_fraction (n k : ℕ) (hk : k ≤ n) (dec : Short (n - k) → (Fin n → Bool)) :
    (Finset.univ.image dec).card * 2 ^ k < 2 ^ n := by
  have h := few_compressible n k dec
  calc (Finset.univ.image dec).card * 2 ^ k < 2 ^ (n - k) * 2 ^ k :=
        Nat.mul_lt_mul_of_pos_right h (pow_pos (by norm_num) _)
    _ = 2 ^ n := by rw [← pow_add, Nat.sub_add_cancel hk]

theorem incompressible_exists (n : ℕ) (dec : Short n → (Fin n → Bool)) : ∃ x, ∀ d, dec d ≠ x := by
  have hlt : (Finset.univ.image dec).card < (Finset.univ : Finset (Fin n → Bool)).card := by
    calc (Finset.univ.image dec).card ≤ Fintype.card (Short n) := Finset.card_image_le
      _ = 2 ^ n - 1 := short_descriptions_card n
      _ < 2 ^ n := Nat.sub_lt (pow_pos (by norm_num) _) (by norm_num)
      _ = (Finset.univ : Finset (Fin n → Bool)).card := by simp
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨x, fun d hd => hx (Finset.mem_image.mpr ⟨d, Finset.mem_univ d, hd⟩)⟩

end CoinBeatsKernel
