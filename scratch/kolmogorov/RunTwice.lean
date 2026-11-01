/-
# Almost no history is one program run twice, and almost none is compressible

Histories are bit strings. A description is a shorter bit string, read by any fixed decoder.

PROVED
1. `squares_card`: of the 4^n bit strings of length 2n, exactly 2^n are "one half run twice"
   (the second half equals the first), a fraction 2^(−n).
2. `short_descriptions_card`: there are exactly 2^k − 1 bit strings of length less than k.
3. `few_compressible`: so for ANY decoder, at most 2^k − 1 strings have a description shorter than
   k bits. Among the 2^n strings of length n, at most a fraction 2^(−c) can be compressed by c bits.

INTERPRETED (not formalized)
- Almost every history is incompressible: its shortest description is itself (item 3), and almost
  none is a repetition (item 1). A history whose two halves are algorithmically independent costs the
  sum of the two halves' complexities: two programs run once, not one program run twice. One program
  run twice is the case of total dependence, where the second half adds nothing.
-/

import Mathlib

namespace RunTwice

open Finset

/-- The doubling map: a string of length n written twice. -/
def double {n : ℕ} (w : Fin n → Bool) : Fin (n + n) → Bool := Fin.append w w

theorem double_injective (n : ℕ) : Function.Injective (double (n := n)) := by
  intro w w' h
  funext i
  have := congrFun h (Fin.castAdd n i)
  simpa [double, Fin.append_left] using this

theorem squares_card (n : ℕ) :
    (univ.image (double (n := n))).card = 2 ^ n ∧ Fintype.card (Fin (n + n) → Bool) = 4 ^ n := by
  constructor
  · rw [card_image_of_injective _ (double_injective n), card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  · rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← two_mul, pow_mul]
    norm_num

/-- All bit strings of length less than k, as a finite type. -/
abbrev Short (k : ℕ) := Σ l : Fin k, (Fin l → Bool)

theorem short_descriptions_card (k : ℕ) : Fintype.card (Short k) = 2 ^ k - 1 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun l => 2 ^ l) k, Nat.geomSum_eq (le_refl 2)]
  simp

theorem few_compressible {X : Type*} [DecidableEq X] (k : ℕ) (decode : Short k → X) :
    (univ.image decode).card ≤ 2 ^ k - 1 := by
  calc (univ.image decode).card ≤ (univ : Finset (Short k)).card := card_image_le
    _ = 2 ^ k - 1 := by rw [card_univ, short_descriptions_card]

end RunTwice

#print axioms RunTwice.double_injective
#print axioms RunTwice.squares_card
#print axioms RunTwice.short_descriptions_card
#print axioms RunTwice.few_compressible
