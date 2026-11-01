/-
# Cut-and-choose auditing

A prover builds n objects (for example garbled circuits), t of them bad. The verifier opens a uniformly
random subset of size k and checks those; the cheat escapes if no opened object is bad.

PROVED
1. `escape_count`: the number of size-k subsets avoiding a fixed set of t objects is C(n − t, k).
2. `escape_one_bad`: with one bad object among m + 1, the escaping subsets are a fraction
   (m + 1 − k)/(m + 1) of all size-k subsets: C(m, k) · (m + 1) = C(m + 1, k) · (m + 1 − k).
3. `escape_half`: opening half of 2 objects with one bad one, the cheat escapes in exactly 1 of the 2
   subsets.

CITED
- Cut-and-choose in secure two-party computation (Yao's garbled circuits, Lindell–Pinkas 2007): opening
  a random subset and evaluating the rest bounds a cheating prover's success probability.
-/

import Mathlib

namespace CutAndChooseAudit

open Finset

theorem escape_count (n k : ℕ) (T : Finset (Fin n)) :
    ((univ : Finset (Fin n)).powersetCard k |>.filter fun S => Disjoint S T).card =
      Nat.choose (n - T.card) k := by
  have h : ((univ : Finset (Fin n)).powersetCard k |>.filter fun S => Disjoint S T) =
      Tᶜ.powersetCard k := by
    ext S
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
    constructor
    · rintro ⟨hc, hd⟩
      exact ⟨le_compl_iff_disjoint_right.mpr hd, hc⟩
    · rintro ⟨hs, hc⟩
      exact ⟨hc, le_compl_iff_disjoint_right.mp hs⟩
  rw [h, card_powersetCard, card_compl, Fintype.card_fin]

theorem escape_one_bad (m k : ℕ) : Nat.choose m k * (m + 1) = Nat.choose (m + 1) k * (m + 1 - k) :=
  Nat.choose_mul_succ_eq m k

theorem escape_half :
    ((univ : Finset (Fin 2)).powersetCard 1 |>.filter fun S => Disjoint S {0}).card = 1 ∧
      ((univ : Finset (Fin 2)).powersetCard 1).card = 2 := by
  constructor
  · rw [escape_count]; rfl
  · rw [card_powersetCard]; rfl

end CutAndChooseAudit

#print axioms CutAndChooseAudit.escape_count
#print axioms CutAndChooseAudit.escape_one_bad
#print axioms CutAndChooseAudit.escape_half
