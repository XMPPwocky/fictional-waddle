import Mathlib

/-!
# Kraft inequality for prefix-free binary codes

PROVED
* `KraftInequalityPrefixFree.PrefixFree` (definition): `S : Set (List Bool)` is prefix-free if
  for all `w, w' ∈ S`, `w <+: w'` implies `w = w'`.
* `KraftInequalityPrefixFree.prefixFree_iff_isPrefixFree`: this definition coincides with
  Mathlib's `InformationTheory.IsPrefixFree`.
* `KraftInequalityPrefixFree.weight_eq`: `(2:ℝ)^(-(n:ℤ)) = (1/2)^n`.
* `KraftInequalityPrefixFree.kraft_finset`: for every prefix-free `S : Finset (List Bool)`,
  `∑ w ∈ S, (2:ℝ)^(-(w.length:ℤ)) ≤ 1`.
* `KraftInequalityPrefixFree.kraft_summable`: for every prefix-free `S : Set (List Bool)`,
  the family `w : S ↦ (2:ℝ)^(-(w.length:ℤ))` is summable.
* `KraftInequalityPrefixFree.kraft_tsum`: for every prefix-free `S : Set (List Bool)`,
  `∑' w : S, (2:ℝ)^(-(w.length:ℤ)) ≤ 1`.
* `KraftInequalityPrefixFree.kraft_set`: the conjunction of the two previous statements.

The finite and infinite bounds are obtained from Mathlib's
`InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one`,
`InformationTheory.IsPrefixFree.summable_one_div_card_pow_length` and
`InformationTheory.IsPrefixFree.tsum_one_div_card_pow_length_le_one` (alphabet `Bool`, card 2).

INTERPRETED (not formalized)
* "The measure `2^(-|program|)` over a prefix-free set of programs is normalizable" is read as
  `kraft_set`: the total mass is a finite sum (summable) of value at most 1.
-/

namespace KraftInequalityPrefixFree

/-- A set of binary words is prefix-free if no word is a proper prefix of another member. -/
def PrefixFree (S : Set (List Bool)) : Prop :=
  ∀ w ∈ S, ∀ w' ∈ S, w <+: w' → w = w'

theorem prefixFree_iff_isPrefixFree (S : Set (List Bool)) :
    PrefixFree S ↔ InformationTheory.IsPrefixFree S :=
  Iff.rfl

theorem weight_eq (n : ℕ) : (2 : ℝ) ^ (-(n : ℤ)) = (1 / (Fintype.card Bool : ℝ)) ^ n := by
  rw [zpow_neg, zpow_natCast, Fintype.card_bool, one_div, inv_pow]
  norm_num

/-- Kraft inequality, finite case. -/
theorem kraft_finset (S : Finset (List Bool)) (hS : PrefixFree (S : Set (List Bool))) :
    ∑ w ∈ S, (2 : ℝ) ^ (-(w.length : ℤ)) ≤ 1 := by
  simp_rw [weight_eq]
  exact InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one hS

/-- Kraft inequality, infinite case: summability. -/
theorem kraft_summable (S : Set (List Bool)) (hS : PrefixFree S) :
    Summable (fun w : S => (2 : ℝ) ^ (-((w : List Bool).length : ℤ))) := by
  simp_rw [weight_eq]
  exact InformationTheory.IsPrefixFree.summable_one_div_card_pow_length hS

/-- Kraft inequality, infinite case: the total mass is at most one. -/
theorem kraft_tsum (S : Set (List Bool)) (hS : PrefixFree S) :
    ∑' w : S, (2 : ℝ) ^ (-((w : List Bool).length : ℤ)) ≤ 1 := by
  simp_rw [weight_eq]
  exact InformationTheory.IsPrefixFree.tsum_one_div_card_pow_length_le_one hS

/-- Kraft inequality, infinite case: summable with sum at most one. -/
theorem kraft_set (S : Set (List Bool)) (hS : PrefixFree S) :
    Summable (fun w : S => (2 : ℝ) ^ (-((w : List Bool).length : ℤ))) ∧
      ∑' w : S, (2 : ℝ) ^ (-((w : List Bool).length : ℤ)) ≤ 1 :=
  ⟨kraft_summable S hS, kraft_tsum S hS⟩

end KraftInequalityPrefixFree
