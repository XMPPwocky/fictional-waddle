/-
# One bit survives every even scrambling, and it counts reorderings of unrelated events

PROVED
1. `sign_survives_even`: composing with any even permutation leaves the sign unchanged.
2. `sign_is_one_bit`: the sign is 1 or −1.
3. `sign_eq_inversion_parity`: the sign of σ on Fin n is (−1) raised to the number of inversions,
   pairs (a, b) with b < a whose images are in the opposite order.
4. `inversions_are_unrelated`: let events be numbered by one observer's order, and let σ give their
   positions in a second observer's order. If both orders respect a relation `causal` (whenever
   causal a b, a comes first for both observers), then every inverted pair is causally unrelated in
   both directions.
5. `total_causal_order_sign_one`: if every two distinct events are causally related, there are no
   inversions, so the sign is 1: observers who must agree on all causal pairs agree on the parity.

CITED
- The alternating group is (N − 2)-transitive, so no other invariant of the permutation survives
  composition with unknown even permutations.

INTERPRETED (not formalized)
- With causal = "can influence" (a light-cone relation), item 4 says the one bit that survives even
  scrambling is the parity of how many non-causally-related pairs the two observers order differently.
-/

import Mathlib

namespace SignAndCausalOrder

open Equiv Equiv.Perm Finset

theorem sign_survives_even {α : Type*} [DecidableEq α] [Fintype α] (σ τ : Perm α)
    (hτ : τ ∈ alternatingGroup α) : sign (τ * σ) = sign σ := by
  rw [Perm.sign_mul, (mem_alternatingGroup).mp hτ, one_mul]

theorem sign_is_one_bit {α : Type*} [DecidableEq α] [Fintype α] (σ : Perm α) :
    sign σ = 1 ∨ sign σ = -1 :=
  Int.units_eq_one_or (sign σ)

theorem sign_eq_signAux {n : ℕ} (σ : Perm (Fin n)) : sign σ = signAux σ := by
  refine Perm.swap_induction_on σ (by simp) ?_
  intro f x y hxy ih
  rw [Perm.sign_mul, signAux_mul, sign_swap hxy, signAux_swap hxy, ih]

/-- Inverted pairs: (a, b) with b < a and σ a ≤ σ b. -/
def inversions {n : ℕ} (σ : Perm (Fin n)) : Finset (Σ _ : Fin n, Fin n) :=
  (finPairsLT n).filter fun x => σ x.1 ≤ σ x.2

theorem sign_eq_inversion_parity {n : ℕ} (σ : Perm (Fin n)) :
    sign σ = (-1) ^ (inversions σ).card := by
  rw [sign_eq_signAux, signAux, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const]
  rfl

theorem inversions_are_unrelated {n : ℕ} (σ : Perm (Fin n)) (causal : Fin n → Fin n → Prop)
    (h1 : ∀ a b, causal a b → a < b) (h2 : ∀ a b, causal a b → σ a < σ b)
    (x : Σ _ : Fin n, Fin n) (hx : x ∈ inversions σ) : ¬ causal x.1 x.2 ∧ ¬ causal x.2 x.1 := by
  simp only [inversions, Finset.mem_filter, mem_finPairsLT] at hx
  refine ⟨fun h => absurd (h1 _ _ h) (not_lt.mpr hx.1.le), fun h => absurd (h2 _ _ h) (not_lt.mpr hx.2)⟩

theorem total_causal_order_sign_one {n : ℕ} (σ : Perm (Fin n)) (causal : Fin n → Fin n → Prop)
    (h1 : ∀ a b, causal a b → a < b) (h2 : ∀ a b, causal a b → σ a < σ b)
    (htotal : ∀ a b, a ≠ b → causal a b ∨ causal b a) : sign σ = 1 := by
  have hempty : inversions σ = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    have hne : x.1 ≠ x.2 := by
      have := hx
      simp only [inversions, Finset.mem_filter, mem_finPairsLT] at this
      exact ne_of_gt this.1
    obtain ⟨hn1, hn2⟩ := inversions_are_unrelated σ causal h1 h2 x hx
    rcases htotal x.1 x.2 hne with h | h
    · exact hn1 h
    · exact hn2 h
  rw [sign_eq_inversion_parity, hempty, Finset.card_empty, pow_zero]

end SignAndCausalOrder

#print axioms SignAndCausalOrder.sign_survives_even
#print axioms SignAndCausalOrder.sign_is_one_bit
#print axioms SignAndCausalOrder.sign_eq_inversion_parity
#print axioms SignAndCausalOrder.inversions_are_unrelated
#print axioms SignAndCausalOrder.total_causal_order_sign_one
