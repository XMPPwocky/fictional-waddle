/-
# Fridge logic is consistent, if the fridge decides everything

A fast checker reads claims during the show; a slow checker reads them later, at the fridge. The
fridge set is what passed the fast check and failed the slow one. `neg` sends a claim to its
negation; a set is consistent if it never holds a claim together with its negation.

PROVED
1. `fridge_consistent`: if the slow checker is complete (it accepts each claim or its negation),
   the fridge set is consistent.
2. `incomplete_fridge_inconsistent`: without completeness it can fail: a slow checker that rejects
   everything puts both a claim and its negation in the fridge.
3. `empty_fridge_consistent`: the empty set is consistent.
4. `trusting_fridge_is_empty`: a slow checker that accepts everything leaves the fridge empty.

CITED, NOT PROVED HERE
- Gödel's first incompleteness theorem: no consistent, effectively axiomatized checker strong
  enough for arithmetic is complete. So item 1's hypothesis is out of reach for any fridge that can
  do arithmetic.
- Gödel's second: such a checker cannot prove its own consistency.
-/

import Mathlib

namespace FridgeLogic

variable {C : Type*}

def fridge (fast slow : C → Bool) : Set C := {c | fast c = true ∧ slow c = false}

def Consistent (neg : C → C) (A : Set C) : Prop := ∀ c, ¬ (c ∈ A ∧ neg c ∈ A)

theorem fridge_consistent (fast slow : C → Bool) (neg : C → C)
    (hcomplete : ∀ c, slow c = true ∨ slow (neg c) = true) :
    Consistent neg (fridge fast slow) := by
  rintro c ⟨h1, h2⟩
  simp only [fridge, Set.mem_setOf_eq] at h1 h2
  rcases hcomplete c with h | h
  · rw [h1.2] at h; exact Bool.false_ne_true h
  · rw [h2.2] at h; exact Bool.false_ne_true h

theorem incomplete_fridge_inconsistent :
    ¬ Consistent not (fridge (C := Bool) (fun _ => true) (fun _ => false)) := by
  intro h
  exact h true ⟨by simp [fridge], by simp [fridge]⟩

theorem empty_fridge_consistent (neg : C → C) : Consistent neg (∅ : Set C) := by
  rintro c ⟨h, _⟩
  exact h

theorem trusting_fridge_is_empty (fast : C → Bool) : fridge fast (fun _ => true) = ∅ := by
  ext c
  simp [fridge]

end FridgeLogic

#print axioms FridgeLogic.fridge_consistent
#print axioms FridgeLogic.incomplete_fridge_inconsistent
#print axioms FridgeLogic.empty_fridge_consistent
#print axioms FridgeLogic.trusting_fridge_is_empty
