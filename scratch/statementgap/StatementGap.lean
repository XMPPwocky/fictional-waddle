/-
# The statement gap

A proof checker reads text. Whether a formal statement means what its author intended depends on
an interpretation the checker never receives. This file proves three precise versions of that.

PROVED
1. `no_sound_faithfulness_certifier`: a certifier that sees only the statement and the proof, and is
   sound for faithfulness under every interpretation, certifies nothing.
2. `faithfulness_undecidable`: when statements are programs and the intent is a partial recursive
   function, "this program computes exactly the intended function" is not a computable predicate
   (Rice's theorem, from Mathlib).
3. `finite_agreement_not_faithful` and `disagreement_refutes`: agreement with the intent on any finite
   set of test inputs never implies faithfulness, while a single disagreement refutes it.

INTERPRETED (not formalized)
- Lean statements are not literally programs, and an author's intent is not literally a function.
  Item 2 is the clean special case; items 1 and 3 do not need that identification.
- Item 3 is why theorem fuzzing can find unfaithful statements but cannot certify faithful ones.
-/

import Mathlib

namespace StatementGap

/-! ## 1. A syntax-only certifier cannot be sound for meaning -/

/-- Suppose `certify` sees only a statement and a proof, and its approval guarantees that the
statement matches the intent under every interpretation `I`. Then it never approves anything. -/
theorem no_sound_faithfulness_certifier {Stmt Pf : Type} (certify : Stmt → Pf → Bool)
    (intent : Prop)
    (hsound : ∀ (I : Stmt → Prop) (s : Stmt) (p : Pf), certify s p = true → (I s ↔ intent)) :
    ∀ s p, certify s p = false := by
  intro s p
  by_contra h
  have h' : certify s p = true := by simpa using h
  have := hsound (fun _ => ¬ intent) s p h'
  by_cases hi : intent
  · exact (this.mpr hi) hi
  · exact hi (this.mp hi)

/-- The certifier is not at fault: the same statement is faithful under one interpretation and
unfaithful under another, and nothing the certifier reads distinguishes the two. -/
theorem interpretations_disagree {Stmt : Type} (intent : Prop) (s : Stmt) :
    ∃ I I' : Stmt → Prop, (I s ↔ intent) ∧ ¬ (I' s ↔ intent) := by
  refine ⟨fun _ => intent, fun _ => ¬ intent, Iff.rfl, ?_⟩
  intro h
  by_cases hi : intent
  · exact (h.mpr hi) hi
  · exact hi (h.mp hi)

/-! ## 2. Rice: extensional faithfulness is undecidable -/

open Nat.Partrec in
/-- For any partial recursive intended function `f`, there is no computable test of whether a
program code computes exactly `f`. -/
theorem faithfulness_undecidable (f : ℕ →. ℕ) (hf : Nat.Partrec f) :
    ¬ ComputablePred (fun c : Code => Code.eval c = f) := by
  intro h
  have h' : ComputablePred (fun c : Code => Code.eval c ∈ ({f} : Set (ℕ →. ℕ))) := by
    simpa [Set.mem_singleton_iff] using h
  have h0 : (pure 0 : ℕ →. ℕ) ∈ ({f} : Set (ℕ →. ℕ)) :=
    ComputablePred.rice {f} h' hf Nat.Partrec.zero rfl
  have h1 : (fun _ => Part.none : ℕ →. ℕ) ∈ ({f} : Set (ℕ →. ℕ)) :=
    ComputablePred.rice {f} h' hf Nat.Partrec.none rfl
  have h1' : (fun _ => Part.none : ℕ →. ℕ) = f := h1
  have h0' : (pure 0 : ℕ →. ℕ) = f := h0
  have e := congrFun (h0'.trans h1'.symm) 0
  have hm : (0 : ℕ) ∈ (pure 0 : ℕ →. ℕ) 0 := Part.mem_some 0
  rw [e] at hm
  exact Part.notMem_none 0 hm

/-! ## 3. Testing refutes but never certifies -/

/-- Agreeing with `f` on every input in a finite test set `S` does not make a function equal to
`f`: some function passes every test and still differs from `f`. -/
theorem finite_agreement_not_faithful (f : ℕ → ℕ) (S : Finset ℕ) :
    ∃ g : ℕ → ℕ, (∀ n ∈ S, g n = f n) ∧ g ≠ f := by
  obtain ⟨m, hm⟩ := Infinite.exists_notMem_finset S
  refine ⟨Function.update f m (f m + 1), ?_, ?_⟩
  · intro n hn
    have hne : n ≠ m := fun h => hm (h ▸ hn)
    simp [Function.update, hne]
  · intro h
    have := congrFun h m
    simp at this

/-- One input where `g` and `f` differ shows `g ≠ f`. -/
theorem disagreement_refutes (f g : ℕ → ℕ) (n : ℕ) (h : g n ≠ f n) : g ≠ f :=
  fun e => h (congrFun e n)

end StatementGap

#print axioms StatementGap.no_sound_faithfulness_certifier
#print axioms StatementGap.interpretations_disagree
#print axioms StatementGap.faithfulness_undecidable
#print axioms StatementGap.finite_agreement_not_faithful
#print axioms StatementGap.disagreement_refutes
