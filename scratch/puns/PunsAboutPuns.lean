import Mathlib

/-!
# Provable puns about provable puns

A pun is one expression with two readings. A provable pun is one formal object that serves both readings.

PROVED:
* `pun_iff_not_injective`: a naming of meanings by words has a pun (a word with two meanings) iff it is not
  injective. With more meanings than words (the dad-joke theorem in `Puns.lean`) puns are unavoidable.
* `same_term_proves_and_runs`: Curry–Howard as a pun. The one term `@id` is a proof that `P` implies `P` and a
  program that returns its input; Lean checks both readings of the same constant.
* `no_pun_becomes_identity`: in Lean a pun stays a pun. There are two different equivalences from `Bool` to itself,
  but at most one proof that `Bool = Bool`, so no injective map turns equivalences into equalities. Univalence,
  which would make every equivalence an identity, contradicts Lean's proof irrelevance.
-/

namespace PunsAboutPuns

theorem pun_iff_not_injective {Meaning Word : Type*} (name : Meaning → Word) :
    (∃ m₁ m₂, m₁ ≠ m₂ ∧ name m₁ = name m₂) ↔ ¬ Function.Injective name := by
  constructor
  · rintro ⟨m₁, m₂, hne, heq⟩ hinj
    exact hne (hinj heq)
  · intro h
    simp only [Function.Injective, not_forall] at h
    obtain ⟨m₁, m₂, heq, hne⟩ := h
    exact ⟨m₁, m₂, hne, heq⟩

theorem same_term_proves_and_runs :
    (∀ P : Prop, P → P) ∧ (∀ (α : Type) (a : α), @id α a = a) :=
  ⟨fun P => @id P, fun _ _ => rfl⟩

theorem no_pun_becomes_identity : ¬ ∃ f : (Bool ≃ Bool) → (Bool = Bool), Function.Injective f := by
  rintro ⟨f, hf⟩
  have h : (Equiv.refl Bool) = (Equiv.ofBijective not ⟨fun a b h => by simpa using h,
      fun b => ⟨!b, by simp⟩⟩) := hf (Subsingleton.elim _ _)
  have := congrArg (fun e : Bool ≃ Bool => e true) h
  simp only [Equiv.refl_apply, Equiv.ofBijective_apply, Bool.not_true] at this
  exact Bool.noConfusion this

end PunsAboutPuns
