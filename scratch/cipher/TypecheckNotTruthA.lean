import Mathlib

/-!
# Typechecking is a precondition, not evidence

A tiny typed language of sentences `feel a b` over four nouns: two things
(`x0`, `x1`) and two algebras (`e`, `s`). The checker accepts `feel a b`
exactly when `a` is a thing and `b` is an algebra. The model is the
symmetric group `Equiv.Perm (Fin 2)` acting on `Fin 2`: `x0 ↦ 0`, `x1 ↦ 1`,
`e ↦ 1` (identity permutation), `s ↦ Equiv.swap 0 1`. A well-typed sentence
`feel a b` means "the permutation denoted by `b` fixes the point denoted by
`a`"; an ill-typed sentence means `False`.

## PROVED

* `check_feel_x0_e`, `check_feel_x0_s`: `feel x0 e` and `feel x0 s` both
  typecheck.
* `meaning_feel_x0_e`: `meaning (feel x0 e)` holds.
* `not_meaning_feel_x0_s`: `meaning (feel x0 s)` fails.
* `welltyped_true_and_false`: there exist sentences `σ τ` with
  `check σ = true`, `check τ = true`, `meaning σ`, `¬ meaning τ`.
* `no_verdict_decider_general`: for any type `S`, any `chk : S → Bool`,
  any `mean : S → Prop`, if there are `σ τ` with `chk σ = true`,
  `chk τ = true`, `mean σ`, `¬ mean τ`, then there is no
  `d : Bool → Prop` with `∀ x, chk x = true → (d (chk x) ↔ mean x)`.
  Its hypotheses are instantiated by this language (`no_verdict_decider`).
* `no_verdict_decider`: there is no `d : Bool → Prop` with
  `∀ σ, check σ = true → (d (check σ) ↔ meaning σ)`.
* `no_verdict_decider_any`: stronger form, there is no `d : Bool → Prop`
  with `∀ σ, d (check σ) ↔ meaning σ` either (this follows from the
  previous one by restriction).
* `check_feel_e_x0`: `check (feel e x0) = false` (an ill-typed sentence).
* `check_nontrivial`: there exist `σ τ` with `check σ = true` and
  `check τ = false`.
* `meaning_implies_check`: `meaning σ → check σ = true` (typechecking is a
  precondition of truth in this semantics).
* `check_not_implies_meaning`: `¬ ∀ σ, check σ = true → meaning σ`.
* `prop_iff_nonempty_plift`: for every `p : Prop`, `p ↔ Nonempty (PLift p)`.
* `prop_iff_nonempty`: for every `p : Prop`, `p ↔ Nonempty p`.
* `true_false_opposite`: `True ∧ ¬ False`, where `True False : Prop`.
* `prop_type_not_evidence`: `¬ ∀ p : Prop, p` and `¬ ∀ p : Prop, ¬ p`;
  i.e. being of type `Prop` decides neither truth nor falsity.
* `prop_no_decider_from_type`: there is no `d : Prop` with
  `∀ p : Prop, d ↔ p` (a single verdict shared by all well-formed
  propositions cannot track their truth).

## CITED / INTERPRETED (not proved)

* Curry-Howard reading: a proposition `p : Prop` is a type, and a proof of
  `p` is an inhabitant; `p ↔ Nonempty (PLift p)` is the Lean-internal form
  of "p is true iff its type is inhabited". The statement `p : Prop` itself
  is a typing judgment, which every proposition, true or false, passes.
* The reading "a typechecker is a precondition, not evidence" is an
  interpretation of `meaning_implies_check` together with
  `no_verdict_decider`: in this semantics truth requires typing, but the
  typing verdict alone does not determine truth.
-/

namespace TypecheckNotTruthA

/-- Nouns: two things and two algebras. -/
inductive Noun
  | x0 | x1 | e | s
  deriving DecidableEq, Repr

/-- Sentences: `feel subject object`. -/
inductive Sentence
  | feel : Noun → Noun → Sentence
  deriving DecidableEq, Repr

open Noun Sentence

/-- Sort predicate: is the noun a thing. -/
def isThing : Noun → Bool
  | x0 => true
  | x1 => true
  | _ => false

/-- Sort predicate: is the noun an algebra. -/
def isAlgebra : Noun → Bool
  | e => true
  | s => true
  | _ => false

/-- Type checker: subject must be a thing, object an algebra. -/
def check : Sentence → Bool
  | feel a b => isThing a && isAlgebra b

/-- Denotation of things as points of `Fin 2` (junk value off-sort). -/
def thingVal : Noun → Fin 2
  | x1 => 1
  | _ => 0

/-- Denotation of algebras as elements of `Equiv.Perm (Fin 2)`
(junk value off-sort). -/
def algVal : Noun → Equiv.Perm (Fin 2)
  | s => Equiv.swap 0 1
  | _ => 1

/-- Semantics: a well-typed `feel a b` means `algVal b` fixes `thingVal a`;
an ill-typed sentence means `False`. -/
def meaning : Sentence → Prop
  | feel a b => check (feel a b) = true ∧ algVal b (thingVal a) = thingVal a

theorem check_feel_x0_e : check (feel x0 e) = true := by decide

theorem check_feel_x0_s : check (feel x0 s) = true := by decide

theorem meaning_feel_x0_e : meaning (feel x0 e) := by
  refine ⟨by decide, ?_⟩
  simp [algVal, thingVal]

theorem not_meaning_feel_x0_s : ¬ meaning (feel x0 s) := by
  rintro ⟨-, h⟩
  simp [algVal, thingVal] at h

theorem welltyped_true_and_false :
    ∃ σ τ : Sentence, check σ = true ∧ check τ = true ∧ meaning σ ∧ ¬ meaning τ :=
  ⟨feel x0 e, feel x0 s, check_feel_x0_e, check_feel_x0_s,
    meaning_feel_x0_e, not_meaning_feel_x0_s⟩

/-- General form: if two accepted inputs differ in meaning, no function of
the verdict alone agrees with meaning on accepted inputs. -/
theorem no_verdict_decider_general {S : Type*} (chk : S → Bool) (mean : S → Prop)
    (h : ∃ σ τ : S, chk σ = true ∧ chk τ = true ∧ mean σ ∧ ¬ mean τ) :
    ¬ ∃ d : Bool → Prop, ∀ x, chk x = true → (d (chk x) ↔ mean x) := by
  rintro ⟨d, hd⟩
  obtain ⟨σ, τ, hσ, hτ, mσ, mτ⟩ := h
  have h1 : d true := by simpa [hσ] using (hd σ hσ).mpr mσ
  have h2 : d (chk τ) := by simpa [hτ] using h1
  exact mτ ((hd τ hτ).mp h2)

theorem no_verdict_decider :
    ¬ ∃ d : Bool → Prop, ∀ σ, check σ = true → (d (check σ) ↔ meaning σ) :=
  no_verdict_decider_general check meaning welltyped_true_and_false

theorem no_verdict_decider_any :
    ¬ ∃ d : Bool → Prop, ∀ σ, (d (check σ) ↔ meaning σ) := by
  rintro ⟨d, hd⟩
  exact no_verdict_decider ⟨d, fun σ _ => hd σ⟩

theorem check_feel_e_x0 : check (feel e x0) = false := by decide

theorem check_nontrivial : ∃ σ τ : Sentence, check σ = true ∧ check τ = false :=
  ⟨feel x0 e, feel e x0, check_feel_x0_e, check_feel_e_x0⟩

theorem meaning_implies_check (σ : Sentence) (h : meaning σ) : check σ = true := by
  cases σ with
  | feel a b => exact h.1

/-- The hypothesis of `meaning_implies_check` is satisfiable. -/
example : meaning (feel x0 e) := meaning_feel_x0_e

theorem check_not_implies_meaning : ¬ ∀ σ, check σ = true → meaning σ :=
  fun h => not_meaning_feel_x0_s (h _ check_feel_x0_s)

theorem prop_iff_nonempty_plift (p : Prop) : p ↔ Nonempty (PLift p) :=
  ⟨fun hp => ⟨⟨hp⟩⟩, fun ⟨⟨hp⟩⟩ => hp⟩

theorem prop_iff_nonempty (p : Prop) : p ↔ Nonempty p :=
  nonempty_prop.symm

theorem true_false_opposite : (True : Prop) ∧ ¬ (False : Prop) :=
  ⟨trivial, id⟩

theorem prop_type_not_evidence : (¬ ∀ p : Prop, p) ∧ (¬ ∀ p : Prop, ¬ p) :=
  ⟨fun h => h False, fun h => h True trivial⟩

theorem prop_no_decider_from_type : ¬ ∃ d : Prop, ∀ p : Prop, d ↔ p := by
  rintro ⟨d, hd⟩
  exact ((hd False).mp ((hd True).mpr trivial))

end TypecheckNotTruthA

#print axioms TypecheckNotTruthA.check_feel_x0_e
#print axioms TypecheckNotTruthA.check_feel_x0_s
#print axioms TypecheckNotTruthA.meaning_feel_x0_e
#print axioms TypecheckNotTruthA.not_meaning_feel_x0_s
#print axioms TypecheckNotTruthA.welltyped_true_and_false
#print axioms TypecheckNotTruthA.no_verdict_decider_general
#print axioms TypecheckNotTruthA.no_verdict_decider
#print axioms TypecheckNotTruthA.no_verdict_decider_any
#print axioms TypecheckNotTruthA.check_feel_e_x0
#print axioms TypecheckNotTruthA.check_nontrivial
#print axioms TypecheckNotTruthA.meaning_implies_check
#print axioms TypecheckNotTruthA.check_not_implies_meaning
#print axioms TypecheckNotTruthA.prop_iff_nonempty_plift
#print axioms TypecheckNotTruthA.prop_iff_nonempty
#print axioms TypecheckNotTruthA.true_false_opposite
#print axioms TypecheckNotTruthA.prop_type_not_evidence
#print axioms TypecheckNotTruthA.prop_no_decider_from_type
