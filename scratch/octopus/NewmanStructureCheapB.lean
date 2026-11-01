import Mathlib

/-!
# Newman's objection to pure structuralism

PROVED.
* `transport_iff`: for `e : X ≃ Y` and `R : Y → Y → Prop`, the transported relation
  `transport e R x₁ x₂ := R (e x₁) (e x₂)` satisfies
  `∀ x₁ x₂, transport e R x₁ x₂ ↔ R (e x₁) (e x₂)`.
* `transportRelIso`: the same `e` is a relation isomorphism `transport e R ≃r R`.
* `exists_relIso_of_card_eq`: for finite `X`, `Y` with `Fintype.card X = Fintype.card Y`,
  every relation `R` on `Y` is realized up to isomorphism by some relation on `X`.
* `card_eq_of_relIso`: conversely, a relation isomorphism between relations on finite types
  forces equal cardinalities.
* `exists_relIso_iff_card_eq`: for finite `X`, `Y` and any `R` on `Y`,
  `(∃ R' on X, Nonempty (R' ≃r R)) ↔ Fintype.card X = Fintype.card Y`.
  The structural claim "the domain carries a relation isomorphic to `R`" is equivalent to a
  cardinality claim.
* `card_rel`: on a finite type with `n` elements there are `2 ^ (n ^ 2)` binary relations
  `X → X → Prop`.
* `card_relBool`: the same count for `Bool`-valued relations.
* `isoClass_meets_every_set`: for `R` on `Fin n` and every finite `X` with `n` elements,
  the isomorphism class of `R` contains a relation on `X`.
* `newman`: packaged statement: the relation count is `2 ^ (n ^ 2)`, and for each of these
  relations `R` on `Fin n`, every `n`-element type carries a relation isomorphic to `R`.

INTERPRETED (docstring only, not formalized).
Knowing only that the world has some relation of a given shape conveys no more than the size
of the domain. What makes structural knowledge non-trivial is knowing which of the
`2 ^ (n ^ 2)` relations is the real one, which is grounding.
-/

namespace NewmanStructureCheapB

/-- The relation on `X` obtained by pulling back `R` along `e`. -/
def transport {X Y : Type*} (e : X ≃ Y) (R : Y → Y → Prop) : X → X → Prop :=
  fun x₁ x₂ => R (e x₁) (e x₂)

theorem transport_iff {X Y : Type*} (e : X ≃ Y) (R : Y → Y → Prop) :
    ∀ x₁ x₂, transport e R x₁ x₂ ↔ R (e x₁) (e x₂) :=
  fun _ _ => Iff.rfl

/-- `e` is an isomorphism of relational structures `(X, transport e R) ≃ (Y, R)`. -/
def transportRelIso {X Y : Type*} (e : X ≃ Y) (R : Y → Y → Prop) :
    transport e R ≃r R where
  toEquiv := e
  map_rel_iff' := Iff.rfl

theorem transportRelIso_apply {X Y : Type*} (e : X ≃ Y) (R : Y → Y → Prop) (x : X) :
    transportRelIso e R x = e x := rfl

theorem exists_relIso_of_card_eq {X Y : Type*} [Fintype X] [Fintype Y]
    (h : Fintype.card X = Fintype.card Y) (R : Y → Y → Prop) :
    ∃ R' : X → X → Prop, Nonempty (R' ≃r R) := by
  classical
  exact ⟨transport (Fintype.equivOfCardEq h) R,
    ⟨transportRelIso (Fintype.equivOfCardEq h) R⟩⟩

theorem card_eq_of_relIso {X Y : Type*} [Fintype X] [Fintype Y]
    {R' : X → X → Prop} {R : Y → Y → Prop} (f : R' ≃r R) :
    Fintype.card X = Fintype.card Y :=
  Fintype.card_congr f.toEquiv

theorem exists_relIso_iff_card_eq {X Y : Type*} [Fintype X] [Fintype Y]
    (R : Y → Y → Prop) :
    (∃ R' : X → X → Prop, Nonempty (R' ≃r R)) ↔ Fintype.card X = Fintype.card Y := by
  constructor
  · rintro ⟨R', ⟨f⟩⟩
    exact card_eq_of_relIso f
  · intro h
    exact exists_relIso_of_card_eq h R

theorem card_rel (X : Type*) [Fintype X] [DecidableEq X] :
    Fintype.card (X → X → Prop) = 2 ^ (Fintype.card X ^ 2) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_prop, ← pow_mul, sq]

theorem card_relBool (X : Type*) [Fintype X] [DecidableEq X] :
    Fintype.card (X → X → Bool) = 2 ^ (Fintype.card X ^ 2) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, ← pow_mul, sq]

theorem isoClass_meets_every_set (n : ℕ) (R : Fin n → Fin n → Prop)
    (X : Type*) [Fintype X] (hX : Fintype.card X = n) :
    ∃ R' : X → X → Prop, Nonempty (R' ≃r R) :=
  exists_relIso_of_card_eq (by rw [hX, Fintype.card_fin]) R

theorem newman (n : ℕ) :
    Fintype.card (Fin n → Fin n → Prop) = 2 ^ (n ^ 2) ∧
    ∀ R : Fin n → Fin n → Prop, ∀ (X : Type) [Fintype X], Fintype.card X = n →
      ∃ R' : X → X → Prop, Nonempty (R' ≃r R) := by
  refine ⟨?_, fun R X _ hX => isoClass_meets_every_set n R X hX⟩
  rw [card_rel, Fintype.card_fin]

end NewmanStructureCheapB
