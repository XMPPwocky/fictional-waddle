import Mathlib

/-!
# Newman's objection to pure structuralism

PROVED
* `transport_iff`: for `e : X ≃ Y` and `R : Y → Y → Prop`, the transported relation
  `transport e R x₁ x₂ := R (e x₁) (e x₂)` satisfies
  `∀ x₁ x₂, transport e R x₁ x₂ ↔ R (e x₁) (e x₂)`.
* `transport_relIso`: `e` underlies a relation isomorphism `transport e R ≃r R`.
* `exists_relIso_of_card_eq`: for finite `X`, `Y` with `Fintype.card X = Fintype.card Y`,
  every relation `R` on `Y` is isomorphic to some relation on `X`.
* `exists_relIso_iff_card_eq`: for finite `X`, `Y`, the statement
  "`X` carries some relation isomorphic to `R`" holds iff `Fintype.card X = Fintype.card Y`;
  it carries no information beyond cardinality, whatever `R` is.
* `card_relations`: on a finite type with `n` elements there are `2 ^ (n ^ 2)` binary relations
  (`Nat.card (X → X → Prop) = 2 ^ (Fintype.card X ^ 2)`).
* `isoClass_nonempty_on_every_set`: for any `R` on an `n`-element type `Y` and any type `X`
  with `n` elements, the set of relations on `X` isomorphic to `R` is nonempty.

INTERPRETED
* Knowing only that the world has *some* relation of the shape of `R` rules out almost nothing:
  among the `2 ^ (n ^ 2)` relations on an `n`-element domain, the existence claim is satisfied
  by every domain of size `n`, so the only content of the claim is the cardinality `n`.
  What makes structural knowledge non-trivial is knowing which relation on the domain is the
  real one, i.e. grounding.
-/

namespace NewmanStructureCheapA

/-- The relation on `X` obtained by pulling `R` back along `e`. -/
def transport {X Y : Type*} (e : X ≃ Y) (R : Y → Y → Prop) : X → X → Prop :=
  fun x₁ x₂ => R (e x₁) (e x₂)

/-- (1) `e` is an isomorphism of relational structures from `transport e R` to `R`. -/
theorem transport_iff {X Y : Type*} (e : X ≃ Y) (R : Y → Y → Prop) :
    ∀ x₁ x₂, transport e R x₁ x₂ ↔ R (e x₁) (e x₂) :=
  fun _ _ => Iff.rfl

/-- (1') The same fact packaged as a Mathlib `RelIso` whose underlying equivalence is `e`. -/
def transport_relIso {X Y : Type*} (e : X ≃ Y) (R : Y → Y → Prop) :
    transport e R ≃r R where
  toEquiv := e
  map_rel_iff' := Iff.rfl

theorem transport_relIso_toEquiv {X Y : Type*} (e : X ≃ Y) (R : Y → Y → Prop) :
    (transport_relIso e R).toEquiv = e := rfl

/-- (2) Structure of a given shape exists on any finite set of the right size. -/
theorem exists_relIso_of_card_eq {X Y : Type*} [Fintype X] [Fintype Y]
    (h : Fintype.card X = Fintype.card Y) (R : Y → Y → Prop) :
    ∃ R' : X → X → Prop, Nonempty (R' ≃r R) :=
  ⟨transport (Fintype.equivOfCardEq h) R, ⟨transport_relIso _ R⟩⟩

/-- (2') For finite domains, "carries some relation isomorphic to `R`" is equivalent to
having the same cardinality as the domain of `R`. -/
theorem exists_relIso_iff_card_eq {X Y : Type*} [Fintype X] [Fintype Y]
    (R : Y → Y → Prop) :
    (∃ R' : X → X → Prop, Nonempty (R' ≃r R)) ↔ Fintype.card X = Fintype.card Y := by
  constructor
  · rintro ⟨R', ⟨f⟩⟩
    exact Fintype.card_congr f.toEquiv
  · intro h
    exact exists_relIso_of_card_eq h R

/-- (3) On a finite type with `n` elements there are `2 ^ (n ^ 2)` binary relations. -/
theorem card_relations (X : Type*) [Fintype X] :
    Nat.card (X → X → Prop) = 2 ^ (Fintype.card X ^ 2) := by
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Prop), Fintype.card_prop,
    Nat.card_eq_fintype_card, ← pow_mul, sq]

/-- (3') The isomorphism class of `R` contains at least one relation on every set with
the same number of elements. -/
theorem isoClass_nonempty_on_every_set {X Y : Type*} [Fintype X] [Fintype Y]
    (h : Fintype.card X = Fintype.card Y) (R : Y → Y → Prop) :
    {R' : X → X → Prop | Nonempty (R' ≃r R)}.Nonempty :=
  exists_relIso_of_card_eq h R

/-- Combined statement: the number of relations on an `n`-element type is `2 ^ (n ^ 2)`,
and every relation on an `n`-element type has an isomorphic copy on every `n`-element type. -/
theorem newman (n : ℕ) :
    (∀ (X : Type) [Fintype X], Fintype.card X = n → Nat.card (X → X → Prop) = 2 ^ (n ^ 2)) ∧
    (∀ (X Y : Type) [Fintype X] [Fintype Y], Fintype.card X = n → Fintype.card Y = n →
      ∀ R : Y → Y → Prop, ∃ R' : X → X → Prop, Nonempty (R' ≃r R)) := by
  refine ⟨fun X _ hX => ?_, fun X Y _ _ hX hY R => exists_relIso_of_card_eq (hX.trans hY.symm) R⟩
  rw [card_relations, hX]

end NewmanStructureCheapA
