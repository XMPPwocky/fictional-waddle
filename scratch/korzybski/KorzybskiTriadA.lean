import Mathlib

/-!
# Korzybski's three premises as statements about maps `f : T → M`

PROVED
* `nonidentity` / `nonidentity_not_injective`: if `T`, `M` are finite with
  `card M < card T`, then any `f : T → M` sends two distinct points of `T` to the
  same symbol; equivalently `f` is not injective.
* `nonallness`: for any type `T` and any `e : T → Set T`, the diagonal region
  `{x | x ∉ e x}` is not `e x` for any `x`; hence `e` is not surjective
  (`nonallness_not_surjective`).
* `self_reflexiveness`: for any type `A` and any `e : A → (A → Bool)`, the function
  `a ↦ !(e a a)` is not in the range of `e`; hence `e` is not surjective
  (`self_reflexiveness_not_surjective`).

INTERPRETED
* (1) Non-identity: a map with fewer symbols than the territory has points identifies
  distinct points of the territory.
* (2) Non-allness: no map indexed by the territory lists all of its regions.
* (3) Self-reflexiveness: a map cannot contain a complete map of its own descriptions
  (Cantor/Lawvere diagonal argument on `Bool`-valued descriptions).
-/

namespace KorzybskiTriadA

/-- Non-identity: fewer map symbols than territory points forces a collision. -/
theorem nonidentity {T M : Type*} [Fintype T] [Fintype M] (f : T → M)
    (h : Fintype.card M < Fintype.card T) : ∃ x y : T, x ≠ y ∧ f x = f y :=
  Fintype.exists_ne_map_eq_of_card_lt f h

/-- Non-identity, injectivity form. -/
theorem nonidentity_not_injective {T M : Type*} [Fintype T] [Fintype M] (f : T → M)
    (h : Fintype.card M < Fintype.card T) : ¬ Function.Injective f := by
  intro hf
  obtain ⟨x, y, hxy, hfxy⟩ := nonidentity f h
  exact hxy (hf hfxy)

/-- Non-allness: the diagonal region is assigned to no point. -/
theorem nonallness {T : Type*} (e : T → Set T) : ∀ x : T, e x ≠ {y | y ∉ e y} := by
  intro x hx
  have h : x ∈ e x ↔ x ∉ e x := by
    constructor
    · intro hm
      have : x ∈ {y | y ∉ e y} := hx ▸ hm
      exact this
    · intro hn
      have : x ∈ {y | y ∉ e y} := hn
      exact hx ▸ this
  exact (iff_not_self h).elim

/-- Non-allness, existential form: some region is not `e x` for any `x`. -/
theorem nonallness_exists {T : Type*} (e : T → Set T) : ∃ S : Set T, ∀ x : T, e x ≠ S :=
  ⟨{y | y ∉ e y}, nonallness e⟩

/-- Non-allness, surjectivity form. -/
theorem nonallness_not_surjective {T : Type*} (e : T → Set T) : ¬ Function.Surjective e :=
  Function.cantor_surjective e

/-- Self-reflexiveness: `a ↦ !(e a a)` is not in the range of `e`. -/
theorem self_reflexiveness {A : Type*} (e : A → (A → Bool)) :
    ∀ a : A, e a ≠ fun b => !(e b b) := by
  intro a ha
  have h := congrFun ha a
  cases hb : e a a <;> simp [hb] at h

/-- Self-reflexiveness, range form. -/
theorem self_reflexiveness_not_mem_range {A : Type*} (e : A → (A → Bool)) :
    (fun b => !(e b b)) ∉ Set.range e := by
  rintro ⟨a, ha⟩
  exact self_reflexiveness e a ha

/-- Self-reflexiveness, surjectivity form. -/
theorem self_reflexiveness_not_surjective {A : Type*} (e : A → (A → Bool)) :
    ¬ Function.Surjective e := by
  intro hs
  exact self_reflexiveness_not_mem_range e (hs _)

end KorzybskiTriadA
