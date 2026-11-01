import Mathlib

/-!
# Korzybski's three premises as statements about maps `f : T → M`

PROVED:
* `nonIdentity` : for finite `T`, `M` with `card M < card T` and any `f : T → M`, there are
  distinct `x ≠ y` in `T` with `f x = f y`.
* `nonIdentity_not_injective` : under the same hypotheses, `f` is not injective.
* `nonAllness` : for any type `T` and any `e : T → Set T`, there is a set `S : Set T` with
  `e x ≠ S` for every `x`; the witness is the diagonal set `{x | x ∉ e x}`.
* `nonAllness_diagonal` : the diagonal set `{x | x ∉ e x}` itself is not `e x` for any `x`.
* `nonAllness_not_surjective` : `e` is not surjective.
* `selfReflexiveness` : for any type `A` and any `e : A → (A → Bool)`, the function
  `fun a => !(e a a)` is not in the range of `e`.
* `selfReflexiveness_not_surjective` : such an `e` is not surjective.

INTERPRETED:
* (1) Non-identity: a map with fewer symbols than the territory has points identifies two
  distinct points of the territory ("the map is not the territory").
* (2) Non-allness: no family of regions indexed by the points of the territory lists every
  region of the territory ("the map does not cover all of the territory").
* (3) Self-reflexiveness: no family of `A`-indexed Boolean descriptions of `A` contains the
  diagonal description `a ↦ !(e a a)`, so a map cannot contain a complete map of its own
  descriptions (Cantor/Lawvere diagonal argument).
-/

namespace KorzybskiTriadB

/-- (1) Non-identity: with fewer map symbols than territory points, two distinct points of the
territory receive the same symbol. -/
theorem nonIdentity {T M : Type*} [Fintype T] [Fintype M] (f : T → M)
    (h : Fintype.card M < Fintype.card T) : ∃ x y : T, x ≠ y ∧ f x = f y :=
  Fintype.exists_ne_map_eq_of_card_lt f h

/-- (1') Non-identity, as non-injectivity. -/
theorem nonIdentity_not_injective {T M : Type*} [Fintype T] [Fintype M] (f : T → M)
    (h : Fintype.card M < Fintype.card T) : ¬ Function.Injective f := by
  intro hinj
  obtain ⟨x, y, hxy, hf⟩ := nonIdentity f h
  exact hxy (hinj hf)

/-- (2) Non-allness, diagonal form: the set `{x | x ∉ e x}` is not `e x` for any `x`. -/
theorem nonAllness_diagonal {T : Type*} (e : T → Set T) :
    ∀ x : T, e x ≠ {y | y ∉ e y} := by
  intro x hx
  have h : x ∈ e x ↔ x ∉ e x := by
    constructor
    · intro hm
      have : x ∈ {y | y ∉ e y} := hx ▸ hm
      exact this
    · intro hm
      have : x ∈ {y | y ∉ e y} := hm
      exact hx ▸ this
  by_cases hm : x ∈ e x
  · exact h.mp hm hm
  · exact hm (h.mpr hm)

/-- (2) Non-allness: some region of `T` is not `e x` for any `x`. -/
theorem nonAllness {T : Type*} (e : T → Set T) : ∃ S : Set T, ∀ x : T, e x ≠ S :=
  ⟨{y | y ∉ e y}, nonAllness_diagonal e⟩

/-- (2') Non-allness, as non-surjectivity. -/
theorem nonAllness_not_surjective {T : Type*} (e : T → Set T) : ¬ Function.Surjective e :=
  Function.cantor_surjective e

/-- (3) Self-reflexiveness: the diagonal description `a ↦ !(e a a)` is not in the range of
`e`. -/
theorem selfReflexiveness {A : Type*} (e : A → (A → Bool)) :
    (fun a => !(e a a)) ∉ Set.range e := by
  rintro ⟨a, ha⟩
  have h : e a a = !(e a a) := congrFun ha a
  cases hb : e a a <;> simp [hb] at h

/-- (3') Self-reflexiveness, as non-surjectivity. -/
theorem selfReflexiveness_not_surjective {A : Type*} (e : A → (A → Bool)) :
    ¬ Function.Surjective e := by
  intro hs
  exact selfReflexiveness e (hs fun a => !(e a a))

end KorzybskiTriadB
