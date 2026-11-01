import Mathlib

/-!
# Money forces comparability

PROVED:
* `prices_comparable`: for any map `f : P → L` into a linear order and any `a b : P`,
  `f a ≤ f b ∨ f b ≤ f a`.
* `prices_comparable_real`: the same statement for `L = ℝ`.
* `no_order_reflecting_map`: if `a b` are incomparable in a partial order `P`, there is no
  `f : P → L` (into a linear order) with `∀ x y, x ≤ y ↔ f x ≤ f y`.
* `no_order_reflecting_map_real`: the same statement for `L = ℝ`.
* `no_order_embedding`: under the same hypothesis, `IsEmpty (P ↪o L)`.
* `invented_comparison`: under the same hypothesis, every `f : P → L` has `x y` with
  `f x ≤ f y` but `¬ x ≤ y`.
* `tf_ft_incomparable`: in `Fin 2 → Bool` with the pointwise order, `![true, false]` and
  `![false, true]` are incomparable.
* `bool2_no_reflecting_map`: every `f : (Fin 2 → Bool) → ℝ` fails
  `∀ x y, x ≤ y ↔ f x ≤ f y`.
* `bool2_invented_comparison`: for every such `f`, there are `x y` with `f x ≤ f y` and
  `¬ x ≤ y`.
* `countTrue_strictMono`: `countTrue x = ∑ i, (if x i then 1 else 0 : ℝ)` is strictly
  monotone on `Fin 2 → Bool`.
* `exists_strictMono_pricing`: there exists a strictly monotone map `(Fin 2 → Bool) → ℝ`.

INTERPRETED (not part of any theorem statement):
* A partial order of goods with incomparable elements models heterogeneous desires/products;
  a map to a linear order models a single price scale (money as the general equivalent).
  The theorems say that such a scale always makes every pair comparable, hence cannot
  reflect the original order when incomparable pairs exist, while order-preserving (even
  strictly monotone) pricing is still possible. In the Deleuze–Guattari reading, this is
  the axiomatic of capital imposing a common measure on decoded flows: the failure is of
  reflection (a comparison is invented), not of preservation.
-/

namespace MoneyForcesComparabilityA

/-- (1) Any pricing into a linear order makes any two elements comparable. -/
theorem prices_comparable {P L : Type*} [LinearOrder L] (f : P → L) (a b : P) :
    f a ≤ f b ∨ f b ≤ f a :=
  le_total _ _

/-- (1) for real-valued pricing. -/
theorem prices_comparable_real {P : Type*} (f : P → ℝ) (a b : P) :
    f a ≤ f b ∨ f b ≤ f a :=
  prices_comparable f a b

/-- (2) With an incomparable pair, no map into a linear order reflects and preserves the
order. -/
theorem no_order_reflecting_map {P L : Type*} [PartialOrder P] [LinearOrder L] (a b : P)
    (hab : ¬ a ≤ b ∧ ¬ b ≤ a) : ¬ ∃ f : P → L, ∀ x y, x ≤ y ↔ f x ≤ f y := by
  rintro ⟨f, hf⟩
  rcases le_total (f a) (f b) with h | h
  · exact hab.1 ((hf a b).2 h)
  · exact hab.2 ((hf b a).2 h)

/-- (2) for real-valued pricing. -/
theorem no_order_reflecting_map_real {P : Type*} [PartialOrder P] (a b : P)
    (hab : ¬ a ≤ b ∧ ¬ b ≤ a) : ¬ ∃ f : P → ℝ, ∀ x y, x ≤ y ↔ f x ≤ f y :=
  no_order_reflecting_map a b hab

/-- (2) in Mathlib's `OrderEmbedding` form. -/
theorem no_order_embedding {P L : Type*} [PartialOrder P] [LinearOrder L] (a b : P)
    (hab : ¬ a ≤ b ∧ ¬ b ≤ a) : IsEmpty (P ↪o L) :=
  ⟨fun e => no_order_reflecting_map (L := L) a b hab
    ⟨e, fun _ _ => e.le_iff_le.symm⟩⟩

/-- (2) explicit form: every pricing invents a comparison absent from `P`. -/
theorem invented_comparison {P L : Type*} [PartialOrder P] [LinearOrder L] (a b : P)
    (hab : ¬ a ≤ b ∧ ¬ b ≤ a) (f : P → L) : ∃ x y, f x ≤ f y ∧ ¬ x ≤ y := by
  rcases le_total (f a) (f b) with h | h
  · exact ⟨a, b, h, hab.1⟩
  · exact ⟨b, a, h, hab.2⟩

/-- (3) `(true, false)` and `(false, true)` are incomparable in `Fin 2 → Bool`. -/
theorem tf_ft_incomparable :
    ¬ (![true, false] : Fin 2 → Bool) ≤ ![false, true] ∧
      ¬ (![false, true] : Fin 2 → Bool) ≤ ![true, false] := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h 0
    simp [Bool.le_iff_imp] at this
  · have := h 1
    simp [Bool.le_iff_imp] at this

/-- (3) No real-valued map on `Fin 2 → Bool` reflects the order. -/
theorem bool2_no_reflecting_map :
    ∀ f : (Fin 2 → Bool) → ℝ, ¬ ∀ x y, x ≤ y ↔ f x ≤ f y :=
  fun f hf => no_order_reflecting_map_real _ _ tf_ft_incomparable ⟨f, hf⟩

/-- (3) explicit form on `Fin 2 → Bool`. -/
theorem bool2_invented_comparison (f : (Fin 2 → Bool) → ℝ) :
    ∃ x y, f x ≤ f y ∧ ¬ x ≤ y :=
  invented_comparison _ _ tf_ft_incomparable f

/-- Number of `true` coordinates, as a real number. -/
noncomputable def countTrue (x : Fin 2 → Bool) : ℝ :=
  ∑ i, (if x i then 1 else 0 : ℝ)

/-- (4) Counting trues is strictly monotone. -/
theorem countTrue_strictMono : StrictMono countTrue := by
  intro x y hxy
  rw [Pi.lt_def] at hxy
  obtain ⟨hle, i, hi⟩ := hxy
  unfold countTrue
  apply Finset.sum_lt_sum
  · intro j _
    have := hle j
    cases hx : x j <;> cases hy : y j <;> simp_all [Bool.le_iff_imp]
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    cases hx : x i <;> cases hy : y i <;> simp_all [Bool.lt_iff_le_not_le, Bool.le_iff_imp]

/-- (4) A strictly monotone pricing exists. -/
theorem exists_strictMono_pricing : ∃ f : (Fin 2 → Bool) → ℝ, StrictMono f :=
  ⟨countTrue, countTrue_strictMono⟩

end MoneyForcesComparabilityA
