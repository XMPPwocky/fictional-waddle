import Mathlib

/-!
# Money forces comparability

PROVED
* `prices_comparable`: for any partial order `P`, any linear order `α`, any map
  `f : P → α` and any `a b : P`, `f a ≤ f b ∨ f b ≤ f a`.
* `prices_comparable_of_incomparable`: the same, stated under the hypothesis that
  `a, b` are incomparable in `P`.
* `no_order_reflecting_price`: if `a, b : P` are incomparable, there is no
  `f : P → α` with `∀ x y, x ≤ y ↔ f x ≤ f y`.
* `no_orderEmbedding`: in that situation `P ↪o α` is empty.
* `price_invents_comparison`: in that situation every `f : P → α` has a pair
  `x, y` with `¬ x ≤ y` but `f x ≤ f y`; explicitly one of `(a, b)`, `(b, a)`.
* `u_v_incomparable`: in `Fin 2 → Bool` with the pointwise order,
  `u = ![true, false]` and `v = ![false, true]` are incomparable.
* `pair_no_order_reflecting_price`: no map `(Fin 2 → Bool) → ℝ` reflects the order.
* `pair_price_invents_comparison`: every map `(Fin 2 → Bool) → ℝ` compares `u`
  and `v` although they are incomparable.
* `countTrue_strictMono`: `countTrue x = ∑ i, (if x i then 1 else 0)` is a strictly
  monotone map `(Fin 2 → Bool) → ℝ`.
* `countTrue_not_reflecting`: `countTrue` does not reflect the order.

INTERPRETED
* Deleuze–Guattari reading: goods with a partial order of use-comparisons are
  priced by a map into a linear order (money as general equivalent). Any such
  pricing makes all goods comparable (`prices_comparable`), and if two goods were
  incomparable, pricing cannot reflect the original order (`no_order_reflecting_price`):
  it invents a comparison absent among the goods. Monotone pricing exists
  (`countTrue_strictMono`), so the loss lies in reflection, not in preservation.
-/

namespace MoneyForcesComparabilityB

/-- (1) Any pricing into a linear order compares any two elements. -/
theorem prices_comparable {P α : Type*} [PartialOrder P] [LinearOrder α]
    (f : P → α) (a b : P) : f a ≤ f b ∨ f b ≤ f a :=
  le_total (f a) (f b)

section General

variable {P α : Type*} [PartialOrder P] [LinearOrder α]

/-- (1), stated under the incomparability hypothesis. -/
theorem prices_comparable_of_incomparable {a b : P} (_hab : ¬ a ≤ b ∧ ¬ b ≤ a)
    (f : P → α) : f a ≤ f b ∨ f b ≤ f a :=
  le_total (f a) (f b)

/-- (2) If `a, b` are incomparable, no map into a linear order reflects the order. -/
theorem no_order_reflecting_price {a b : P} (hab : ¬ a ≤ b ∧ ¬ b ≤ a) :
    ¬ ∃ f : P → α, ∀ x y, x ≤ y ↔ f x ≤ f y := by
  rintro ⟨f, hf⟩
  rcases le_total (f a) (f b) with h | h
  · exact hab.1 ((hf a b).2 h)
  · exact hab.2 ((hf b a).2 h)

/-- (2), in terms of Mathlib's order embeddings. -/
theorem no_orderEmbedding {a b : P} (hab : ¬ a ≤ b ∧ ¬ b ≤ a) :
    IsEmpty (P ↪o α) :=
  ⟨fun e => no_order_reflecting_price (α := α) hab
    ⟨e, fun _ _ => e.le_iff_le.symm⟩⟩

/-- (2), positive form: every pricing compares `a` and `b` in a direction that
does not hold in `P`. -/
theorem price_invents_comparison {a b : P} (hab : ¬ a ≤ b ∧ ¬ b ≤ a) (f : P → α) :
    (¬ a ≤ b ∧ f a ≤ f b) ∨ (¬ b ≤ a ∧ f b ≤ f a) := by
  rcases le_total (f a) (f b) with h | h
  · exact Or.inl ⟨hab.1, h⟩
  · exact Or.inr ⟨hab.2, h⟩

/-- (2), existential form. -/
theorem exists_invented_comparison {a b : P} (hab : ¬ a ≤ b ∧ ¬ b ≤ a) (f : P → α) :
    ∃ x y : P, ¬ x ≤ y ∧ f x ≤ f y := by
  rcases price_invents_comparison hab f with h | h
  · exact ⟨a, b, h⟩
  · exact ⟨b, a, h⟩

end General

section Pair

/-- The good `(true, false)`. -/
def u : Fin 2 → Bool := ![true, false]

/-- The good `(false, true)`. -/
def v : Fin 2 → Bool := ![false, true]

/-- (3) `u` and `v` are incomparable in the pointwise order. -/
theorem u_v_incomparable : ¬ u ≤ v ∧ ¬ v ≤ u := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h0 := h 0
    exact absurd h0 (by decide)
  · have h1 := h 1
    exact absurd h1 (by decide)

/-- (3) No map `(Fin 2 → Bool) → ℝ` reflects the pointwise order. -/
theorem pair_no_order_reflecting_price :
    ¬ ∃ f : (Fin 2 → Bool) → ℝ, ∀ x y, x ≤ y ↔ f x ≤ f y :=
  no_order_reflecting_price u_v_incomparable

/-- (3) Every map `(Fin 2 → Bool) → ℝ` fails to reflect the order. -/
theorem pair_every_price_fails_reflect (f : (Fin 2 → Bool) → ℝ) :
    ¬ ∀ x y, x ≤ y ↔ f x ≤ f y :=
  fun hf => pair_no_order_reflecting_price ⟨f, hf⟩

/-- (3) Every map `(Fin 2 → Bool) → ℝ` compares `u` and `v`. -/
theorem pair_price_invents_comparison (f : (Fin 2 → Bool) → ℝ) :
    (¬ u ≤ v ∧ f u ≤ f v) ∨ (¬ v ≤ u ∧ f v ≤ f u) :=
  price_invents_comparison u_v_incomparable f

/-- Number of `true` coordinates, as a real number. -/
noncomputable def countTrue (x : Fin 2 → Bool) : ℝ :=
  ∑ i, if x i then 1 else 0

private lemma indicator_mono {p q : Bool} (h : p ≤ q) :
    (if p then (1 : ℝ) else 0) ≤ if q then 1 else 0 := by
  cases p <;> cases q
  · exact le_rfl
  · norm_num
  · exact absurd h (by decide)
  · exact le_rfl

private lemma indicator_strictMono {p q : Bool} (h : p < q) :
    (if p then (1 : ℝ) else 0) < if q then 1 else 0 := by
  cases p <;> cases q
  · exact absurd h (by decide)
  · norm_num
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- (4) Counting trues is strictly monotone. -/
theorem countTrue_strictMono : StrictMono countTrue := by
  intro x y hxy
  have hle : x ≤ y := hxy.le
  obtain ⟨i, hi⟩ : ∃ i, x i < y i := by
    by_contra h
    push Not at h
    exact hxy.ne (le_antisymm hle (fun i => h i))
  apply Finset.sum_lt_sum
  · intro j _
    exact indicator_mono (hle j)
  · exact ⟨i, Finset.mem_univ _, indicator_strictMono hi⟩

/-- (4) A monotone pricing exists. -/
theorem exists_strictMono_price : ∃ f : (Fin 2 → Bool) → ℝ, StrictMono f :=
  ⟨countTrue, countTrue_strictMono⟩

/-- (4) The strictly monotone pricing `countTrue` still fails to reflect the order. -/
theorem countTrue_not_reflecting : ¬ ∀ x y, x ≤ y ↔ countTrue x ≤ countTrue y :=
  pair_every_price_fails_reflect countTrue

/-- (4) Preservation holds and reflection fails, simultaneously. -/
theorem preserve_not_reflect :
    ∃ f : (Fin 2 → Bool) → ℝ, StrictMono f ∧ ¬ ∀ x y, x ≤ y ↔ f x ≤ f y :=
  ⟨countTrue, countTrue_strictMono, countTrue_not_reflecting⟩

end Pair

end MoneyForcesComparabilityB
