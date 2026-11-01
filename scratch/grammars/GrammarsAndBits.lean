/-
# Grammars and bits: aⁿbⁿ needs unboundedly many states

Over the alphabet {a, b} (written false, true), let L = { aⁿbⁿ : n ∈ ℕ }. The grammar S → aSb | ε
generates it (classical, not formalized here).

PROVED
1. `mem_anbn_iff`: aⁱbʲ ∈ L exactly when i = j.
2. `nerode_is_relEq`: two prefixes have the same left quotient (Myhill–Nerode equivalence) exactly
   when every suffix gives them the same membership answer: sameness relative to all suffix probes.
3. `quotients_distinct`: the prefixes aⁱ and aʲ for i ≠ j are told apart by the suffix bⁱ.
4. `anbn_not_regular`: L is not regular (via Mathlib's Myhill–Nerode theorem).
5. `dfa_needs_infinite_states`: any DFA accepting L, over any state type, has infinitely many
   states. No finite number of bits of memory suffices.
6. `passive_cannot_separate`: for any finite set of positive examples aⁿbⁿ (n ∈ S), the finite
   language of exactly those examples and L both contain every example, yet they differ; one
   membership query, at some aᵐbᵐ with m ∉ S, tells them apart.

CITED, NOT PROVED HERE
- Gold (1967): from positive examples alone, no learner identifies, in the limit, every language in
  a class containing all finite languages and one infinite one. Item 6 is the step that drives it.
- Angluin (1987): with membership and equivalence queries, regular languages are learnable exactly
  in polynomial time.
-/

import Mathlib

namespace GrammarsAndBits

open List

/-- The language aⁿbⁿ, with a = false and b = true. -/
def anbn : Language Bool := {s | ∃ n, s = replicate n false ++ replicate n true}

theorem block_eq (i j m n : ℕ)
    (h : replicate i false ++ replicate j true = replicate m false ++ replicate n true) :
    i = m ∧ j = n := by
  have h1 := congrArg (List.count false) h
  have h2 := congrArg (List.count true) h
  simp [List.count_replicate] at h1 h2
  exact ⟨h1, h2⟩

theorem mem_anbn_iff (i j : ℕ) : replicate i false ++ replicate j true ∈ anbn ↔ i = j := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨h1, h2⟩ := block_eq i j n n hn
    omega
  · rintro rfl
    exact ⟨i, rfl⟩

/-- Sameness relative to a set of probes. -/
def relEq {Thing Probe R : Type*} (resp : Thing → Probe → R) (P : Set Probe) (a b : Thing) :
    Prop :=
  ∀ p ∈ P, resp a p = resp b p

theorem nerode_is_relEq (L : Language Bool) (x y : List Bool) :
    L.leftQuotient x = L.leftQuotient y ↔
      relEq (fun u w => (u ++ w ∈ L : Prop)) Set.univ x y := by
  constructor
  · intro h w _
    have := congrArg (fun K : Language Bool => w ∈ K) h
    simpa [Language.mem_leftQuotient] using this
  · intro h
    ext w
    rw [Language.mem_leftQuotient, Language.mem_leftQuotient]
    exact Eq.to_iff (h w (Set.mem_univ w))

theorem quotients_distinct (i j : ℕ) (hij : i ≠ j) :
    anbn.leftQuotient (replicate i false) ≠ anbn.leftQuotient (replicate j false) := by
  intro heq
  have hi : replicate i true ∈ anbn.leftQuotient (replicate i false) := by
    rw [Language.mem_leftQuotient, mem_anbn_iff]
  rw [heq, Language.mem_leftQuotient, mem_anbn_iff] at hi
  exact hij hi.symm

theorem anbn_not_regular : ¬ anbn.IsRegular := by
  intro h
  have hfin := h.finite_range_leftQuotient
  have hinj : Function.Injective fun i : ℕ => anbn.leftQuotient (replicate i false) := by
    intro i j hq
    by_contra hne
    exact quotients_distinct i j hne hq
  have hinf := Set.infinite_range_of_injective hinj
  exact hinf (hfin.subset (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩))

theorem dfa_needs_infinite_states {σ : Type*} (M : DFA Bool σ) (hM : M.accepts = anbn) :
    Infinite σ := by
  have hinj : Function.Injective fun i : ℕ => M.eval (replicate i false) := by
    intro i j hij
    by_contra hne
    apply quotients_distinct i j hne
    rw [← hM, Language.leftQuotient_accepts_apply, Language.leftQuotient_accepts_apply]
    exact congrArg M.acceptsFrom hij
  exact Infinite.of_injective _ hinj

/-- The finite language containing exactly the examples aⁿbⁿ for n ∈ S. -/
def finiteOf (S : Finset ℕ) : Language Bool :=
  {s | ∃ n ∈ S, s = replicate n false ++ replicate n true}

theorem passive_cannot_separate (S : Finset ℕ) :
    (∀ n ∈ S, replicate n false ++ replicate n true ∈ finiteOf S ∧
      replicate n false ++ replicate n true ∈ anbn) ∧
    ∃ m, replicate m false ++ replicate m true ∈ anbn ∧
      replicate m false ++ replicate m true ∉ finiteOf S := by
  refine ⟨fun n hn => ⟨⟨n, hn, rfl⟩, ⟨n, rfl⟩⟩, ?_⟩
  obtain ⟨m, hm⟩ := Infinite.exists_notMem_finset S
  refine ⟨m, ⟨m, rfl⟩, ?_⟩
  rintro ⟨n, hn, h⟩
  obtain ⟨h1, _⟩ := block_eq m m n n h
  exact hm (h1 ▸ hn)

end GrammarsAndBits

#print axioms GrammarsAndBits.mem_anbn_iff
#print axioms GrammarsAndBits.nerode_is_relEq
#print axioms GrammarsAndBits.quotients_distinct
#print axioms GrammarsAndBits.anbn_not_regular
#print axioms GrammarsAndBits.dfa_needs_infinite_states
#print axioms GrammarsAndBits.passive_cannot_separate
