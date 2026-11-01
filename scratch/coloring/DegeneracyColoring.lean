import Mathlib

/-!
# Degeneracy colouring

Greedy colouring along a well-order: if every vertex has at most `d` neighbours
that come earlier in the order, then `d + 1` colours suffice.

PROVED
* `DegeneracyColoring.greedy_lt` : the greedy colour of every vertex is at most `d`.
* `DegeneracyColoring.greedy_ne_of_adj` : adjacent vertices get different greedy colours.
* `DegeneracyColoring.colorable_of_wellOrder` : on a well-ordered vertex type (possibly
  infinite), if the earlier neighbours of each vertex lie in some finset of size at most
  `d`, then `G.Colorable (d + 1)`.
* `DegeneracyColoring.colorable_of_finite` : on a finite linearly ordered vertex type, if
  each vertex has at most `d` smaller neighbours (counted by `Set.ncard`), then
  `G.Colorable (d + 1)`.
* `DegeneracyColoring.colorable_of_finset` : the same with the count taken as
  `((G.neighborFinset v).filter (· < v)).card` on a `Fintype` vertex type.
* `DegeneracyColoring.colorable_of_injective_nat` : for any vertex type with an injective
  map `f : V → ℕ` (possibly infinite), if each vertex has at most `d` neighbours with
  smaller `f`-value (and these form a finite set), then `G.Colorable (d + 1)`.
-/

namespace DegeneracyColoring

open SimpleGraph

variable {V : Type*} [LinearOrder V] [WellFoundedLT V] (G : SimpleGraph V)

/-- Greedy colour: the least natural number not used by any earlier neighbour. -/
noncomputable def greedy : V → ℕ :=
  (wellFounded_lt (α := V)).fix
    (fun v rec => sInf {n : ℕ | ∀ u (h : u < v), G.Adj v u → rec u h ≠ n})

theorem greedy_eq (v : V) :
    greedy G v = sInf {n : ℕ | ∀ u, u < v → G.Adj v u → greedy G u ≠ n} := by
  unfold greedy
  rw [WellFounded.fix_eq]

variable {G} {d : ℕ}

/-- Under the degeneracy hypothesis, some colour `n ≤ d` is free at `v`. -/
theorem exists_free (hd : ∀ v, ∃ s : Finset V, s.card ≤ d ∧ ∀ u, G.Adj v u → u < v → u ∈ s)
    (v : V) : ∃ n, n ≤ d ∧ ∀ u, u < v → G.Adj v u → greedy G u ≠ n := by
  obtain ⟨s, hs, hsub⟩ := hd v
  have : ∃ n ∈ Finset.range (d + 1), n ∉ s.image (greedy G) := by
    by_contra hc
    push Not at hc
    have h1 := Finset.card_le_card (show Finset.range (d + 1) ⊆ s.image (greedy G) from hc)
    have h2 := Finset.card_image_le (s := s) (f := greedy G)
    simp at h1
    omega
  obtain ⟨n, hn, hni⟩ := this
  refine ⟨n, by simpa [Nat.lt_succ_iff] using hn, ?_⟩
  intro u hu hadj heq
  exact hni (Finset.mem_image.2 ⟨u, hsub u hadj hu, heq⟩)

theorem greedy_le (hd : ∀ v, ∃ s : Finset V, s.card ≤ d ∧ ∀ u, G.Adj v u → u < v → u ∈ s)
    (v : V) : greedy G v ≤ d := by
  obtain ⟨n, hn, hfree⟩ := exists_free hd v
  rw [greedy_eq]
  exact le_trans (Nat.sInf_le hfree) hn

theorem greedy_lt (hd : ∀ v, ∃ s : Finset V, s.card ≤ d ∧ ∀ u, G.Adj v u → u < v → u ∈ s)
    (v : V) : greedy G v < d + 1 :=
  Nat.lt_succ_of_le (greedy_le hd v)

theorem greedy_ne_of_lt (hd : ∀ v, ∃ s : Finset V, s.card ≤ d ∧ ∀ u, G.Adj v u → u < v → u ∈ s)
    {u v : V} (huv : u < v) (hadj : G.Adj v u) : greedy G u ≠ greedy G v := by
  obtain ⟨n, -, hfree⟩ := exists_free hd v
  have hmem : greedy G v ∈ {n : ℕ | ∀ u, u < v → G.Adj v u → greedy G u ≠ n} := by
    rw [greedy_eq G v]
    exact Nat.sInf_mem ⟨n, hfree⟩
  exact hmem u huv hadj

theorem greedy_ne_of_adj (hd : ∀ v, ∃ s : Finset V, s.card ≤ d ∧ ∀ u, G.Adj v u → u < v → u ∈ s)
    {u v : V} (hadj : G.Adj u v) : greedy G u ≠ greedy G v := by
  rcases lt_trichotomy u v with h | h | h
  · exact greedy_ne_of_lt hd h hadj.symm
  · exact absurd h (G.ne_of_adj hadj)
  · exact (greedy_ne_of_lt hd h hadj).symm

/-- The greedy colouring as a `Fin (d + 1)`-colouring. -/
noncomputable def greedyColoring
    (hd : ∀ v, ∃ s : Finset V, s.card ≤ d ∧ ∀ u, G.Adj v u → u < v → u ∈ s) :
    G.Coloring (Fin (d + 1)) :=
  Coloring.mk (fun v => ⟨greedy G v, greedy_lt hd v⟩) (by
    intro u v hadj heq
    exact greedy_ne_of_adj hd hadj (congrArg Fin.val heq))

theorem colorable_of_wellOrder
    (hd : ∀ v, ∃ s : Finset V, s.card ≤ d ∧ ∀ u, G.Adj v u → u < v → u ∈ s) :
    G.Colorable (d + 1) :=
  ⟨greedyColoring hd⟩

end DegeneracyColoring

namespace DegeneracyColoring

open SimpleGraph

theorem colorable_of_finite {V : Type*} [LinearOrder V] [Finite V] (G : SimpleGraph V)
    {d : ℕ} (hd : ∀ v, {u | G.Adj v u ∧ u < v}.ncard ≤ d) : G.Colorable (d + 1) := by
  have : WellFoundedLT V := Finite.to_wellFoundedLT
  refine colorable_of_wellOrder (G := G) (fun v => ?_)
  have hfin : {u | G.Adj v u ∧ u < v}.Finite := Set.toFinite _
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact hd v
  · intro u hadj hu
    simp [hadj, hu]

theorem colorable_of_finset {V : Type*} [LinearOrder V] [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (hd : ∀ v, ((G.neighborFinset v).filter (· < v)).card ≤ d) :
    G.Colorable (d + 1) := by
  have : WellFoundedLT V := Finite.to_wellFoundedLT
  refine colorable_of_wellOrder (G := G) (fun v => ⟨(G.neighborFinset v).filter (· < v), hd v, ?_⟩)
  intro u hadj hu
  simp [hadj, hu]

theorem colorable_of_injective_nat {V : Type*} (G : SimpleGraph V) (f : V → ℕ)
    (hf : Function.Injective f) {d : ℕ}
    (hd : ∀ v, ∃ s : Finset V, s.card ≤ d ∧ ∀ u, G.Adj v u → f u < f v → u ∈ s) :
    G.Colorable (d + 1) := by
  let _ : LinearOrder V := LinearOrder.lift' f hf
  have : WellFoundedLT V := InvImage.wf f (wellFounded_lt (α := ℕ))
  exact colorable_of_wellOrder (G := G) hd

end DegeneracyColoring
