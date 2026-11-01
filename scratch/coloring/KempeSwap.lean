import Mathlib

/-!
# The Kempe swap lemma

Let `c` be a proper colouring of a simple graph `G` with colours in `α`, and let `a`, `b` be
two colours. Let `H` be the subgraph of `G` induced on the vertices coloured `a` or `b`.
Swapping `a` and `b` on one connected component of `H` (and leaving every other vertex alone)
gives a proper colouring again.

The swap is `Equiv.swap a b`, applied to `c v` for `v` in the chosen set and not elsewhere.
The hypothesis `a ≠ b` is not needed: when `a = b` the swap is the identity.

PROVED
* `kempeRecolor_valid`: if `C` is any set of `a`/`b`-coloured vertices that is closed under
  adjacency to `a`/`b`-coloured vertices (if `u ∈ C`, `G.Adj u v` and `c v ∈ {a, b}`, then
  `v ∈ C`), then swapping `a` and `b` on `C` keeps the colouring proper.
* `kempeSet_closed`: the vertex set of a connected component of the induced `a`/`b` subgraph
  `G.induce {v | c v = a ∨ c v = b}` satisfies both hypotheses above.
* `kempeComponent_valid`: swapping `a` and `b` on a connected component of the induced `a`/`b`
  subgraph keeps the colouring proper (the Kempe swap lemma as usually stated).
* `kempeComponentColoring`: the swapped colouring packaged as a `G.Coloring α`;
  `kempeComponentColoring_apply_of_not_mem` (vertices outside the component keep their colour)
  and `kempeComponentColoring_apply_of_mem` (vertices inside get `Equiv.swap a b` of their
  colour).
-/

namespace KempeSwap

open SimpleGraph

variable {V α : Type*} [DecidableEq α] {G : SimpleGraph V}

/-- Recolour by swapping `a` and `b` on the vertices of `C`, leaving other vertices alone. -/
noncomputable def kempeRecolor (c : V → α) (a b : α) (C : Set V) (v : V) : α :=
  open Classical in
  if v ∈ C then Equiv.swap a b (c v) else c v

lemma swap_mem_ab (a b x : α) (hx : x = a ∨ x = b) :
    Equiv.swap a b x = a ∨ Equiv.swap a b x = b := by
  rcases hx with rfl | rfl
  · simp
  · simp

/-- Kempe swap on a closed set: swapping two colours on a set of vertices coloured with them,
closed under adjacency to vertices coloured with them, keeps a proper colouring proper. -/
theorem kempeRecolor_valid (c : G.Coloring α) (a b : α) (C : Set V)
    (hcol : ∀ v ∈ C, c v = a ∨ c v = b)
    (hclosed : ∀ u v, G.Adj u v → u ∈ C → (c v = a ∨ c v = b) → v ∈ C)
    {u v : V} (huv : G.Adj u v) :
    kempeRecolor c a b C u ≠ kempeRecolor c a b C v := by
  classical
  unfold kempeRecolor
  by_cases hu : u ∈ C <;> by_cases hv : v ∈ C <;> simp only [hu, hv, ite_true, ite_false]
  · exact fun h => c.valid huv ((Equiv.swap a b).injective h)
  · intro h
    have hv' : c v = a ∨ c v = b := h ▸ swap_mem_ab a b (c u) (hcol u hu)
    exact hv (hclosed u v huv hu hv')
  · intro h
    have hu' : c u = a ∨ c u = b := h ▸ swap_mem_ab a b (c v) (hcol v hv)
    exact hu (hclosed v u huv.symm hv hu')
  · exact c.valid huv

/-- The subgraph of `G` induced on the vertices coloured `a` or `b`. -/
abbrev abGraph (c : V → α) (a b : α) : SimpleGraph {v : V | c v = a ∨ c v = b} :=
  G.induce {v : V | c v = a ∨ c v = b}

/-- The vertex set (in `V`) of a connected component `K` of the induced `a`/`b` subgraph. -/
def kempeSet (c : V → α) (a b : α) (K : (abGraph (G := G) c a b).ConnectedComponent) : Set V :=
  {v | ∃ h : c v = a ∨ c v = b, (abGraph (G := G) c a b).connectedComponentMk ⟨v, h⟩ = K}

omit [DecidableEq α] in
theorem kempeSet_col (c : V → α) (a b : α) (K : (abGraph (G := G) c a b).ConnectedComponent) :
    ∀ v ∈ kempeSet c a b K, c v = a ∨ c v = b := fun _ ⟨h, _⟩ => h

omit [DecidableEq α] in
/-- A component of the induced `a`/`b` subgraph is closed under `G`-adjacency to
`a`/`b`-coloured vertices. -/
theorem kempeSet_closed (c : V → α) (a b : α)
    (K : (abGraph (G := G) c a b).ConnectedComponent) :
    ∀ u v, G.Adj u v → u ∈ kempeSet c a b K → (c v = a ∨ c v = b) → v ∈ kempeSet c a b K := by
  rintro u v huv ⟨hu, hK⟩ hv
  refine ⟨hv, ?_⟩
  rw [← hK]
  symm
  apply ConnectedComponent.connectedComponentMk_eq_of_adj
  exact induce_adj.mpr huv

/-- The Kempe swap lemma: swapping `a` and `b` on one connected component of the subgraph
induced on the `a`/`b`-coloured vertices keeps a proper colouring proper. -/
theorem kempeComponent_valid (c : G.Coloring α) (a b : α)
    (K : (abGraph (G := G) c a b).ConnectedComponent) {u v : V} (huv : G.Adj u v) :
    kempeRecolor c a b (kempeSet c a b K) u ≠ kempeRecolor c a b (kempeSet c a b K) v :=
  kempeRecolor_valid c a b _ (kempeSet_col c a b K) (kempeSet_closed c a b K) huv

/-- The Kempe-swapped colouring as a `G.Coloring α`. -/
noncomputable def kempeComponentColoring (c : G.Coloring α) (a b : α)
    (K : (abGraph (G := G) c a b).ConnectedComponent) : G.Coloring α :=
  Coloring.mk (kempeRecolor c a b (kempeSet c a b K)) fun h => kempeComponent_valid c a b K h

theorem kempeComponentColoring_apply_of_not_mem (c : G.Coloring α) (a b : α)
    (K : (abGraph (G := G) c a b).ConnectedComponent) {v : V} (hv : v ∉ kempeSet c a b K) :
    kempeComponentColoring c a b K v = c v := by
  classical
  change kempeRecolor c a b (kempeSet c a b K) v = c v
  unfold kempeRecolor
  simp [hv]

theorem kempeComponentColoring_apply_of_mem (c : G.Coloring α) (a b : α)
    (K : (abGraph (G := G) c a b).ConnectedComponent) {v : V} (hv : v ∈ kempeSet c a b K) :
    kempeComponentColoring c a b K v = Equiv.swap a b (c v) := by
  classical
  change kempeRecolor c a b (kempeSet c a b K) v = Equiv.swap a b (c v)
  unfold kempeRecolor
  simp [hv]

end KempeSwap
