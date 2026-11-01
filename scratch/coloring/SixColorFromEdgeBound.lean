import Mathlib

/-!
# Six colours from a hereditary edge bound

PROVED
* `SixColorFromEdgeBound.colorable_of_forall_exists_low_degree`: if every nonempty finite
  vertex set `S` contains a vertex with at most `d` neighbours inside `S`, then `G` is
  `(d + 1)`-colourable (greedy colouring by removing a low-degree vertex).
* `SixColorFromEdgeBound.restrict_adj`: adjacency in `restrict G S`, the graph on `V` keeping
  only the edges of `G` with both endpoints in `S`.
* `SixColorFromEdgeBound.sum_card_adj_eq_two_mul`: handshake lemma inside a vertex set `S`:
  the sum over `v ∈ S` of the number of neighbours of `v` in `S` is twice the number of
  edges of `G` with both endpoints in `S`.
* `SixColorFromEdgeBound.card_edgeFinset_induce_eq`: the number of edges of the induced
  subgraph `G[S]` equals the number of edges of `G` with both endpoints in `S`.
* `SixColorFromEdgeBound.exists_low_degree`: under the hereditary bound, every nonempty `S`
  has a vertex with at most 5 neighbours in `S`.
* `SixColorFromEdgeBound.six_colorable_of_edge_bound`: if every induced subgraph `G[S]` of a
  finite simple graph with `|S| ≥ 3` has at most `3|S| - 6` edges, then `G` is 6-colourable.
  Sets with fewer than 3 vertices are unconstrained by the hypothesis and handled directly.
* `SixColorFromEdgeBound.six_colorable_of_edge_bound'`: the same with the bound stated on the
  edges of `G` having both endpoints in `S`.
-/

namespace SixColorFromEdgeBound

open Finset SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- Greedy colouring: if every nonempty finite set of vertices contains a vertex with at most
`d` neighbours in that set, then `G` admits a proper colouring with `d + 1` colours. -/
theorem colorable_of_forall_exists_low_degree [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (d : ℕ) (h : ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, #(S.filter (G.Adj v)) ≤ d) :
    G.Colorable (d + 1) := by
  have key : ∀ S : Finset V, ∃ c : V → Fin (d + 1),
      ∀ u ∈ S, ∀ w ∈ S, G.Adj u w → c u ≠ c w := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
      rcases S.eq_empty_or_nonempty with hS | hS
      · exact ⟨fun _ => 0, by simp [hS]⟩
      obtain ⟨v, hv, hdeg⟩ := h S hS
      obtain ⟨c, hc⟩ := ih (S.erase v) (erase_ssubset hv)
      have hlt : #((S.filter (G.Adj v)).image c) < #(univ : Finset (Fin (d + 1))) := by
        rw [card_univ, Fintype.card_fin]
        exact lt_of_le_of_lt (card_image_le.trans hdeg) (Nat.lt_succ_self d)
      obtain ⟨k, -, hk⟩ := exists_mem_notMem_of_card_lt_card hlt
      refine ⟨Function.update c v k, ?_⟩
      have away : ∀ w ∈ S, G.Adj v w → c w ≠ k := by
        intro w hw hadj hck
        exact hk (mem_image.2 ⟨w, mem_filter.2 ⟨hw, hadj⟩, hck⟩)
      intro u hu w hw hadj
      by_cases huv : u = v
      · subst huv
        have hwu : w ≠ u := fun e => G.loopless.irrefl u (e ▸ hadj)
        rw [Function.update_self, Function.update_of_ne hwu]
        exact fun e => away w hw hadj e.symm
      by_cases hwv : w = v
      · subst hwv
        rw [Function.update_self, Function.update_of_ne huv]
        exact away u hu hadj.symm
      rw [Function.update_of_ne huv, Function.update_of_ne hwv]
      exact hc u (mem_erase.2 ⟨huv, hu⟩) w (mem_erase.2 ⟨hwv, hw⟩) hadj
  obtain ⟨c, hc⟩ := key univ
  exact ⟨Coloring.mk c fun {u w} hadj => hc u (mem_univ u) w (mem_univ w) hadj⟩

/-- The graph on `V` keeping exactly the edges of `G` with both endpoints in `S`. -/
def restrict (S : Finset V) : SimpleGraph V where
  Adj u w := G.Adj u w ∧ u ∈ S ∧ w ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

@[simp] theorem restrict_adj (S : Finset V) (u w : V) :
    (restrict G S).Adj u w ↔ G.Adj u w ∧ u ∈ S ∧ w ∈ S := Iff.rfl

theorem sum_card_adj_eq_two_mul [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (S : Finset V) :
    ∑ v ∈ S, #(S.filter (G.Adj v)) =
      2 * #(G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)) := by
  classical
  have hdeg : ∀ v, (restrict G S).degree v = if v ∈ S then #(S.filter (G.Adj v)) else 0 := by
    intro v
    rw [← card_neighborFinset_eq_degree]
    split_ifs with hv
    · congr 1
      ext w
      rw [mem_neighborFinset, mem_filter, restrict_adj]
      tauto
    · rw [card_eq_zero]
      ext w
      rw [mem_neighborFinset, restrict_adj]
      simp [hv]
  have hedge : (restrict G S).edgeFinset = G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S) := by
    ext e
    induction e using Sym2.ind with
    | h a b => rw [mem_edgeFinset, mem_edgeSet, restrict_adj]; simp [mem_edgeFinset]
  have hsum := sum_degrees_eq_twice_card_edges (restrict G S)
  simp_rw [hdeg] at hsum
  rw [sum_ite_mem, univ_inter] at hsum
  rw [hsum, hedge]

theorem card_edgeFinset_induce_eq [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (S : Finset V) :
    #(G.induce (S : Set V)).edgeFinset = #(G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)) := by
  have hmap := map_edgeFinset_induce (G := G) (s := (S : Set V))
  calc #(G.induce (S : Set V)).edgeFinset
      = #((G.induce (S : Set V)).edgeFinset.map
          (Function.Embedding.subtype (· ∈ (S : Set V))).sym2Map) := (card_map _).symm
    _ = #(G.edgeFinset ∩ (S : Set V).toFinset.sym2) := by congr 1; convert hmap
    _ = #(G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)) := by
      congr 1
      ext e
      induction e using Sym2.ind with
      | h a b => simp [mem_edgeFinset]

theorem exists_low_degree [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : ∀ S : Finset V, 3 ≤ #S →
      #(G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)) ≤ 3 * #S - 6)
    (S : Finset V) (hS : S.Nonempty) : ∃ v ∈ S, #(S.filter (G.Adj v)) ≤ 5 := by
  by_cases h3 : 3 ≤ #S
  · by_contra hcon
    push Not at hcon
    have hlow : ∑ _v ∈ S, 6 ≤ ∑ v ∈ S, #(S.filter (G.Adj v)) :=
      sum_le_sum fun v hv => hcon v hv
    rw [sum_const, smul_eq_mul, sum_card_adj_eq_two_mul] at hlow
    have hb := h S h3
    omega
  · obtain ⟨v, hv⟩ := hS
    refine ⟨v, hv, ?_⟩
    have hsub : S.filter (G.Adj v) ⊆ S.erase v := by
      intro w hw
      rw [mem_filter] at hw
      exact mem_erase.2 ⟨fun e => G.loopless.irrefl v (e ▸ hw.2), hw.1⟩
    have := card_le_card hsub
    rw [card_erase_of_mem hv] at this
    omega

/-- Hereditary edge bound stated on edges of `G` with both endpoints in `S`. -/
theorem six_colorable_of_edge_bound' [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : ∀ S : Finset V, 3 ≤ #S →
      #(G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)) ≤ 3 * #S - 6) :
    G.Colorable 6 :=
  colorable_of_forall_exists_low_degree G 5 (exists_low_degree G h)

/-- Six colour theorem from the hereditary Euler bound: if every induced subgraph `G[S]` with
at least 3 vertices has at most `3|S| - 6` edges, then `G` is 6-colourable. -/
theorem six_colorable_of_edge_bound [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : ∀ S : Finset V, 3 ≤ #S → #(G.induce (S : Set V)).edgeFinset ≤ 3 * #S - 6) :
    G.Colorable 6 :=
  six_colorable_of_edge_bound' G fun S hS => (card_edgeFinset_induce_eq G S) ▸ h S hS

end SixColorFromEdgeBound
