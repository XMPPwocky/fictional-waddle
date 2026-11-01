import Mathlib

/-!
# Vector clocks as the down-set embedding of happened-before

Events are pairs `(p, k) : Fin n × ℕ`. A `CausalOrder n` is a preorder `le` on events that
contains the local order (`le (p, j) (p, k)` whenever `j ≤ k`) and has finite pasts
(`{k | le (q, k) f}` is finite for all `f`, `q`). The vector clock is
`V f q := Set.ncard {k | le (q, k) f}`, the number of `q`-events in the causal past of `f`,
and the scalar clock is `L f := ∑ q, V f q`.

PROVED
* `past_downward_closed`: `{k | le (q, k) f}` is downward closed in `ℕ`.
* `mem_past_iff_lt_V`: `le (q, k) f ↔ k < V f q`.
* `past_eq_Iio`: `{k | le (q, k) f} = Set.Iio (V f q)`, so `V f q` counts exactly the
  `q`-events below `f`, and they are the indices `0, …, V f q - 1`.
* `V_mono`: `le e f → ∀ q, V e q ≤ V f q`.
* `le_of_V_le`: `(∀ q, V e q ≤ V f q) → le e f`.
* `le_iff_V_le`: `le e f ↔ ∀ q, V e q ≤ V f q`.
* `L_mono`: `le e f → L e ≤ L f`.
* `localOnly`: the two-process order with no messages (`(p, j) ≤ (q, k) ↔ p = q ∧ j ≤ k`)
  is a `CausalOrder 2`.
* `L_not_reflecting`: in `localOnly`, the events `(0, 0)` and `(1, 0)` are incomparable and
  `L (0, 0) ≤ L (1, 0)` (both equal `1`).
* `L_not_reflecting_general`: it is not the case that for every `CausalOrder 2` and all events,
  `L e ≤ L f → le e f`.

INTERPRETED
* "Finite pasts" is taken as `Set.Finite {k | le (q, k) f}`.
* "The number of k with le (q, k) f" is `Set.ncard`, which is the cardinality for a finite set.
-/

namespace VectorClocksB

/-- A preorder on events `Fin n × ℕ` containing the local order, with finite pasts. -/
structure CausalOrder (n : ℕ) where
  le : Fin n × ℕ → Fin n × ℕ → Prop
  refl : ∀ e, le e e
  trans : ∀ e f g, le e f → le f g → le e g
  local_le : ∀ (p : Fin n) (j k : ℕ), j ≤ k → le (p, j) (p, k)
  finite_past : ∀ (f : Fin n × ℕ) (q : Fin n), Set.Finite {k : ℕ | le (q, k) f}

variable {n : ℕ} (C : CausalOrder n)

namespace CausalOrder

/-- The causal past of `f` on process `q`, as a set of local indices. -/
def past (f : Fin n × ℕ) (q : Fin n) : Set ℕ := {k : ℕ | C.le (q, k) f}

/-- Vector clock: the number of `q`-events in the causal past of `f`. -/
noncomputable def V (f : Fin n × ℕ) (q : Fin n) : ℕ := Set.ncard {k : ℕ | C.le (q, k) f}

/-- Scalar Lamport-style clock: the sum of the vector clock entries. -/
noncomputable def L (f : Fin n × ℕ) : ℕ := ∑ q, C.V f q

theorem past_downward_closed (f : Fin n × ℕ) (q : Fin n) {j k : ℕ} (hjk : j ≤ k)
    (hk : C.le (q, k) f) : C.le (q, j) f :=
  C.trans _ _ _ (C.local_le q j k hjk) hk

theorem mem_past_iff_lt_V (f : Fin n × ℕ) (q : Fin n) (k : ℕ) :
    C.le (q, k) f ↔ k < C.V f q := by
  have hfin := C.finite_past f q
  constructor
  · intro hk
    have hsub : (Set.Iio (k + 1)) ⊆ {k : ℕ | C.le (q, k) f} := by
      intro j hj
      exact C.past_downward_closed f q (Nat.lt_succ_iff.mp hj) hk
    have h1 := Set.ncard_le_ncard hsub hfin
    have h2 : (Set.Iio (k + 1)).ncard = k + 1 := by
      rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
    unfold V
    omega
  · intro hlt
    by_contra hk
    have hsub : {k : ℕ | C.le (q, k) f} ⊆ Set.Iio k := by
      intro j hj
      by_contra hjk
      exact hk (C.past_downward_closed f q (not_lt.mp hjk) hj)
    have h1 := Set.ncard_le_ncard hsub (Set.finite_Iio k)
    have h2 : (Set.Iio k).ncard = k := by
      rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
    unfold V at hlt
    omega

theorem past_eq_Iio (f : Fin n × ℕ) (q : Fin n) :
    {k : ℕ | C.le (q, k) f} = Set.Iio (C.V f q) := by
  ext k
  exact C.mem_past_iff_lt_V f q k

theorem V_mono {e f : Fin n × ℕ} (h : C.le e f) (q : Fin n) : C.V e q ≤ C.V f q := by
  apply Set.ncard_le_ncard _ (C.finite_past f q)
  intro k hk
  exact C.trans _ _ _ hk h

theorem le_of_V_le {e f : Fin n × ℕ} (h : ∀ q, C.V e q ≤ C.V f q) : C.le e f := by
  obtain ⟨p, k⟩ := e
  have he : k < C.V (p, k) p := (C.mem_past_iff_lt_V (p, k) p k).mp (C.refl _)
  exact (C.mem_past_iff_lt_V f p k).mpr (lt_of_lt_of_le he (h p))

theorem le_iff_V_le (e f : Fin n × ℕ) : C.le e f ↔ ∀ q, C.V e q ≤ C.V f q :=
  ⟨fun h q => C.V_mono h q, C.le_of_V_le⟩

theorem L_mono {e f : Fin n × ℕ} (h : C.le e f) : C.L e ≤ C.L f :=
  Finset.sum_le_sum fun q _ => C.V_mono h q

end CausalOrder

/-- Two processes, no messages: `(p, j) ≤ (q, k)` iff `p = q` and `j ≤ k`. -/
def localOnly : CausalOrder 2 where
  le e f := e.1 = f.1 ∧ e.2 ≤ f.2
  refl _ := ⟨rfl, le_rfl⟩
  trans _ _ _ h1 h2 := ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  local_le _ _ _ h := ⟨rfl, h⟩
  finite_past f _ := (Set.finite_Iic f.2).subset fun _ hk => hk.2

theorem localOnly_V_same (p : Fin 2) (k : ℕ) : localOnly.V (p, k) p = k + 1 := by
  have h : {j : ℕ | localOnly.le (p, j) (p, k)} = Set.Iio (k + 1) := by
    ext j
    simp only [localOnly, Set.mem_ofPred_eq, Set.mem_Iio, true_and]
    omega
  unfold CausalOrder.V
  rw [h, ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

theorem localOnly_V_other (p q : Fin 2) (hpq : q ≠ p) (k : ℕ) : localOnly.V (p, k) q = 0 := by
  have h : {j : ℕ | localOnly.le (q, j) (p, k)} = ∅ := by
    ext j
    simp only [localOnly, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h
    exact absurd h hpq
  unfold CausalOrder.V
  rw [h, Set.ncard_empty]

theorem localOnly_L (p : Fin 2) (k : ℕ) : localOnly.L (p, k) = k + 1 := by
  unfold CausalOrder.L
  rw [Fin.sum_univ_two]
  fin_cases p
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [localOnly_V_same, localOnly_V_other _ _ (by decide)]
  · simp only [Fin.mk_one, Fin.isValue]
    rw [localOnly_V_same, localOnly_V_other _ _ (by decide), Nat.zero_add]

/-- The scalar clock does not reflect the order: `(0, 0)` and `(1, 0)` are incomparable in
`localOnly`, yet `L (0, 0) ≤ L (1, 0)`. -/
theorem L_not_reflecting :
    ¬ localOnly.le ((0 : Fin 2), 0) ((1 : Fin 2), 0) ∧
    ¬ localOnly.le ((1 : Fin 2), 0) ((0 : Fin 2), 0) ∧
    localOnly.L ((0 : Fin 2), 0) ≤ localOnly.L ((1 : Fin 2), 0) := by
  refine ⟨fun h => absurd h.1 (by decide), fun h => absurd h.1 (by decide), ?_⟩
  rw [localOnly_L, localOnly_L]

theorem L_not_reflecting_general :
    ¬ ∀ (C : CausalOrder 2) (e f : Fin 2 × ℕ), C.L e ≤ C.L f → C.le e f := by
  intro h
  exact L_not_reflecting.1 (h localOnly _ _ L_not_reflecting.2.2)

end VectorClocksB
