import Mathlib

/-!
# Vector clocks as the down-set (Yoneda) embedding of happened-before

Events are pairs `(p, k) : Fin n × ℕ`. A relation `le` on events is a *causal order* if it is
reflexive, transitive, contains the local order `(p, j) ≤ (p, k)` for `j ≤ k`, and has finite
pasts: `{k | le (q, k) f}` is finite for every event `f` and process `q`.
The vector clock is `V le f q := ncard {k | le (q, k) f}` and the scalar clock is
`L le f := ∑ q, V le f q`.

PROVED
* `past_downClosed`: `{k | le (q, k) f}` is downward closed in `ℕ`.
* `past_eq_Iio`: `{k | le (q, k) f} = Set.Iio (V le f q)`, so `V le f q` counts exactly the
  `q`-events in the causal past of `f`, and they are the first `V le f q` of them.
* `mem_past_iff`: `le (q, k) f ↔ k < V le f q`.
* `V_mono`: `le e f → ∀ q, V le e q ≤ V le f q`.
* `V_reflect`: `(∀ q, V le e q ≤ V le f q) → le e f`.
* `le_iff_V_le`: `le e f ↔ ∀ q, V le e q ≤ V le f q`.
* `L_mono`: `le e f → L le e ≤ L le f`.
* `example_isCausalOrder`, `example_incomparable`, `example_L_le`, `example_L_lt`:
  for two processes with no messages (`leLocal`), the events `e = (0, 0)` and `f = (1, 1)` are
  incomparable while `L e = 1 < 2 = L f`.
* `L_not_reflect`: there is a causal order on `Fin 2 × ℕ` and events `e, f` with
  `L le e ≤ L le f` and `¬ le e f`.

INTERPRETED
* "the number of `k` with `le (q, k) f`" is `Set.ncard`; under finite pasts this is the honest
  cardinality, and `past_eq_Iio` shows it equals one plus the largest such `k` (or `0`).
* "finite pasts" is the hypothesis `Set.Finite {k | le (q, k) f}`.
* "Yoneda embedding" is read as: `f ↦ (q ↦ V le f q)` is an order embedding of the preorder
  into `Fin n → ℕ` with the pointwise order (`le_iff_V_le`); `V` determines the down-set of `f`
  by `past_eq_Iio`.
-/

namespace VectorClocksA

variable {n : ℕ}

/-- Hypotheses on happened-before: preorder, contains local order, finite pasts. -/
structure IsCausalOrder (le : Fin n × ℕ → Fin n × ℕ → Prop) : Prop where
  refl : ∀ e, le e e
  trans : ∀ e f g, le e f → le f g → le e g
  local_le : ∀ (p : Fin n) (j k : ℕ), j ≤ k → le (p, j) (p, k)
  finite_past : ∀ (f : Fin n × ℕ) (q : Fin n), Set.Finite {k : ℕ | le (q, k) f}

/-- Vector clock: number of `q`-events in the causal past of `f`. -/
noncomputable def V (le : Fin n × ℕ → Fin n × ℕ → Prop) (f : Fin n × ℕ) (q : Fin n) : ℕ :=
  {k : ℕ | le (q, k) f}.ncard

/-- Scalar Lamport-style clock. -/
noncomputable def L (le : Fin n × ℕ → Fin n × ℕ → Prop) (f : Fin n × ℕ) : ℕ :=
  ∑ q, V le f q

section

variable {le : Fin n × ℕ → Fin n × ℕ → Prop}

theorem past_downClosed (h : IsCausalOrder le) (f : Fin n × ℕ) (q : Fin n) {j k : ℕ}
    (hk : le (q, k) f) (hjk : j ≤ k) : le (q, j) f :=
  h.trans _ _ _ (h.local_le q j k hjk) hk

/-- A finite downward-closed subset of `ℕ` is `Iio` of its cardinality. -/
theorem finite_downClosed_eq_Iio (S : Set ℕ) (hS : S.Finite)
    (hd : ∀ j k, k ∈ S → j ≤ k → j ∈ S) : S = Set.Iio S.ncard := by
  have hex : ∃ m, m ∉ S := hS.exists_notMem
  classical
  set m := Nat.find hex with hm
  have hS' : S = Set.Iio m := by
    ext k
    simp only [Set.mem_Iio]
    constructor
    · intro hk
      by_contra hlt
      exact Nat.find_spec hex (hd _ _ hk (not_lt.mp hlt))
    · intro hk
      by_contra hkS
      exact absurd (Nat.find_min' hex hkS) (not_le.mpr hk)
  rw [hS']
  congr 1
  rw [Set.ncard_eq_toFinset_card' , Set.toFinset_Iio, Nat.card_Iio]

theorem past_eq_Iio (h : IsCausalOrder le) (f : Fin n × ℕ) (q : Fin n) :
    {k : ℕ | le (q, k) f} = Set.Iio (V le f q) :=
  finite_downClosed_eq_Iio _ (h.finite_past f q)
    (fun _ _ hk hjk => past_downClosed h f q hk hjk)

theorem mem_past_iff (h : IsCausalOrder le) (f : Fin n × ℕ) (q : Fin n) (k : ℕ) :
    le (q, k) f ↔ k < V le f q := by
  have := congrArg (k ∈ ·) (past_eq_Iio h f q)
  simpa using this

theorem V_mono (h : IsCausalOrder le) {e f : Fin n × ℕ} (hef : le e f) (q : Fin n) :
    V le e q ≤ V le f q := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : le (q, V le f q) e := (mem_past_iff h e q _).mpr hlt
  have h2 : le (q, V le f q) f := h.trans _ _ _ h1 hef
  exact lt_irrefl _ ((mem_past_iff h f q _).mp h2)

theorem V_reflect (h : IsCausalOrder le) {e f : Fin n × ℕ}
    (hV : ∀ q, V le e q ≤ V le f q) : le e f := by
  obtain ⟨p, k⟩ := e
  have hk : k < V le (p, k) p := (mem_past_iff h (p, k) p k).mp (h.refl _)
  exact (mem_past_iff h f p k).mpr (lt_of_lt_of_le hk (hV p))

theorem le_iff_V_le (h : IsCausalOrder le) (e f : Fin n × ℕ) :
    le e f ↔ ∀ q, V le e q ≤ V le f q :=
  ⟨fun hef q => V_mono h hef q, V_reflect h⟩

theorem L_mono (h : IsCausalOrder le) {e f : Fin n × ℕ} (hef : le e f) :
    L le e ≤ L le f :=
  Finset.sum_le_sum (fun q _ => V_mono h hef q)

end

/-- Happened-before with no messages: only the local order. -/
def leLocal (e f : Fin 2 × ℕ) : Prop := e.1 = f.1 ∧ e.2 ≤ f.2

theorem example_isCausalOrder : IsCausalOrder leLocal where
  refl _ := ⟨rfl, le_rfl⟩
  trans _ _ _ h1 h2 := ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  local_le _ _ _ hjk := ⟨rfl, hjk⟩
  finite_past f _ := (Set.finite_Iic f.2).subset (fun _ hk => hk.2)

theorem example_V (p q : Fin 2) (k : ℕ) :
    V leLocal (p, k) q = if q = p then k + 1 else 0 := by
  unfold V leLocal
  by_cases hqp : q = p
  · subst hqp
    simp only [true_and, ite_true]
    rw [show {x : ℕ | x ≤ k} = Set.Iic k from rfl, Set.ncard_eq_toFinset_card',
      Set.toFinset_Iic, Nat.card_Iic]
  · simp [hqp]

theorem example_incomparable :
    ¬ leLocal ((0 : Fin 2), 0) ((1 : Fin 2), 1) ∧ ¬ leLocal ((1 : Fin 2), 1) ((0 : Fin 2), 0) := by
  unfold leLocal
  decide

theorem example_L_lt : L leLocal ((0 : Fin 2), 0) < L leLocal ((1 : Fin 2), 1) := by
  unfold L
  simp [example_V]

theorem example_L_le : L leLocal ((0 : Fin 2), 0) ≤ L leLocal ((1 : Fin 2), 1) :=
  example_L_lt.le

theorem L_not_reflect :
    ∃ le : Fin 2 × ℕ → Fin 2 × ℕ → Prop, IsCausalOrder le ∧
      ∃ e f : Fin 2 × ℕ, L le e ≤ L le f ∧ ¬ le e f ∧ ¬ le f e :=
  ⟨leLocal, example_isCausalOrder, (0, 0), (1, 1), example_L_le, example_incomparable⟩

end VectorClocksA
