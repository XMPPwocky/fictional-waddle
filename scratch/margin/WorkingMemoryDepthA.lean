import Mathlib

/-!
# Working memory and bracket depth

Alphabet `Bool`, with `true` read as `(` and `false` read as `)`.
`L d` is the set of balanced bracket strings whose nesting depth never exceeds `d`:
the numbers of `(` and `)` agree, and in every prefix the number of `)` is at most the
number of `(`, which in turn exceeds the number of `)` by at most `d`.

PROVED
* `card_ge_of_accepts` : every Mathlib `DFA Bool σ` with finite `σ` and
  `M.accepts = L d` has `Fintype.card σ ≥ d + 1` (for every `d`, in particular `d ≥ 1`).
* `card_ge_of_step` : the same bound for a deterministic automaton given by a step
  function `step : σ → Bool → σ`, a start state and an accepting set.
* `counter_accepts` : the automaton `counter d` on `Option (Fin (d + 1))`
  (depth counter `0, …, d` plus a dead state `none`) accepts exactly `L d`.
* `card_counter` : `counter d` has `d + 2` states.
* `exists_dfa_card` : some DFA with exactly `d + 2` states accepts exactly `L d`.

The lower bound is the Myhill–Nerode argument: the prefixes `(^i`, `i = 0, …, d`,
reach pairwise distinct states, since `(^i )^i ∈ L d` while `(^j )^i ∉ L d` for `j ≠ i`.

INTERPRETED (docstring only)
A reader whose only memory is one of `k` states cannot check nesting of depth `k`:
with about four chunks of working memory, depth-four nesting needs paper.
-/

namespace WorkingMemoryDepthA

/-- Balanced bracket strings of nesting depth at most `d`. -/
def L (d : ℕ) : Language Bool :=
  {w | w.count true = w.count false ∧
    ∀ p, p <+: w → p.count false ≤ p.count true ∧ p.count true ≤ p.count false + d}

lemma replicate_mem (d i : ℕ) (hi : i ≤ d) :
    List.replicate i true ++ List.replicate i false ∈ L d := by
  refine ⟨by simp [List.count_replicate], ?_⟩
  intro p hp
  rw [List.prefix_iff_eq_take] at hp
  rw [hp, List.take_append, List.take_replicate, List.take_replicate]
  simp only [List.count_append, List.count_replicate, List.length_replicate]
  simp
  omega

lemma replicate_not_mem (d i j : ℕ) (hij : i ≠ j) :
    List.replicate j true ++ List.replicate i false ∉ L d := by
  intro h
  have := h.1
  simp [List.count_replicate] at this
  omega

/-- Lower bound for Mathlib DFAs. -/
theorem card_ge_of_accepts {σ : Type*} [Fintype σ] (d : ℕ) (M : DFA Bool σ)
    (hM : M.accepts = L d) : d + 1 ≤ Fintype.card σ := by
  let f : Fin (d + 1) → σ := fun i => M.eval (List.replicate i.val true)
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have h1 : List.replicate i.val true ++ List.replicate i.val false ∈ M.accepts := by
      rw [hM]; exact replicate_mem d i.val (by omega)
    have h2 : List.replicate j.val true ++ List.replicate i.val false ∉ M.accepts := by
      rw [hM]; exact replicate_not_mem d i.val j.val hne'
    apply h2
    rw [DFA.mem_accepts] at h1 ⊢
    simp only [DFA.eval, DFA.evalFrom_of_append] at h1 ⊢
    have hij' : M.evalFrom M.start (List.replicate i.val true)
        = M.evalFrom M.start (List.replicate j.val true) := hij
    rw [← hij']
    exact h1
  simpa using Fintype.card_le_of_injective f hf

/-- Lower bound for an automaton given by a step function, a start state and an
accepting set. -/
theorem card_ge_of_step {σ : Type*} [Fintype σ] (d : ℕ) (step : σ → Bool → σ) (start : σ)
    (accept : Set σ)
    (h : ∀ w : List Bool, w.foldl step start ∈ accept ↔ w ∈ L d) :
    d + 1 ≤ Fintype.card σ := by
  apply card_ge_of_accepts d ⟨step, start, accept⟩
  ext w
  exact h w

/-- Transition function of the depth counter with a dead state `none`. -/
def counterStep (d : ℕ) : Option (Fin (d + 1)) → Bool → Option (Fin (d + 1))
  | none, _ => none
  | some k, true => if h : k.val + 1 ≤ d then some ⟨k.val + 1, by omega⟩ else none
  | some k, false => if h : k.val = 0 then none else some ⟨k.val - 1, by omega⟩

/-- The depth counter automaton: states `some 0, …, some d` and the dead state `none`. -/
def counter (d : ℕ) : DFA Bool (Option (Fin (d + 1))) where
  step := counterStep d
  start := some 0
  accept := {some 0}

lemma evalFrom_none (d : ℕ) (w : List Bool) : (counter d).evalFrom none w = none := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [DFA.evalFrom_cons]
    cases b <;> exact ih

lemma forall_prefix_cons {Q : List Bool → Prop} (b : Bool) (w : List Bool) :
    (∀ p, p <+: b :: w → Q p) ↔ Q [] ∧ ∀ t, t <+: w → Q (b :: t) := by
  constructor
  · intro h
    exact ⟨h [] (List.nil_prefix), fun t ht => h (b :: t) ((List.cons_prefix_cons).2 ⟨rfl, ht⟩)⟩
  · rintro ⟨h0, h1⟩ p hp
    cases p with
    | nil => exact h0
    | cons a t =>
      obtain ⟨rfl, ht⟩ := (List.cons_prefix_cons).1 hp
      exact h1 t ht

/-- Acceptance from counter state `k`. -/
def P (d k : ℕ) (w : List Bool) : Prop :=
  k + w.count true = w.count false ∧
    ∀ p, p <+: w → p.count false ≤ k + p.count true ∧ k + p.count true ≤ p.count false + d

lemma evalFrom_some (d : ℕ) (w : List Bool) :
    ∀ k : Fin (d + 1), (counter d).evalFrom (some k) w = some 0 ↔ P d k.val w := by
  induction w with
  | nil =>
    intro k
    simp only [DFA.evalFrom_nil, P, List.prefix_nil, forall_eq, List.count_nil]
    constructor
    · intro h
      have : k = 0 := Option.some_injective _ h
      subst this
      simp
    · rintro ⟨h, -⟩
      congr 1
      exact Fin.ext (by simpa using h)
  | cons b w ih =>
    intro k
    rw [DFA.evalFrom_cons]
    unfold P
    rw [forall_prefix_cons]
    cases b with
    | true =>
      show (counter d).evalFrom (counterStep d (some k) true) w = some 0 ↔ _
      simp only [counterStep]
      split_ifs with hk
      · rw [ih, P]
        simp only [List.count_cons_self, List.count_nil, List.count_cons_of_ne
          (show (true : Bool) ≠ false by decide)]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨by omega, by omega, fun t ht => ?_⟩
          have := h2 t ht
          constructor <;> omega
        · rintro ⟨h1, -, h2⟩
          refine ⟨by omega, fun t ht => ?_⟩
          have := h2 t ht
          constructor <;> omega
      · rw [evalFrom_none]
        simp only [reduceCtorEq, false_iff]
        rintro ⟨-, -, h2⟩
        have := (h2 [] List.nil_prefix).2
        simp at this
        omega
    | false =>
      show (counter d).evalFrom (counterStep d (some k) false) w = some 0 ↔ _
      simp only [counterStep]
      split_ifs with hk
      · rw [evalFrom_none]
        simp only [reduceCtorEq, false_iff]
        rintro ⟨-, -, h2⟩
        have := (h2 [] List.nil_prefix).1
        simp at this
        omega
      · rw [ih, P]
        simp only [List.count_cons_self, List.count_nil, List.count_cons_of_ne
          (show (false : Bool) ≠ true by decide)]
        have hk2 := k.isLt
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨by omega, by omega, fun t ht => ?_⟩
          have := h2 t ht
          constructor <;> omega
        · rintro ⟨h1, -, h2⟩
          refine ⟨by omega, fun t ht => ?_⟩
          have := h2 t ht
          constructor <;> omega

/-- The depth counter accepts exactly `L d`. -/
theorem counter_accepts (d : ℕ) : (counter d).accepts = L d := by
  ext w
  rw [DFA.mem_accepts]
  change (counter d).evalFrom (some 0) w ∈ ({some 0} : Set _) ↔ _
  rw [Set.mem_singleton_iff, evalFrom_some]
  simp only [P, Fin.val_zero, zero_add]
  rfl

/-- The depth counter has `d + 2` states. -/
theorem card_counter (d : ℕ) : Fintype.card (Option (Fin (d + 1))) = d + 2 := by
  simp

/-- Matching upper bound: a DFA with `d + 2` states accepts exactly `L d`. -/
theorem exists_dfa_card (d : ℕ) :
    ∃ (σ : Type) (_ : Fintype σ) (M : DFA Bool σ),
      Fintype.card σ = d + 2 ∧ M.accepts = L d :=
  ⟨Option (Fin (d + 1)), inferInstance, counter d, card_counter d, counter_accepts d⟩

end WorkingMemoryDepthA
