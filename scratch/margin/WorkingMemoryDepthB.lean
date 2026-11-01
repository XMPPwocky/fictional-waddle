import Mathlib

/-!
# Bounded-depth bracket checking needs a counter of matching size

Alphabet `Bool`, with `true = "("` and `false = ")"`.

`height w` is the number of `(` minus the number of `)` in `w` (an integer).
`L d` is the set of strings `w` with `height w = 0` and `0 ≤ height (w.take n) ≤ d` for every `n`:
the balanced bracket strings whose nesting depth never exceeds `d`.

PROVED
* `L_iff_ok`: `L d` agrees with the left-to-right recursive checker `Ok d 0`.
* `card_ge_succ_succ`: every Mathlib `DFA Bool σ` with `M.accepts = L d` has
  `d + 2 ≤ Fintype.card σ`. The states reached by `"(" ^ i` (`i = 0, …, d`) and by `")"`
  are pairwise distinct (Myhill–Nerode with suffixes `")" ^ i`).
* `card_ge_succ`: the target bound `d + 1 ≤ Fintype.card σ`, for every `d` (the hypothesis
  `d ≥ 1` is not needed).
* `card_ge_succ_of_step`: the same bound for an automaton given as a step function
  `σ → Bool → σ`, a start state and an accepting set.
* `counterDFA_accepts`, `card_counterState`: the DFA with states `Option (Fin (d + 1))`
  (depth counter `0..d`, plus the dead state `none`) accepts exactly `L d` and has `d + 2`
  states. Together with `card_ge_succ_succ`, `d + 2` is the exact minimum.

INTERPRETED (docstring only)
A reader whose only memory is `k` states cannot check nesting of depth `k`
(it cannot even check depth `k - 1`). With about four chunks of working memory,
depth-four nesting needs paper.
-/

namespace WorkingMemoryDepthB

/-- Contribution of one symbol to the height: `(` is `+1`, `)` is `-1`. -/
def val (b : Bool) : ℤ := if b then 1 else -1

/-- Number of `(` minus number of `)`. -/
def height (w : List Bool) : ℤ := (w.map val).sum

/-- Balanced bracket strings of nesting depth at most `d`. -/
def L (d : ℕ) : Language Bool :=
  {w | height w = 0 ∧ ∀ n, 0 ≤ height (w.take n) ∧ height (w.take n) ≤ d}

@[simp] lemma height_nil : height [] = 0 := rfl

@[simp] lemma height_cons (a : Bool) (w : List Bool) :
    height (a :: w) = val a + height w := by
  simp [height]

lemma height_append (u v : List Bool) : height (u ++ v) = height u + height v := by
  simp [height]

@[simp] lemma height_replicate_true (n : ℕ) : height (List.replicate n true) = n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, height_cons, ih]; simp [val]; ring

@[simp] lemma height_replicate_false (n : ℕ) : height (List.replicate n false) = -n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, height_cons, ih]; simp [val]

/-- Left-to-right checker from current depth `h`. -/
def Ok (d : ℕ) : ℕ → List Bool → Prop
  | h, [] => h = 0
  | h, true :: w => h + 1 ≤ d ∧ Ok d (h + 1) w
  | h, false :: w => 0 < h ∧ Ok d (h - 1) w

lemma ok_iff (d : ℕ) (w : List Bool) : ∀ h : ℕ, h ≤ d →
    (Ok d h w ↔ ((h : ℤ) + height w = 0 ∧
      ∀ n, 0 ≤ (h : ℤ) + height (w.take n) ∧ (h : ℤ) + height (w.take n) ≤ d)) := by
  induction w with
  | nil =>
    intro h hd
    simp only [Ok, height_nil, add_zero, List.take_nil]
    constructor
    · rintro rfl; simp
    · rintro ⟨h0, -⟩; exact_mod_cast h0
  | cons a w ih =>
    intro h hd
    have key : (∀ n, 0 ≤ (h : ℤ) + height ((a :: w).take n) ∧
          (h : ℤ) + height ((a :: w).take n) ≤ d) ↔
        ∀ n, 0 ≤ (h : ℤ) + val a + height (w.take n) ∧
          (h : ℤ) + val a + height (w.take n) ≤ d := by
      constructor
      · intro H n
        have := H (n + 1)
        simp only [List.take_succ_cons, height_cons] at this
        constructor <;> linarith [this.1, this.2]
      · intro H n
        cases n with
        | zero => simp; exact_mod_cast hd
        | succ n =>
          have := H n
          simp only [List.take_succ_cons, height_cons]
          constructor <;> linarith [this.1, this.2]
    rw [key]
    cases a with
    | true =>
      simp only [Ok, val, ite_true, height_cons]
      constructor
      · rintro ⟨h1, hw⟩
        have := (ih (h + 1) h1).1 hw
        push_cast at this
        refine ⟨by linarith [this.1], fun n => ?_⟩
        have := this.2 n
        constructor <;> linarith [this.1, this.2]
      · rintro ⟨h0, H⟩
        have h1 : h + 1 ≤ d := by
          have := (H 0).2
          simp at this
          exact_mod_cast this
        refine ⟨h1, (ih (h + 1) h1).2 ⟨?_, fun n => ?_⟩⟩
        · push_cast; linarith
        · have := H n; push_cast
          constructor <;> linarith [this.1, this.2]
    | false =>
      simp only [Ok, val, Bool.false_eq_true, ite_false, height_cons]
      constructor
      · rintro ⟨h1, hw⟩
        have := (ih (h - 1) (by omega)).1 hw
        have hc : ((h - 1 : ℕ) : ℤ) = (h : ℤ) - 1 := by omega
        rw [hc] at this
        refine ⟨by linarith [this.1], fun n => ?_⟩
        have := this.2 n
        constructor <;> linarith [this.1, this.2]
      · rintro ⟨h0, H⟩
        have h1 : 0 < h := by
          have := (H 0).1
          simp at this
          omega
        have hc : ((h - 1 : ℕ) : ℤ) = (h : ℤ) - 1 := by omega
        refine ⟨h1, (ih (h - 1) (by omega)).2 ⟨?_, fun n => ?_⟩⟩
        · rw [hc]; linarith
        · have := H n; rw [hc]
          constructor <;> linarith [this.1, this.2]

/-- The recursive checker started at depth `0` decides `L d`. -/
theorem L_iff_ok (d : ℕ) (w : List Bool) : w ∈ L d ↔ Ok d 0 w := by
  rw [ok_iff d w 0 (Nat.zero_le _)]
  simp only [Nat.cast_zero, zero_add]
  rfl

lemma mem_L_replicate (d i : ℕ) (hi : i ≤ d) :
    List.replicate i true ++ List.replicate i false ∈ L d := by
  refine ⟨by simp [height_append], fun n => ?_⟩
  rw [List.take_append, List.take_replicate, List.take_replicate, height_append]
  simp only [List.length_replicate, height_replicate_true, height_replicate_false]
  constructor <;> omega

lemma not_mem_L_replicate (d i j : ℕ) (hij : j ≠ i) :
    List.replicate j true ++ List.replicate i false ∉ L d := by
  intro h
  have := h.1
  simp [height_append] at this
  omega

lemma not_mem_L_false (d i : ℕ) : false :: List.replicate i false ∉ L d := by
  intro h
  have := (h.2 1).1
  simp [val] at this

section LowerBound

variable {σ : Type*}

/-- Myhill–Nerode lower bound with the dead state: `d + 2` states are needed. -/
theorem card_ge_succ_succ [Fintype σ] (d : ℕ) (M : DFA Bool σ) (hM : M.accepts = L d) :
    d + 2 ≤ Fintype.card σ := by
  let f : Option (Fin (d + 1)) → σ := fun o =>
    match o with
    | none => M.eval [false]
    | some i => M.eval (List.replicate i true)
  have hmem : ∀ x, x ∈ L d ↔ M.evalFrom M.start x ∈ M.accept := by
    intro x; rw [← hM]; exact DFA.mem_accepts M
  have hinj : Function.Injective f := by
    have key : ∀ (u v : List Bool) (i : ℕ), M.eval u = M.eval v →
        (u ++ List.replicate i false ∈ L d ↔ v ++ List.replicate i false ∈ L d) := by
      intro u v i huv
      rw [hmem, hmem, DFA.evalFrom_of_append, DFA.evalFrom_of_append]
      exact Iff.of_eq (congrArg (fun s => M.evalFrom s (List.replicate i false) ∈ M.accept) huv)
    rintro (_ | i) (_ | j) hfij
    · rfl
    · exfalso
      have := (key _ _ j hfij).2 (mem_L_replicate d j (Nat.lt_succ_iff.mp j.2))
      exact not_mem_L_false d j this
    · exfalso
      have := (key _ _ i hfij).1 (mem_L_replicate d i (Nat.lt_succ_iff.mp i.2))
      exact not_mem_L_false d i this
    · by_contra hne
      have hne' : (j : ℕ) ≠ i := fun h => hne (congrArg some (Fin.ext h.symm))
      have := (key _ _ i hfij).1 (mem_L_replicate d i (Nat.lt_succ_iff.mp i.2))
      exact not_mem_L_replicate d i j hne' this
  have := Fintype.card_le_of_injective f hinj
  simp at this
  omega

/-- The target bound: a DFA accepting exactly `L d` has at least `d + 1` states. -/
theorem card_ge_succ [Fintype σ] (d : ℕ) (M : DFA Bool σ) (hM : M.accepts = L d) :
    d + 1 ≤ Fintype.card σ :=
  le_trans (Nat.le_succ _) (card_ge_succ_succ d M hM)

/-- The same bound for an automaton given by a step function, a start state and an
accepting set; the language of a word is the accepting test after folding `step`. -/
theorem card_ge_succ_of_step [Fintype σ] (d : ℕ) (step : σ → Bool → σ) (start : σ)
    (accept : Set σ) (h : ∀ w, w.foldl step start ∈ accept ↔ w ∈ L d) :
    d + 1 ≤ Fintype.card σ := by
  apply card_ge_succ d ⟨step, start, accept⟩
  ext w
  rw [DFA.mem_accepts]
  exact h w

end LowerBound

section UpperBound

/-- States of the counter automaton: a depth `0..d`, or the dead state `none`. -/
abbrev CounterState (d : ℕ) := Option (Fin (d + 1))

/-- Transition of the counter automaton. -/
def counterStep (d : ℕ) : CounterState d → Bool → CounterState d
  | none, _ => none
  | some h, true => if hh : (h : ℕ) + 1 ≤ d then some ⟨h + 1, by omega⟩ else none
  | some h, false => if (h : ℕ) = 0 then none else some ⟨h - 1, by omega⟩

/-- Depth counter `0..d` plus a dead state. -/
def counterDFA (d : ℕ) : DFA Bool (CounterState d) where
  step := counterStep d
  start := some 0
  accept := {some 0}

theorem card_counterState (d : ℕ) : Fintype.card (CounterState d) = d + 2 := by
  simp

lemma evalFrom_none (d : ℕ) (w : List Bool) : (counterDFA d).evalFrom none w = none := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    show (counterDFA d).evalFrom ((counterDFA d).step none a) w = none
    exact ih

lemma evalFrom_some (d : ℕ) (w : List Bool) : ∀ h : Fin (d + 1),
    ((counterDFA d).evalFrom (some h) w ∈ (counterDFA d).accept ↔ Ok d h w) := by
  induction w with
  | nil =>
    intro h
    show some h = some 0 ↔ (h : ℕ) = 0
    rw [Option.some_inj, Fin.ext_iff]
    rfl
  | cons a w ih =>
    intro h
    show (counterDFA d).evalFrom (counterStep d (some h) a) w ∈ (counterDFA d).accept ↔ _
    cases a with
    | true =>
      simp only [counterStep, Ok]
      split_ifs with hh
      · rw [ih]; simp [hh]
      · rw [evalFrom_none]
        simp [counterDFA, hh]
    | false =>
      simp only [counterStep, Ok]
      split_ifs with hh
      · rw [evalFrom_none]
        simp [counterDFA, hh]
      · rw [ih]
        constructor
        · intro hw; exact ⟨Nat.pos_of_ne_zero hh, hw⟩
        · intro hw; exact hw.2

/-- The counter DFA with `d + 2` states accepts exactly `L d`. -/
theorem counterDFA_accepts (d : ℕ) : (counterDFA d).accepts = L d := by
  ext w
  rw [DFA.mem_accepts, L_iff_ok]
  exact evalFrom_some d w 0

/-- Matching upper bound: some DFA with `d + 2` states accepts exactly `L d`. -/
theorem exists_dfa (d : ℕ) :
    ∃ (σ : Type) (_ : Fintype σ) (M : DFA Bool σ),
      Fintype.card σ = d + 2 ∧ M.accepts = L d :=
  ⟨CounterState d, inferInstance, counterDFA d, card_counterState d, counterDFA_accepts d⟩

end UpperBound

end WorkingMemoryDepthB
