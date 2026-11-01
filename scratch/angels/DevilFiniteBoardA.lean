import Mathlib

/-!
# Angel and devil on a finite board

Board: a finite type `V` with `N = Fintype.card V` cells and an arbitrary adjacency relation
`adj : V → V → Prop` (no symmetry, irreflexivity or connectivity assumed).

One turn: the devil names a cell. The removal takes effect only if it is legal, i.e. the cell is
not yet removed and is not the angel's current cell; an illegal choice is a pass (so the devil can
never gain from an illegal choice). Then the angel must move to a cell `b` with `adj a b`, `b ≠ a`
(it may not stay) and `b` not removed. Strategies of both players see the full state, including
the complete history of (devil choice, angel move) pairs, so angel strategies are arbitrary
history-dependent deterministic strategies.

`Survives adj devil angel n st` says the angel makes `n` consecutive legal moves from state `st`.

PROVED
* `exact_form`: if `R` has `N - 1` cells and the angel's cell `a ∉ R`, then `R = univ.erase a`
  and the angel has no legal move (`no_legal_move_of_card`).
* `card_add_le_of_survives`: against any devil that removes a legal cell whenever one exists
  (`IsGreedy`), surviving `n + 1` turns from a state with removed set `R` forces
  `R.card + n + 3 ≤ N`.
* `survives_le`: from the empty start, surviving `n + 1` turns forces `n + 3 ≤ N`, i.e. the angel
  survives at most `N - 2` turns.
* `not_survives_card`: the angel cannot survive `N` turns (any `N ≥ 1`), and
  `not_survives_card_sub_one`: it cannot survive `N - 1` turns when `N ≥ 2`.
* `greedy_isGreedy`: the strategy "remove some remaining unoccupied cell" exists and is greedy.
* `devil_wins_uniform`: there is one devil strategy that beats every angel strategy from every
  start within `N` turns; `devil_wins`: the stated form, for every angel strategy there is a
  devil strategy such that the angel has no legal move within `N` turns.

INTERPRETED
* A finite board plays the role of a sphere (compact, finitely many cells): there the devil wins
  regardless of adjacency, simply by counting removals. Compare `AngelBinaryTree`, where the
  exponential growth of a hyperbolic (tree-like) board lets the angel escape.
-/

namespace DevilFiniteBoardA

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A legal angel move from `a` to `b` when the removed set is `R`. -/
def LegalMove (adj : V → V → Prop) (R : Finset V) (a b : V) : Prop :=
  adj a b ∧ b ≠ a ∧ b ∉ R

/-- A legal devil removal of `c` when the removed set is `R` and the angel is at `a`. -/
def LegalRemoval (R : Finset V) (a c : V) : Prop :=
  c ∉ R ∧ c ≠ a

/-- Game state: removed cells, the angel's position, and the history of
(devil choice, angel move) pairs, most recent first. -/
structure State (V : Type*) where
  removed : Finset V
  pos : V
  hist : List (V × V)

/-- A devil strategy chooses a cell to remove from the full state. -/
abbrev DevilStrategy (V : Type*) := State V → V

/-- An angel strategy chooses a cell to move to from the full state
(with the devil's removal of this turn already applied). -/
abbrev AngelStrategy (V : Type*) := State V → V

/-- The removed set after the devil's choice `c`: applied if legal, otherwise a pass. -/
def applyRemoval (st : State V) (c : V) : Finset V :=
  if c ∉ st.removed ∧ c ≠ st.pos then insert c st.removed else st.removed

/-- The angel makes `n` consecutive legal moves starting from `st`. -/
def Survives (adj : V → V → Prop) (devil : DevilStrategy V) (angel : AngelStrategy V) :
    ℕ → State V → Prop
  | 0, _ => True
  | n + 1, st =>
    LegalMove adj (applyRemoval st (devil st)) st.pos
        (angel ⟨applyRemoval st (devil st), st.pos, st.hist⟩) ∧
      Survives adj devil angel n
        ⟨applyRemoval st (devil st), angel ⟨applyRemoval st (devil st), st.pos, st.hist⟩,
          (devil st, angel ⟨applyRemoval st (devil st), st.pos, st.hist⟩) :: st.hist⟩

/-- Initial state: nothing removed, angel at `a₀`. -/
def init (a₀ : V) : State V := ⟨∅, a₀, []⟩

/-- A devil strategy that removes a legal cell whenever a legal removal exists. -/
def IsGreedy (devil : DevilStrategy V) : Prop :=
  ∀ st : State V, (∃ c, LegalRemoval st.removed st.pos c) →
    LegalRemoval st.removed st.pos (devil st)

/-- "Remove any remaining unoccupied cell." -/
noncomputable def greedy : DevilStrategy V := fun st =>
  open Classical in
  if h : ∃ c, LegalRemoval st.removed st.pos c then Classical.choose h else st.pos

omit [DecidableEq V] in
theorem greedy_isGreedy : IsGreedy (greedy : DevilStrategy V) := by
  intro st h
  classical
  unfold greedy
  rw [dite_eq_left h]
  exact Classical.choose_spec h

/-- Exact form: `N - 1` removed cells not containing the angel's cell are all other cells. -/
theorem exact_form (R : Finset V) (a : V) (ha : a ∉ R)
    (hR : R.card + 1 = Fintype.card V) : R = Finset.univ.erase a := by
  have hsub : R ⊆ Finset.univ.erase a := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩
    rintro rfl
    exact ha hx
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
  omega

/-- After `N - 1` removals (angel's cell excluded) the angel has no legal move. -/
theorem no_legal_move_of_card (adj : V → V → Prop) (R : Finset V) (a : V) (ha : a ∉ R)
    (hR : R.card + 1 = Fintype.card V) : ∀ b, ¬ LegalMove adj R a b := by
  rintro b ⟨-, hba, hbR⟩
  rw [exact_form R a ha hR] at hbR
  exact hbR (Finset.mem_erase.mpr ⟨hba, Finset.mem_univ b⟩)

/-- Two distinct cells outside `R` force `R.card + 2 ≤ N`. -/
theorem card_add_two_le (R : Finset V) (a b : V) (ha : a ∉ R) (hb : b ∉ R) (hab : b ≠ a) :
    R.card + 2 ≤ Fintype.card V := by
  have hsub : insert a (insert b R) ⊆ Finset.univ := Finset.subset_univ _
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem hb] at h1
  · omega
  · simp only [Finset.mem_insert, not_or]
    exact ⟨Ne.symm hab, ha⟩

theorem card_add_le_of_survives (adj : V → V → Prop) (devil : DevilStrategy V)
    (hdev : IsGreedy devil) (angel : AngelStrategy V) :
    ∀ (n : ℕ) (st : State V), st.pos ∉ st.removed →
      Survives adj devil angel (n + 1) st → st.removed.card + n + 3 ≤ Fintype.card V := by
  intro n
  induction n with
  | zero =>
    intro st hpos hs
    obtain ⟨⟨-, hba, hbR⟩, -⟩ := hs
    generalize angel ⟨applyRemoval st (devil st), st.pos, st.hist⟩ = b at hba hbR
    by_cases hex : ∃ c, LegalRemoval st.removed st.pos c
    · have hc := hdev st hex
      obtain ⟨hcR, hca⟩ := hc
      have hR' : applyRemoval st (devil st) = insert (devil st) st.removed := by
        unfold applyRemoval; rw [ite_eq_left ⟨hcR, hca⟩]
      rw [hR'] at hbR
      have hposR' : st.pos ∉ insert (devil st) st.removed := by
        simp only [Finset.mem_insert, not_or]; exact ⟨Ne.symm hca, hpos⟩
      have := card_add_two_le _ _ _ hposR' hbR hba
      rw [Finset.card_insert_of_notMem hcR] at this
      omega
    · exfalso
      have hR' : applyRemoval st (devil st) = st.removed := by
        unfold applyRemoval
        rw [ite_eq_right]
        rintro ⟨h1, h2⟩
        exact hex ⟨devil st, h1, h2⟩
      rw [hR'] at hbR
      exact hex ⟨_, hbR, hba⟩
  | succ n ih =>
    intro st hpos hs
    obtain ⟨⟨-, hba, hbR⟩, hs'⟩ := hs
    have hnext := ih _ hbR hs'
    simp only at hnext
    generalize angel ⟨applyRemoval st (devil st), st.pos, st.hist⟩ = b at hba hbR
    by_cases hex : ∃ c, LegalRemoval st.removed st.pos c
    · obtain ⟨hcR, hca⟩ := hdev st hex
      have hR' : applyRemoval st (devil st) = insert (devil st) st.removed := by
        unfold applyRemoval; rw [ite_eq_left ⟨hcR, hca⟩]
      rw [hR', Finset.card_insert_of_notMem hcR] at hnext
      omega
    · exfalso
      have hR' : applyRemoval st (devil st) = st.removed := by
        unfold applyRemoval
        rw [ite_eq_right]
        rintro ⟨h1, h2⟩
        exact hex ⟨devil st, h1, h2⟩
      rw [hR'] at hbR
      exact hex ⟨_, hbR, hba⟩

/-- From the empty start the angel survives at most `N - 2` turns. -/
theorem survives_le (adj : V → V → Prop) (devil : DevilStrategy V) (hdev : IsGreedy devil)
    (angel : AngelStrategy V) (a₀ : V) (n : ℕ)
    (hs : Survives adj devil angel (n + 1) (init a₀)) : n + 3 ≤ Fintype.card V := by
  have := card_add_le_of_survives adj devil hdev angel n (init a₀)
    (Finset.notMem_empty a₀) hs
  simpa [init] using this

/-- The angel cannot survive `N` turns. -/
theorem not_survives_card (adj : V → V → Prop) (devil : DevilStrategy V) (hdev : IsGreedy devil)
    (angel : AngelStrategy V) (a₀ : V) :
    ¬ Survives adj devil angel (Fintype.card V) (init a₀) := by
  intro hs
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨a₀⟩
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card V = n + 1 := ⟨Fintype.card V - 1, by omega⟩
  rw [hn] at hs
  have := survives_le adj devil hdev angel a₀ n hs
  omega

/-- For `N ≥ 2` the angel cannot survive `N - 1` turns: it is stuck by turn `N - 1`. -/
theorem not_survives_card_sub_one (adj : V → V → Prop) (devil : DevilStrategy V)
    (hdev : IsGreedy devil) (angel : AngelStrategy V) (a₀ : V) (hN : 2 ≤ Fintype.card V) :
    ¬ Survives adj devil angel (Fintype.card V - 1) (init a₀) := by
  intro hs
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card V - 1 = n + 1 := ⟨Fintype.card V - 2, by omega⟩
  rw [hn] at hs
  have := survives_le adj devil hdev angel a₀ n hs
  omega

/-- One devil strategy beats every angel strategy from every start within `N` turns. -/
theorem devil_wins_uniform (adj : V → V → Prop) :
    ∃ devil : DevilStrategy V, ∀ (angel : AngelStrategy V) (a₀ : V),
      ¬ Survives adj devil angel (Fintype.card V) (init a₀) :=
  ⟨greedy, fun angel a₀ => not_survives_card adj greedy greedy_isGreedy angel a₀⟩

/-- For every angel strategy there is a devil strategy such that, from any start, the angel has
no legal move within `N` turns. -/
theorem devil_wins (adj : V → V → Prop) :
    ∀ angel : AngelStrategy V, ∃ devil : DevilStrategy V, ∀ a₀ : V,
      ¬ Survives adj devil angel (Fintype.card V) (init a₀) :=
  fun angel => ⟨greedy, fun a₀ => not_survives_card adj greedy greedy_isGreedy angel a₀⟩

end DevilFiniteBoardA
