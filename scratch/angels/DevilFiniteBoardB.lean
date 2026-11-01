import Mathlib

/-!
# Angel and devil on a finite board

Board: a finite type `V` with `N = Fintype.card V` cells (`N ≥ 1` since the angel
occupies a cell `a₀ : V`) and an arbitrary adjacency relation `adj : V → V → Prop`.

A turn: the devil removes one cell that is not removed and not occupied by the angel
(`LegalRemoval`); then the angel must move to a cell `b` with `adj a b`, `b` not removed,
and `b ≠ a` (`LegalMove`; staying is not allowed). Strategies are arbitrary functions of
the current removed set and angel position. `run σ τ a₀ k` is the state after `k` turns.
`Played … k` means the first `k` turns were played legally by both sides.

PROVED
* `played_card_removed`: after `k` legally played turns exactly `k` cells are removed and
  the angel's cell is not one of them.
* `played_lt_card`: at most `N - 1` turns can be played legally (`k < N`).
* `played_removed_eq_erase`, `played_stuck`: after `N - 1` legally played turns every cell
  except the angel's is removed, and the angel has no legal move.
* `greedyDevil_legalWhenPossible`: the devil strategy "remove any remaining unoccupied cell"
  plays a legal removal whenever one exists.
* `devil_wins`: for every devil strategy that removes legally whenever possible, every angel
  strategy and start cell, there is `k < N` such that the first `k` turns are legal and at
  turn `k + 1` either the angel is already stuck (no legal move, hence none after any
  removal), or the devil removes legally and the angel's strategy makes no legal move.
* `devil_wins_of_angel_legal`: if moreover the angel strategy moves legally whenever it can,
  then at turn `k + 1 ≤ N` the angel genuinely has no legal move.
* `exists_devil_strategy_wins`: for every angel strategy there is a devil strategy
  (namely `greedyDevil`) with the conclusion of `devil_wins_of_angel_legal`.

INTERPRETED
* On a finite board (a sphere) the devil wins within `N` turns by removing any free cell,
  whatever the adjacency; contrast an exponentially growing board (AngelBinaryTree), where
  the angel can escape.
-/

namespace DevilFiniteBoardB

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An angel strategy: given the removed set (after the devil's removal) and the angel's
position, the cell to move to. -/
abbrev AngelStrategy (V : Type*) := Finset V → V → V

/-- A devil strategy: given the removed set and the angel's position, the cell to remove. -/
abbrev DevilStrategy (V : Type*) := Finset V → V → V

/-- Game state: removed cells and the angel's position. -/
structure State (V : Type*) where
  removed : Finset V
  pos : V

/-- The state after `k` turns. -/
def run (σ : AngelStrategy V) (τ : DevilStrategy V) (a₀ : V) : ℕ → State V
  | 0 => ⟨∅, a₀⟩
  | k + 1 =>
    let s := run σ τ a₀ k
    let R := insert (τ s.removed s.pos) s.removed
    ⟨R, σ R s.pos⟩

/-- A legal angel move from `a` to `b` given removed set `R`. -/
def LegalMove (adj : V → V → Prop) (R : Finset V) (a b : V) : Prop :=
  adj a b ∧ b ∉ R ∧ b ≠ a

/-- The angel at `a` has no legal move given removed set `R`. -/
def Stuck (adj : V → V → Prop) (R : Finset V) (a : V) : Prop :=
  ∀ b, ¬ LegalMove adj R a b

/-- A legal devil removal of `d` given removed set `R` and angel position `a`. -/
def LegalRemoval (R : Finset V) (a d : V) : Prop :=
  d ∉ R ∧ d ≠ a

/-- The devil strategy removes legally whenever a legal removal exists. -/
def DevilLegalWhenPossible (τ : DevilStrategy V) : Prop :=
  ∀ R a, (∃ d, LegalRemoval R a d) → LegalRemoval R a (τ R a)

/-- The angel strategy moves legally whenever a legal move exists. -/
def AngelLegalWhenPossible (adj : V → V → Prop) (σ : AngelStrategy V) : Prop :=
  ∀ R a, (∃ b, LegalMove adj R a b) → LegalMove adj R a (σ R a)

/-- Remove any remaining unoccupied cell. -/
noncomputable def greedyDevil : DevilStrategy V := fun R a =>
  open Classical in if h : ∃ d, LegalRemoval R a d then h.choose else a

/-- The devil's removal at turn `k + 1` is legal. -/
def DevilOK (σ : AngelStrategy V) (τ : DevilStrategy V) (a₀ : V) (k : ℕ) : Prop :=
  LegalRemoval (run σ τ a₀ k).removed (run σ τ a₀ k).pos
    (τ (run σ τ a₀ k).removed (run σ τ a₀ k).pos)

/-- The angel's move at turn `k + 1` is legal. -/
def AngelOK (adj : V → V → Prop) (σ : AngelStrategy V) (τ : DevilStrategy V) (a₀ : V)
    (k : ℕ) : Prop :=
  LegalMove adj (run σ τ a₀ (k + 1)).removed (run σ τ a₀ k).pos (run σ τ a₀ (k + 1)).pos

/-- The first `k` turns were played legally by both sides. -/
def Played (adj : V → V → Prop) (σ : AngelStrategy V) (τ : DevilStrategy V) (a₀ : V)
    (k : ℕ) : Prop :=
  ∀ j < k, DevilOK σ τ a₀ j ∧ AngelOK adj σ τ a₀ j

omit [DecidableEq V] in
theorem greedyDevil_legalWhenPossible : DevilLegalWhenPossible (greedyDevil (V := V)) := by
  intro R a h
  classical
  simp only [greedyDevil, h, dite_true]
  exact h.choose_spec

omit [Fintype V] in
theorem played_card_removed (adj : V → V → Prop) (σ : AngelStrategy V)
    (τ : DevilStrategy V) (a₀ : V) :
    ∀ k, Played adj σ τ a₀ k →
      (run σ τ a₀ k).removed.card = k ∧ (run σ τ a₀ k).pos ∉ (run σ τ a₀ k).removed := by
  intro k
  induction k with
  | zero => intro _; simp [run]
  | succ k ih =>
    intro hP
    have hk : Played adj σ τ a₀ k := fun j hj => hP j (Nat.lt_succ_of_lt hj)
    obtain ⟨hc, -⟩ := ih hk
    obtain ⟨hD, hA⟩ := hP k (Nat.lt_succ_self k)
    refine ⟨?_, hA.2.1⟩
    show (insert _ _ : Finset V).card = k + 1
    rw [Finset.card_insert_of_notMem hD.1, hc]

theorem played_removed_subset (adj : V → V → Prop) (σ : AngelStrategy V)
    (τ : DevilStrategy V) (a₀ : V) (k : ℕ) (hP : Played adj σ τ a₀ k) :
    (run σ τ a₀ k).removed ⊆ Finset.univ.erase (run σ τ a₀ k).pos := by
  intro x hx
  have h := (played_card_removed adj σ τ a₀ k hP).2
  refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
  rintro rfl
  exact h hx

theorem played_lt_card (adj : V → V → Prop) (σ : AngelStrategy V)
    (τ : DevilStrategy V) (a₀ : V) (k : ℕ) (hP : Played adj σ τ a₀ k) :
    k < Fintype.card V := by
  have h1 := Finset.card_le_card (played_removed_subset adj σ τ a₀ k hP)
  rw [(played_card_removed adj σ τ a₀ k hP).1, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ] at h1
  have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨a₀⟩
  omega

theorem played_removed_eq_erase (adj : V → V → Prop) (σ : AngelStrategy V)
    (τ : DevilStrategy V) (a₀ : V) (hP : Played adj σ τ a₀ (Fintype.card V - 1)) :
    (run σ τ a₀ (Fintype.card V - 1)).removed =
      Finset.univ.erase (run σ τ a₀ (Fintype.card V - 1)).pos := by
  apply Finset.eq_of_subset_of_card_le (played_removed_subset adj σ τ a₀ _ hP)
  rw [(played_card_removed adj σ τ a₀ _ hP).1, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]

theorem stuck_of_removed_eq_erase (adj : V → V → Prop) (R : Finset V) (a : V)
    (h : R = Finset.univ.erase a) : Stuck adj R a := by
  rintro b ⟨-, hb, hne⟩
  exact hb (h ▸ Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩)

theorem played_stuck (adj : V → V → Prop) (σ : AngelStrategy V)
    (τ : DevilStrategy V) (a₀ : V) (hP : Played adj σ τ a₀ (Fintype.card V - 1)) :
    Stuck adj (run σ τ a₀ (Fintype.card V - 1)).removed
      (run σ τ a₀ (Fintype.card V - 1)).pos :=
  stuck_of_removed_eq_erase adj _ _ (played_removed_eq_erase adj σ τ a₀ hP)

theorem devil_wins (adj : V → V → Prop) (σ : AngelStrategy V) (τ : DevilStrategy V)
    (hτ : DevilLegalWhenPossible τ) (a₀ : V) :
    ∃ k < Fintype.card V, Played adj σ τ a₀ k ∧
      (Stuck adj (run σ τ a₀ k).removed (run σ τ a₀ k).pos ∨
        (DevilOK σ τ a₀ k ∧ ¬ AngelOK adj σ τ a₀ k)) := by
  classical
  have hex : ∃ k, ¬ (DevilOK σ τ a₀ k ∧ AngelOK adj σ τ a₀ k) := by
    by_contra hne
    have hP : Played adj σ τ a₀ (Fintype.card V) := fun j _ =>
      not_not.mp fun h => hne ⟨j, h⟩
    exact lt_irrefl _ (played_lt_card adj σ τ a₀ _ hP)
  set k := Nat.find hex with hkdef
  have hfail : ¬ (DevilOK σ τ a₀ k ∧ AngelOK adj σ τ a₀ k) := Nat.find_spec hex
  have hP : Played adj σ τ a₀ k := by
    intro j hj
    have := Nat.find_min hex hj
    exact not_not.mp this
  refine ⟨k, played_lt_card adj σ τ a₀ k hP, hP, ?_⟩
  by_cases hd : DevilOK σ τ a₀ k
  · exact Or.inr ⟨hd, fun ha => hfail ⟨hd, ha⟩⟩
  · left
    rintro b ⟨-, hb, hne⟩
    exact hd (hτ _ _ ⟨b, hb, hne⟩)

theorem devil_wins_of_angel_legal (adj : V → V → Prop) (σ : AngelStrategy V)
    (hσ : AngelLegalWhenPossible adj σ) (τ : DevilStrategy V)
    (hτ : DevilLegalWhenPossible τ) (a₀ : V) :
    ∃ k < Fintype.card V, Played adj σ τ a₀ k ∧
      (Stuck adj (run σ τ a₀ k).removed (run σ τ a₀ k).pos ∨
        (DevilOK σ τ a₀ k ∧ Stuck adj (run σ τ a₀ (k + 1)).removed (run σ τ a₀ k).pos)) := by
  obtain ⟨k, hk, hP, h | ⟨hd, ha⟩⟩ := devil_wins adj σ τ hτ a₀
  · exact ⟨k, hk, hP, Or.inl h⟩
  · refine ⟨k, hk, hP, Or.inr ⟨hd, fun b hb => ha (hσ _ _ ⟨b, hb⟩)⟩⟩

theorem exists_devil_strategy_wins (adj : V → V → Prop) (σ : AngelStrategy V)
    (hσ : AngelLegalWhenPossible adj σ) (a₀ : V) :
    ∃ τ : DevilStrategy V, DevilLegalWhenPossible τ ∧
      ∃ k < Fintype.card V, Played adj σ τ a₀ k ∧
        (Stuck adj (run σ τ a₀ k).removed (run σ τ a₀ k).pos ∨
          (DevilOK σ τ a₀ k ∧ Stuck adj (run σ τ a₀ (k + 1)).removed (run σ τ a₀ k).pos)) :=
  ⟨greedyDevil, greedyDevil_legalWhenPossible,
    devil_wins_of_angel_legal adj σ hσ greedyDevil greedyDevil_legalWhenPossible a₀⟩

end DevilFiniteBoardB
