import Mathlib

/-!
# Swapping the players negates a game

Mathlib v4.35 no longer contains combinatorial game theory: `SetTheory.PGame` and
`SetTheory.Game` were removed from Mathlib (moved to the separate CombinatorialGames
project) and no file under `Mathlib/` mentions `PGame`. This file therefore rebuilds the
minimal part of the former `Mathlib.SetTheory.Game.PGame` faithfully: Conway's
inductive pre-games, the mutually recursive order (`≤` and the less-or-fuzzy relation `⧏`)
defined by nested recursion exactly as in former Mathlib, negation (swap the roles of Left
and Right), and the disjunctive sum.

PROVED
* `le_def`, `lf_def` : the Conway order unfolds as
  `x ≤ y ↔ (∀ i, xL i ⧏ y) ∧ (∀ j, x ⧏ yR j)` and
  `x ⧏ y ↔ (∃ i, x ≤ yL i) ∨ (∃ j, xR j ≤ y)`.
* `not_le` : `¬ x ≤ y ↔ y ⧏ x`, and `not_lf` : `¬ x ⧏ y ↔ y ≤ x`
  (so `⧏` is genuinely the negation of `≥`; former Mathlib `PGame.not_le`, `PGame.not_lf`).
* `equiv_refl`, `equiv_symm` : `≈` (defined as `x ≤ y ∧ y ≤ x`) is reflexive and symmetric.
* (1) `neg_neg` : `-(-G) = G`, literal equality of pre-games (former Mathlib `PGame.neg_neg`).
* (2) `add_neg_equiv_zero` : `G + (-G) ≈ 0` for every pre-game `G` (mirror / copycat strategy;
  former Mathlib `PGame.add_neg_equiv`), with both halves `add_neg_le_zero`, `zero_le_add_neg`.
* (3) `neg_add_equiv` : `-(G + H) ≈ (-G) + (-H)` (former Mathlib `PGame.neg_add_relabelling`
  gives a relabelling; here the two inequalities are proved directly).
* (4) `neg_star`, `star_add_star_equiv_zero`, `star_fuzzy_zero`, `star_not_equiv_zero`:
  `-⋆ = ⋆`, `⋆ + ⋆ ≈ 0`, `⋆ ⧏ 0 ∧ 0 ⧏ ⋆` (Right moving first wins, Left moving first wins,
  i.e. a first-player win), and `¬ ⋆ ≈ 0`; also `not_star_le_zero`, `not_zero_le_star`.

INTERPRETED
* "Mathlib's combinatorial game theory" is unavailable in the pinned Mathlib, so the
  former Mathlib definitions are reproduced locally; no Mathlib game lemma is cited because
  none exists in this version. The names of the corresponding former Mathlib lemmas are
  given above for reference.
* `x ⧏ y` means "Left wins `y - x` moving first"; `x ≤ y` means "Left wins `y - x` when Right
  moves first"; `x ≈ y` is `x ≤ y ∧ y ≤ x`; for `x = G + (-G)`,
  `x ≈ 0` says the second player wins.
-/

universe u

namespace MirrorStrategyNegationB

/-- Conway pre-games: a type of Left moves, a type of Right moves, and the resulting games. -/
inductive PGame : Type (u + 1)
  | mk : ∀ α β : Type u, (α → PGame) → (β → PGame) → PGame

namespace PGame

/-- The type of Left moves. -/
def LeftMoves : PGame → Type u
  | mk l _ _ _ => l

/-- The type of Right moves. -/
def RightMoves : PGame → Type u
  | mk _ r _ _ => r

/-- The game after a Left move. -/
def moveLeft : ∀ g : PGame, LeftMoves g → PGame
  | mk _ _ L _ => L

/-- The game after a Right move. -/
def moveRight : ∀ g : PGame, RightMoves g → PGame
  | mk _ _ _ R => R

@[simp] theorem leftMoves_mk {xl xr xL xR} : (mk xl xr xL xR).LeftMoves = xl := rfl
@[simp] theorem rightMoves_mk {xl xr xL xR} : (mk xl xr xL xR).RightMoves = xr := rfl
@[simp] theorem moveLeft_mk {xl xr xL xR} : (mk xl xr xL xR).moveLeft = xL := rfl
@[simp] theorem moveRight_mk {xl xr xL xR} : (mk xl xr xL xR).moveRight = xR := rfl

/-- Simultaneous definition of `x ≤ y` (first component) and `x ⧏ y` (second component),
by nested recursion: outer on `x`, inner on `y`, as in former Mathlib. -/
noncomputable def leLF (x : PGame.{u}) : PGame.{u} → Prop × Prop := by
  induction x with
  | mk xl xr _ _ IHxl IHxr =>
    intro y
    induction y with
    | mk yl yr _ _ IHyl IHyr =>
      exact ((∀ i, (IHxl i (mk yl yr ‹_› ‹_›)).2) ∧ (∀ j, (IHyr j).2),
             (∃ i, (IHyl i).1) ∨ (∃ j, (IHxr j (mk yl yr ‹_› ‹_›)).1))

/-- The Conway order. -/
def le (x y : PGame) : Prop := (leLF x y).1

/-- The less-or-fuzzy relation. -/
def LF (x y : PGame) : Prop := (leLF x y).2

instance : LE PGame := ⟨le⟩

@[inherit_doc] scoped infixl:50 " ⧏ " => PGame.LF

theorem le_def {xl xr : Type u} {xL : xl → PGame} {xR : xr → PGame}
    {yl yr : Type u} {yL : yl → PGame} {yR : yr → PGame} :
    mk xl xr xL xR ≤ mk yl yr yL yR ↔
      (∀ i, xL i ⧏ mk yl yr yL yR) ∧ (∀ j, mk xl xr xL xR ⧏ yR j) :=
  Iff.rfl

theorem lf_def {xl xr : Type u} {xL : xl → PGame} {xR : xr → PGame}
    {yl yr : Type u} {yL : yl → PGame} {yR : yr → PGame} :
    mk xl xr xL xR ⧏ mk yl yr yL yR ↔
      (∃ i, mk xl xr xL xR ≤ yL i) ∨ (∃ j, xR j ≤ mk yl yr yL yR) :=
  Iff.rfl

theorem le_iff {x y : PGame} :
    x ≤ y ↔ (∀ i, x.moveLeft i ⧏ y) ∧ (∀ j, x ⧏ y.moveRight j) := by
  cases x; cases y; exact le_def

theorem lf_iff {x y : PGame} :
    x ⧏ y ↔ (∃ i, x ≤ y.moveLeft i) ∨ (∃ j, x.moveRight j ≤ y) := by
  cases x; cases y; exact lf_def

theorem not_le_and_not_lf (x y : PGame) : (¬ x ≤ y ↔ y ⧏ x) ∧ (¬ x ⧏ y ↔ y ≤ x) := by
  induction x generalizing y with
  | mk xl xr xL xR IHxl IHxr =>
    induction y with
    | mk yl yr yL yR IHyl IHyr =>
      constructor
      · rw [le_def, lf_def]
        simp only [not_and_or, not_forall]
        apply or_congr
        · exact exists_congr fun i => (IHxl i _).2
        · exact exists_congr fun j => (IHyr j).2
      · rw [lf_def, le_def]
        simp only [not_or, not_exists]
        apply and_congr
        · exact forall_congr' fun i => (IHyl i).1
        · exact forall_congr' fun j => (IHxr j _).1

theorem not_le {x y : PGame} : ¬ x ≤ y ↔ y ⧏ x := (not_le_and_not_lf x y).1

theorem not_lf {x y : PGame} : ¬ x ⧏ y ↔ y ≤ x := (not_le_and_not_lf x y).2

/-- Equivalence of pre-games. -/
def Equiv (x y : PGame) : Prop := x ≤ y ∧ y ≤ x

instance : HasEquiv PGame := ⟨Equiv⟩

/-- Fuzzy (incomparable): each side is less-or-fuzzy than the other. -/
def Fuzzy (x y : PGame) : Prop := x ⧏ y ∧ y ⧏ x

theorem lf_of_le_moveLeft {x y : PGame} {i : y.LeftMoves} (h : x ≤ y.moveLeft i) : x ⧏ y :=
  lf_iff.2 (Or.inl ⟨i, h⟩)

theorem lf_of_moveRight_le {x y : PGame} {j : x.RightMoves} (h : x.moveRight j ≤ y) : x ⧏ y :=
  lf_iff.2 (Or.inr ⟨j, h⟩)

theorem le_refl' (x : PGame) : x ≤ x := by
  induction x with
  | mk xl xr xL xR IHl IHr =>
    rw [le_def]
    exact ⟨fun i => lf_of_le_moveLeft (i := i) (IHl i),
      fun j => lf_of_moveRight_le (j := j) (IHr j)⟩

theorem equiv_refl (x : PGame) : x ≈ x := ⟨le_refl' x, le_refl' x⟩

theorem equiv_symm {x y : PGame} (h : x ≈ y) : y ≈ x := ⟨h.2, h.1⟩

/-- The zero game: no moves for either player. -/
instance : Zero PGame := ⟨mk PEmpty PEmpty PEmpty.elim PEmpty.elim⟩

theorem le_zero {x : PGame} : x ≤ 0 ↔ ∀ i, ∃ j, (x.moveLeft i).moveRight j ≤ 0 := by
  rw [le_iff]
  constructor
  · rintro ⟨h, -⟩ i
    rcases lf_iff.1 (h i) with ⟨k, -⟩ | ⟨j, hj⟩
    · cases k
    · exact ⟨j, hj⟩
  · intro h
    refine ⟨fun i => ?_, fun j => (by cases j)⟩
    obtain ⟨j, hj⟩ := h i
    exact lf_of_moveRight_le hj

theorem zero_le {x : PGame} : 0 ≤ x ↔ ∀ j, ∃ i, 0 ≤ (x.moveRight j).moveLeft i := by
  rw [le_iff]
  constructor
  · rintro ⟨-, h⟩ j
    rcases lf_iff.1 (h j) with ⟨i, hi⟩ | ⟨k, -⟩
    · exact ⟨i, hi⟩
    · cases k
  · intro h
    refine ⟨fun i => (by cases i), fun j => ?_⟩
    obtain ⟨i, hi⟩ := h j
    exact lf_of_le_moveLeft hi

/-- Negation swaps the roles of Left and Right. -/
def neg : PGame → PGame
  | mk l r L R => mk r l (fun i => neg (R i)) (fun i => neg (L i))

instance : Neg PGame := ⟨neg⟩

theorem neg_def {xl xr : Type u} {xL : xl → PGame} {xR : xr → PGame} :
    -mk xl xr xL xR = mk xr xl (fun j => -xR j) (fun i => -xL i) := rfl

/-- (1) Negation is an involution (literal equality). -/
theorem neg_neg (x : PGame) : -(-x) = x := by
  induction x with
  | mk xl xr xL xR IHl IHr =>
    rw [neg_def, neg_def]
    congr
    · funext i; exact IHl i
    · funext j; exact IHr j

theorem exists_neg_moveLeft (x : PGame) (i : (-x).LeftMoves) :
    ∃ j : x.RightMoves, (-x).moveLeft i = -(x.moveRight j) := by
  cases x; exact ⟨i, rfl⟩

theorem exists_neg_moveRight (x : PGame) (j : (-x).RightMoves) :
    ∃ i : x.LeftMoves, (-x).moveRight j = -(x.moveLeft i) := by
  cases x; exact ⟨j, rfl⟩

theorem exists_moveLeft_neg (x : PGame) (j : x.RightMoves) :
    ∃ i : (-x).LeftMoves, (-x).moveLeft i = -(x.moveRight j) := by
  cases x; exact ⟨j, rfl⟩

theorem exists_moveRight_neg (x : PGame) (i : x.LeftMoves) :
    ∃ j : (-x).RightMoves, (-x).moveRight j = -(x.moveLeft i) := by
  cases x; exact ⟨i, rfl⟩

/-- The disjunctive sum: a move is a move in exactly one component. -/
noncomputable def add (x : PGame.{u}) : PGame.{u} → PGame.{u} := by
  induction x with
  | mk xl xr _ _ IHxl IHxr =>
    intro y
    induction y with
    | mk yl yr yL yR IHyl IHyr =>
      exact mk (xl ⊕ yl) (xr ⊕ yr)
        (Sum.rec (fun i => IHxl i (mk yl yr yL yR)) IHyl)
        (Sum.rec (fun i => IHxr i (mk yl yr yL yR)) IHyr)

noncomputable instance : Add PGame := ⟨add⟩

theorem add_def {xl xr : Type u} {xL : xl → PGame} {xR : xr → PGame}
    {yl yr : Type u} {yL : yl → PGame} {yR : yr → PGame} :
    mk xl xr xL xR + mk yl yr yL yR =
      mk (xl ⊕ yl) (xr ⊕ yr)
        (Sum.rec (fun i => xL i + mk yl yr yL yR) (fun i => mk xl xr xL xR + yL i))
        (Sum.rec (fun i => xR i + mk yl yr yL yR) (fun i => mk xl xr xL xR + yR i)) := rfl

theorem add_moveLeft_cases (x y : PGame) (k : (x + y).LeftMoves) :
    (∃ i, (x + y).moveLeft k = x.moveLeft i + y) ∨
      (∃ i, (x + y).moveLeft k = x + y.moveLeft i) := by
  cases x; cases y
  rcases k with i | i
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

theorem add_moveRight_cases (x y : PGame) (k : (x + y).RightMoves) :
    (∃ j, (x + y).moveRight k = x.moveRight j + y) ∨
      (∃ j, (x + y).moveRight k = x + y.moveRight j) := by
  cases x; cases y
  rcases k with j | j
  · exact Or.inl ⟨j, rfl⟩
  · exact Or.inr ⟨j, rfl⟩

theorem exists_add_moveRight_left (x y : PGame) (j : x.RightMoves) :
    ∃ k, (x + y).moveRight k = x.moveRight j + y := by
  cases x; cases y; exact ⟨Sum.inl j, rfl⟩

theorem exists_add_moveRight_right (x y : PGame) (j : y.RightMoves) :
    ∃ k, (x + y).moveRight k = x + y.moveRight j := by
  cases x; cases y; exact ⟨Sum.inr j, rfl⟩

theorem exists_add_moveLeft_left (x y : PGame) (i : x.LeftMoves) :
    ∃ k, (x + y).moveLeft k = x.moveLeft i + y := by
  cases x; cases y; exact ⟨Sum.inl i, rfl⟩

theorem exists_add_moveLeft_right (x y : PGame) (i : y.LeftMoves) :
    ∃ k, (x + y).moveLeft k = x + y.moveLeft i := by
  cases x; cases y; exact ⟨Sum.inr i, rfl⟩

/-- (2a) Right, moving second in `G + (-G)`, copies Left's move in the other component. -/
theorem add_neg_le_zero (x : PGame) : x + -x ≤ 0 := by
  induction x with
  | mk xl xr xL xR IHl IHr =>
    rw [le_zero]
    intro k
    rcases add_moveLeft_cases _ _ k with ⟨i, h⟩ | ⟨i, h⟩
    · -- Left moved to `xL i` in `G`; Right answers `-(xL i)` in `-G`.
      rw [h]
      obtain ⟨j, hj⟩ := exists_moveRight_neg (mk xl xr xL xR) i
      obtain ⟨k', hk'⟩ := exists_add_moveRight_right ((mk xl xr xL xR).moveLeft i)
        (-mk xl xr xL xR) j
      refine ⟨k', ?_⟩
      rw [hk', hj]
      exact IHl i
    · -- Left moved to `-(xR j)` in `-G`; Right answers `xR j` in `G`.
      rw [h]
      obtain ⟨j, hj⟩ := exists_neg_moveLeft (mk xl xr xL xR) i
      rw [hj]
      obtain ⟨k', hk'⟩ := exists_add_moveRight_left (mk xl xr xL xR)
        (-(mk xl xr xL xR).moveRight j) j
      refine ⟨k', ?_⟩
      rw [hk']
      exact IHr j

/-- (2b) Left, moving second in `G + (-G)`, copies Right's move in the other component. -/
theorem zero_le_add_neg (x : PGame) : 0 ≤ x + -x := by
  induction x with
  | mk xl xr xL xR IHl IHr =>
    rw [zero_le]
    intro k
    rcases add_moveRight_cases _ _ k with ⟨j, h⟩ | ⟨j, h⟩
    · -- Right moved to `xR j` in `G`; Left answers `-(xR j)` in `-G`.
      rw [h]
      obtain ⟨i, hi⟩ := exists_moveLeft_neg (mk xl xr xL xR) j
      obtain ⟨k', hk'⟩ := exists_add_moveLeft_right ((mk xl xr xL xR).moveRight j)
        (-mk xl xr xL xR) i
      refine ⟨k', ?_⟩
      rw [hk', hi]
      exact IHr j
    · -- Right moved to `-(xL i)` in `-G`; Left answers `xL i` in `G`.
      rw [h]
      obtain ⟨i, hi⟩ := exists_neg_moveRight (mk xl xr xL xR) j
      rw [hi]
      obtain ⟨k', hk'⟩ := exists_add_moveLeft_left (mk xl xr xL xR)
        (-(mk xl xr xL xR).moveLeft i) i
      refine ⟨k', ?_⟩
      rw [hk']
      exact IHl i

/-- (2) The mirror (copycat) strategy: `G + (-G) ≈ 0` for every pre-game `G`. -/
theorem add_neg_equiv_zero (x : PGame) : x + -x ≈ 0 :=
  ⟨add_neg_le_zero x, zero_le_add_neg x⟩

/-- Both inequalities between `-(G + H)` and `-G + -H`, by induction on the pair. -/
theorem neg_add_le_both (x y : PGame) : -(x + y) ≤ -x + -y ∧ -x + -y ≤ -(x + y) := by
  induction x generalizing y with
  | mk xl xr xL xR IHxl IHxr =>
    induction y with
    | mk yl yr yL yR IHyl IHyr =>
      constructor
      · rw [le_iff]
        constructor
        · rintro (a | b)
          · exact lf_of_le_moveLeft (i := Sum.inl a) (IHxr a (mk yl yr yL yR)).1
          · exact lf_of_le_moveLeft (i := Sum.inr b) (IHyr b).1
        · rintro (a | b)
          · exact lf_of_moveRight_le (j := Sum.inl a) (IHxl a (mk yl yr yL yR)).1
          · exact lf_of_moveRight_le (j := Sum.inr b) (IHyl b).1
      · rw [le_iff]
        constructor
        · rintro (a | b)
          · exact lf_of_le_moveLeft (i := Sum.inl a) (IHxr a (mk yl yr yL yR)).2
          · exact lf_of_le_moveLeft (i := Sum.inr b) (IHyr b).2
        · rintro (a | b)
          · exact lf_of_moveRight_le (j := Sum.inl a) (IHxl a (mk yl yr yL yR)).2
          · exact lf_of_moveRight_le (j := Sum.inr b) (IHyl b).2

/-- (3) Negation distributes over the sum, up to equivalence. -/
theorem neg_add_equiv (x y : PGame) : -(x + y) ≈ -x + -y :=
  neg_add_le_both x y

theorem neg_zero : -(0 : PGame) = 0 := by
  show mk PEmpty PEmpty _ _ = mk PEmpty PEmpty _ _
  congr <;> funext i <;> exact i.elim

/-- The game `⋆ = {0 | 0}`. -/
def star : PGame := mk PUnit PUnit (fun _ => 0) (fun _ => 0)

theorem neg_star : -star = star := by
  show mk PUnit PUnit (fun _ => -0) (fun _ => -0) = mk PUnit PUnit (fun _ => 0) (fun _ => 0)
  rw [neg_zero]

/-- (4a) `⋆ + ⋆ ≈ 0`. -/
theorem star_add_star_equiv_zero : star + star ≈ 0 := by
  have h := add_neg_equiv_zero star
  rwa [neg_star] at h

theorem not_zero_lf_zero : ¬ (0 : PGame) ⧏ 0 := by
  rintro (⟨i, -⟩ | ⟨j, -⟩)
  · cases i
  · cases j

theorem not_star_le_zero : ¬ star ≤ 0 :=
  fun h => not_zero_lf_zero ((le_iff.1 h).1 PUnit.unit)

theorem not_zero_le_star : ¬ (0 : PGame) ≤ star :=
  fun h => not_zero_lf_zero ((le_iff.1 h).2 PUnit.unit)

/-- (4b) `⋆` is fuzzy with `0`: whoever moves first wins. -/
theorem star_fuzzy_zero : Fuzzy star 0 :=
  ⟨not_le.1 not_zero_le_star, not_le.1 not_star_le_zero⟩

/-- (4c) `⋆` is not equivalent to `0`. -/
theorem star_not_equiv_zero : ¬ star ≈ 0 :=
  fun h => not_star_le_zero h.1

end PGame

end MirrorStrategyNegationB
