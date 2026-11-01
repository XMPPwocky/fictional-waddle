import Mathlib

/-!
# Swapping the players negates a game

Mathlib v4.35 no longer ships `SetTheory.PGame` / `SetTheory.Game` (the combinatorial game
theory library was moved out of Mathlib into the separate `CombinatorialGames` repository;
`grep PGame` over the v4.35 Mathlib sources returns nothing). This file therefore reproduces
the former Mathlib definitions of `SetTheory.PGame` verbatim in content:

* `PGame.mk α β L R` : Left's moves indexed by `α`, Right's by `β`;
* `x ≤ y ↔ (∀ i, x.moveLeft i ⧏ y) ∧ ∀ j, x ⧏ y.moveRight j`, with `x ⧏ y := ¬ y ≤ x`
  (the former `SetTheory.PGame.le_def` and `SetTheory.PGame.lf_def`, here proved as
  `le_def` and `lf_def` from a simultaneous structural definition of the pair `(≤, ⧏)`,
  as in the former `SetTheory.PGame.leLF`);
* `x ≈ y := x ≤ y ∧ y ≤ x` (the former `SetTheory.PGame.Equiv`);
* `-mk α β L R = mk β α (-R) (-L)` (the former `SetTheory.PGame.neg`);
* `x + y` with left moves `xL i + y` and `x + yL i`, right moves `xR j + y`, `x + yR j`
  (the former `SetTheory.PGame.add`); `x - y := x + -y`;
* `0 = mk PEmpty PEmpty _ _`, `star = mk PUnit PUnit (fun _ => 0) (fun _ => 0)`.

PROVED
* `le_def`, `lf_def` : the recursive characterisations of `≤` and `⧏`
  (former Mathlib `SetTheory.PGame.le_def`, `SetTheory.PGame.lf_def`).
* `le_refl`, `equiv_refl`, `equiv_symm`.
* (1) `neg_neg` : `-(-G) = G` (equality; former `SetTheory.PGame.neg_neg`), and
  `neg_neg_equiv : -(-G) ≈ G`.
* (2) `add_neg_equiv_zero` : `G + -G ≈ 0` for every `G`, and `sub_self_equiv_zero : G - G ≈ 0`
  (former `SetTheory.PGame.add_neg_cancel_equiv`), proved by the copycat strategy: every
  move in one component is answered by the mirrored move in the other component, which
  leads to a smaller game of the form `H + -H` (the induction hypothesis).
* (3) `neg_add` : `-(G + H) = -G + -H` (equality; former `SetTheory.PGame.neg_add`), and
  `neg_add_equiv : -(G + H) ≈ -G + -H`.
* (4) `neg_star : -star = star`, `star_add_star_equiv_zero : star + star ≈ 0`,
  `not_star_equiv_zero : ¬ star ≈ 0`, `star_fuzzy_zero : ¬ star ≤ 0 ∧ ¬ 0 ≤ star`,
  `star_first_player_win : 0 ⧏ star ∧ star ⧏ 0`.

INTERPRETED
* `0 ≤ G` : Left wins `G` when Right moves first; `G ≤ 0` : Right wins when Left moves first.
  `G ≈ 0` : the second player wins. `0 ⧏ G` : Left moving first wins; `G ⧏ 0` : Right moving
  first wins; both together (`star_first_player_win`) : the first player wins.
* Negation swaps the roles of the two players (Left's options become Right's and vice versa,
  recursively). `add_neg_equiv_zero` is the mirror (copycat) strategy for the second player in
  `G - G`.
-/

namespace MirrorStrategyNegationA

universe u

/-- Pre-games, as in the former Mathlib `SetTheory.PGame`. -/
inductive PGame : Type (u + 1)
  | mk : ∀ α β : Type u, (α → PGame) → (β → PGame) → PGame

namespace PGame

/-- Left's moves. -/
def LeftMoves : PGame.{u} → Type u
  | mk l _ _ _ => l

/-- Right's moves. -/
def RightMoves : PGame.{u} → Type u
  | mk _ r _ _ => r

/-- The game after a move by Left. -/
def moveLeft : ∀ g : PGame.{u}, LeftMoves g → PGame.{u}
  | mk _ _ L _ => L

/-- The game after a move by Right. -/
def moveRight : ∀ g : PGame.{u}, RightMoves g → PGame.{u}
  | mk _ _ _ R => R

/-- Simultaneous definition of `(x ≤ y, x ⧏ y)` by recursion on `x` and then on `y`
(the former Mathlib `SetTheory.PGame.leLF`). -/
noncomputable def leLF (x : PGame.{u}) : PGame.{u} → Prop × Prop :=
  PGame.rec (motive := fun _ => PGame.{u} → Prop × Prop)
    (fun _ _ _ _ IHl IHr y =>
      PGame.rec (motive := fun _ => Prop × Prop)
        (fun yl yr yL yR JHl JHr =>
          ((∀ i, (IHl i (mk yl yr yL yR)).2) ∧ ∀ j, (JHr j).2,
            (∃ i, (JHl i).1) ∨ ∃ j, (IHr j (mk yl yr yL yR)).1)) y) x

theorem leLF_fst (x y : PGame.{u}) :
    (leLF x y).1 ↔ (∀ i, (leLF (x.moveLeft i) y).2) ∧ ∀ j, (leLF x (y.moveRight j)).2 := by
  cases x; cases y; exact Iff.rfl

theorem leLF_snd (x y : PGame.{u}) :
    (leLF x y).2 ↔ (∃ i, (leLF x (y.moveLeft i)).1) ∨ ∃ j, (leLF (x.moveRight j) y).1 := by
  cases x; cases y; exact Iff.rfl

noncomputable instance : LE PGame.{u} := ⟨fun x y => (leLF x y).1⟩

/-- `x ⧏ y` : `x` is less or fuzzy with `y`, defined as `¬ y ≤ x`
(the former Mathlib `SetTheory.PGame.LF`). -/
def LF (x y : PGame.{u}) : Prop := ¬ y ≤ x

@[inherit_doc] scoped infix:50 " ⧏ " => LF

/-- The second component of `leLF` is `¬ ≥`. -/
theorem leLF_snd_iff_not (x y : PGame.{u}) :
    ((leLF x y).2 ↔ ¬ (leLF y x).1) ∧ ((leLF y x).2 ↔ ¬ (leLF x y).1) := by
  induction x generalizing y with
  | mk xl xr xL xR IHl IHr =>
    induction y with
    | mk yl yr yL yR JHl JHr =>
      have h1 : ∀ i, (leLF (yL i) (mk xl xr xL xR)).2 ↔ ¬ (leLF (mk xl xr xL xR) (yL i)).1 :=
        fun i => (JHl i).2
      have h2 : ∀ j, (leLF (mk yl yr yL yR) (xR j)).2 ↔ ¬ (leLF (xR j) (mk yl yr yL yR)).1 :=
        fun j => (IHr j _).2
      have h3 : ∀ i, (leLF (xL i) (mk yl yr yL yR)).2 ↔ ¬ (leLF (mk yl yr yL yR) (xL i)).1 :=
        fun i => (IHl i _).1
      have h4 : ∀ j, (leLF (mk xl xr xL xR) (yR j)).2 ↔ ¬ (leLF (yR j) (mk xl xr xL xR)).1 :=
        fun j => (JHr j).1
      constructor
      · rw [leLF_snd, leLF_fst]
        rw [not_and_or, not_forall, not_forall]
        exact or_congr (exists_congr fun i => iff_not_comm.mpr (h1 i))
          (exists_congr fun j => iff_not_comm.mpr (h2 j))
      · rw [leLF_snd, leLF_fst]
        rw [not_and_or, not_forall, not_forall]
        exact or_congr (exists_congr fun i => iff_not_comm.mpr (h3 i))
          (exists_congr fun j => iff_not_comm.mpr (h4 j))

theorem lf_iff_leLF_snd (x y : PGame.{u}) : x ⧏ y ↔ (leLF x y).2 :=
  ((leLF_snd_iff_not x y).1).symm

/-- Former Mathlib `SetTheory.PGame.le_def` (in its `⧏` form). -/
theorem le_def (x y : PGame.{u}) :
    x ≤ y ↔ (∀ i, x.moveLeft i ⧏ y) ∧ ∀ j, x ⧏ y.moveRight j := by
  show (leLF x y).1 ↔ _
  rw [leLF_fst]
  simp only [lf_iff_leLF_snd]

/-- Former Mathlib `SetTheory.PGame.lf_def`. -/
theorem lf_def (x y : PGame.{u}) :
    x ⧏ y ↔ (∃ i, x ≤ y.moveLeft i) ∨ ∃ j, x.moveRight j ≤ y := by
  rw [lf_iff_leLF_snd, leLF_snd]
  rfl

theorem le_refl (x : PGame.{u}) : x ≤ x := by
  induction x with
  | mk l r L R IHl IHr =>
    rw [le_def]
    refine ⟨fun i => ?_, fun j => ?_⟩
    · rw [lf_def]; exact Or.inl ⟨i, IHl i⟩
    · rw [lf_def]; exact Or.inr ⟨j, IHr j⟩

/-- Equivalence of pre-games (former Mathlib `SetTheory.PGame.Equiv`). -/
def Equiv (x y : PGame.{u}) : Prop := x ≤ y ∧ y ≤ x

instance : HasEquiv PGame.{u} := ⟨Equiv⟩

theorem equiv_refl (x : PGame.{u}) : x ≈ x := ⟨le_refl x, le_refl x⟩

theorem equiv_symm {x y : PGame.{u}} (h : x ≈ y) : y ≈ x := ⟨h.2, h.1⟩

/-- The game with no moves. -/
instance : Zero PGame.{u} := ⟨mk PEmpty PEmpty PEmpty.elim PEmpty.elim⟩

/-- Negation: swap the players (former Mathlib `SetTheory.PGame.neg`). -/
def neg : PGame.{u} → PGame.{u}
  | mk l r L R => mk r l (fun j => neg (R j)) (fun i => neg (L i))

instance : Neg PGame.{u} := ⟨neg⟩

theorem neg_mk (l r : Type u) (L : l → PGame.{u}) (R : r → PGame.{u}) :
    -(mk l r L R) = mk r l (fun j => -(R j)) (fun i => -(L i)) := rfl

/-- Sum of games (former Mathlib `SetTheory.PGame.add`), by recursion on `x` then `y`. -/
noncomputable def add (x : PGame.{u}) : PGame.{u} → PGame.{u} :=
  PGame.rec (motive := fun _ => PGame.{u} → PGame.{u})
    (fun xl xr _ _ IHl IHr y =>
      PGame.rec (motive := fun _ => PGame.{u})
        (fun yl yr yL yR JHl JHr =>
          mk (xl ⊕ yl) (xr ⊕ yr)
            (Sum.elim (fun i => IHl i (mk yl yr yL yR)) JHl)
            (Sum.elim (fun j => IHr j (mk yl yr yL yR)) JHr)) y) x

noncomputable instance : Add PGame.{u} := ⟨add⟩

noncomputable instance : Sub PGame.{u} := ⟨fun x y => x + -y⟩

theorem add_mk (xl xr yl yr : Type u) (xL : xl → PGame.{u}) (xR : xr → PGame.{u})
    (yL : yl → PGame.{u}) (yR : yr → PGame.{u}) :
    mk xl xr xL xR + mk yl yr yL yR =
      mk (xl ⊕ yl) (xr ⊕ yr)
        (Sum.elim (fun i => xL i + mk yl yr yL yR) (fun i => mk xl xr xL xR + yL i))
        (Sum.elim (fun j => xR j + mk yl yr yL yR) (fun j => mk xl xr xL xR + yR j)) := rfl

theorem sub_def (x y : PGame.{u}) : x - y = x + -y := rfl

/-! ### Moves in a sum -/

theorem lf_add_of_le_moveLeft_left {x y z : PGame.{u}} (i : x.LeftMoves)
    (h : z ≤ x.moveLeft i + y) : z ⧏ x + y := by
  cases x; cases y
  rw [lf_def]; exact Or.inl ⟨Sum.inl i, h⟩

theorem lf_add_of_le_moveLeft_right {x y z : PGame.{u}} (i : y.LeftMoves)
    (h : z ≤ x + y.moveLeft i) : z ⧏ x + y := by
  cases x; cases y
  rw [lf_def]; exact Or.inl ⟨Sum.inr i, h⟩

theorem add_lf_of_moveRight_left_le {x y z : PGame.{u}} (j : x.RightMoves)
    (h : x.moveRight j + y ≤ z) : x + y ⧏ z := by
  cases x; cases y
  rw [lf_def]; exact Or.inr ⟨Sum.inl j, h⟩

theorem add_lf_of_moveRight_right_le {x y z : PGame.{u}} (j : y.RightMoves)
    (h : x + y.moveRight j ≤ z) : x + y ⧏ z := by
  cases x; cases y
  rw [lf_def]; exact Or.inr ⟨Sum.inr j, h⟩

theorem add_le_of {x y z : PGame.{u}}
    (h1 : ∀ i, x.moveLeft i + y ⧏ z) (h2 : ∀ i, x + y.moveLeft i ⧏ z)
    (h3 : ∀ j, x + y ⧏ z.moveRight j) : x + y ≤ z := by
  cases x; cases y
  rw [le_def]
  refine ⟨?_, h3⟩
  rintro (i | i)
  · exact h1 i
  · exact h2 i

theorem le_add_of {x y z : PGame.{u}}
    (h1 : ∀ i, z.moveLeft i ⧏ x + y) (h2 : ∀ j, z ⧏ x.moveRight j + y)
    (h3 : ∀ j, z ⧏ x + y.moveRight j) : z ≤ x + y := by
  cases x; cases y
  rw [le_def]
  refine ⟨h1, ?_⟩
  rintro (j | j)
  · exact h2 j
  · exact h3 j

/-! ### (1) Negation is an involution -/

theorem neg_neg (x : PGame.{u}) : -(-x) = x := by
  induction x with
  | mk l r L R IHl IHr =>
    rw [neg_mk, neg_mk]
    congr
    · funext i; exact IHl i
    · funext j; exact IHr j

theorem neg_neg_equiv (x : PGame.{u}) : -(-x) ≈ x := by
  rw [neg_neg]; exact equiv_refl x

/-! ### (2) The mirror (copycat) strategy: `G + -G ≈ 0` -/

theorem add_neg_le_zero_and_zero_le (x : PGame.{u}) : x + -x ≤ 0 ∧ 0 ≤ x + -x := by
  induction x with
  | mk l r L R IHl IHr =>
    constructor
    · refine add_le_of (fun i => ?_) (fun j => ?_) (fun j => PEmpty.elim j)
      · -- Left moved to `L i` in the first component; Right copies in the second.
        exact add_lf_of_moveRight_right_le (y := -(mk l r L R)) i (IHl i).1
      · -- Left moved to `-(R j)` in the second component; Right copies in the first.
        exact add_lf_of_moveRight_left_le (x := mk l r L R) j (IHr j).1
    · refine le_add_of (fun i => PEmpty.elim i) (fun j => ?_) (fun i => ?_)
      · -- Right moved to `R j` in the first component; Left copies in the second.
        exact lf_add_of_le_moveLeft_right (y := -(mk l r L R)) j (IHr j).2
      · -- Right moved to `-(L i)` in the second component; Left copies in the first.
        exact lf_add_of_le_moveLeft_left (x := mk l r L R) i (IHl i).2

theorem add_neg_equiv_zero (x : PGame.{u}) : x + -x ≈ 0 :=
  add_neg_le_zero_and_zero_le x

theorem sub_self_equiv_zero (x : PGame.{u}) : x - x ≈ 0 :=
  add_neg_equiv_zero x

/-! ### (3) Negation distributes over sums -/

theorem neg_add (x y : PGame.{u}) : -(x + y) = -x + -y := by
  induction x generalizing y with
  | mk xl xr xL xR IHl IHr =>
    induction y with
    | mk yl yr yL yR JHl JHr =>
      rw [add_mk, neg_mk, neg_mk, neg_mk, add_mk]
      congr
      · funext s
        rcases s with j | j
        · exact IHr j _
        · exact JHr j
      · funext s
        rcases s with i | i
        · exact IHl i _
        · exact JHl i

theorem neg_add_equiv (x y : PGame.{u}) : -(x + y) ≈ -x + -y := by
  rw [neg_add]; exact equiv_refl _

/-! ### (4) Star -/

/-- `star = {0 | 0}`. -/
def star : PGame.{u} := mk PUnit PUnit (fun _ => 0) (fun _ => 0)

theorem neg_zero : -(0 : PGame.{u}) = 0 := by
  show mk PEmpty PEmpty _ _ = mk PEmpty PEmpty _ _
  congr <;> funext i <;> exact PEmpty.elim i

theorem neg_star : -star.{u} = star.{u} := by
  show mk PUnit PUnit (fun _ => -0) (fun _ => -0) = mk PUnit PUnit (fun _ => 0) (fun _ => 0)
  rw [neg_zero]

theorem star_add_star_equiv_zero : star.{u} + star.{u} ≈ 0 := by
  have h := add_neg_equiv_zero star.{u}
  rwa [neg_star] at h

theorem not_zero_lf_zero : ¬ (0 : PGame.{u}) ⧏ 0 := by
  rw [lf_def]
  rintro (⟨i, _⟩ | ⟨j, _⟩)
  · exact PEmpty.elim i
  · exact PEmpty.elim j

theorem star_first_player_win : (0 : PGame.{u}) ⧏ star ∧ star ⧏ (0 : PGame.{u}) := by
  constructor
  · rw [lf_def]; exact Or.inl ⟨PUnit.unit, le_refl 0⟩
  · rw [lf_def]; exact Or.inr ⟨PUnit.unit, le_refl 0⟩

theorem star_fuzzy_zero : ¬ star.{u} ≤ 0 ∧ ¬ (0 : PGame.{u}) ≤ star := by
  exact ⟨star_first_player_win.1, star_first_player_win.2⟩

theorem not_star_equiv_zero : ¬ star.{u} ≈ 0 := fun h => star_fuzzy_zero.1 h.1

end PGame

end MirrorStrategyNegationA
