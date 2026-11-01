import Mathlib

/-!
# Mutual-reading programs: diagonal collapse and symmetric 2x2 classification

PROVED:
* `and_self_diag`, `or_self_diag`: for every `x : Bool`, `(x && x) = x` and `(x || x) = x`.
  Against an exact copy (both players output the same bit `x`), the AND game and the OR game
  outcome is the player's own bit, so the game reduces to a single-player choice of `x`.
* `diag_and_game`, `diag_or_game`: for any payoff `f : Bool → ℝ` on gate outputs, the payoff of
  choosing `x` against a copy is `f x`; `diag_and_best`, `diag_or_best`: against a copy the best attainable value is
  `max (f false) (f true)`, and it is attained.
* `isNash_iff_pd`: Prisoner's Dilemma (`T > R > P > S`): a pure profile is Nash iff it is `(D,D)`.
* `isNash_iff_stagHunt`: Stag Hunt (`R > T > P > S`): Nash iff `(C,C)` or `(D,D)`.
* `isNash_iff_chicken`: Chicken (`T > R > S > P`): Nash iff `(C,D)` or `(D,C)`.
* `isNash_iff_harmony`: Harmony (`R > T`, `S > P`): Nash iff `(C,C)`.
  The `*_nashSet` versions state the same as equalities of `Finset`s of profiles.
  In the PD, Stag Hunt and Chicken cases the middle inequality (`R > P`, `T > P`, `R > S`
  respectively) is part of the hypotheses as stated but is not needed for the classification.
* `prog_nash_cic`, `prog_nash_ad`: in the program game (CIC cooperates iff the opponent is CIC,
  AD always defects; payoff `R` at `(CIC,CIC)` and `P` elsewhere) with `R > P`, both
  `(CIC,CIC)` and `(AD,AD)` are pure Nash equilibria.
* `prog_nash_iff`: with `R > P` the pure Nash equilibria of the program game are exactly
  `(CIC,CIC)` and `(AD,AD)`.
* `prog_paretoOptimal_iff`: with `R > P`, a profile is Pareto-optimal (among all profiles)
  iff it is `(CIC,CIC)`.
* `prog_unique_pareto_nash`: with `R > P`, `(CIC,CIC)` is a Nash equilibrium that is
  Pareto-optimal, every Nash equilibrium that is Pareto-optimal equals `(CIC,CIC)`, and every
  Nash equilibrium that is not Pareto-dominated by another Nash equilibrium equals `(CIC,CIC)`.

INTERPRETED (not formalized):
* The phrase "the AND/OR gate game reduces to a single-player choice" is formalized only as the
  payoff identity `f (x && x) = f x` (resp. `||`); no general notion of game reduction is defined.
* Programs CIC and AD are modelled as two abstract actions with the stated outcome table; the
  semantics of programs reading each other's source is not formalized.
-/

namespace MutualReadingGames2x2

/-! ## (1) Diagonal collapse -/

theorem and_self_diag (x : Bool) : (x && x) = x := by cases x <;> rfl

theorem or_self_diag (x : Bool) : (x || x) = x := by cases x <;> rfl

theorem diag_and_game (f : Bool → ℝ) (x : Bool) : f (x && x) = f x := by
  rw [and_self_diag]

theorem diag_or_game (f : Bool → ℝ) (x : Bool) : f (x || x) = f x := by
  rw [or_self_diag]

theorem diag_and_best (f : Bool → ℝ) :
    (∀ x : Bool, f (x && x) ≤ max (f false) (f true)) ∧
      ∃ x : Bool, f (x && x) = max (f false) (f true) := by
  simp only [and_self_diag]
  refine ⟨fun x => ?_, ?_⟩
  · cases x
    · exact le_max_left _ _
    · exact le_max_right _ _
  · rcases le_total (f false) (f true) with h | h
    · exact ⟨true, (max_eq_right h).symm⟩
    · exact ⟨false, (max_eq_left h).symm⟩

theorem diag_or_best (f : Bool → ℝ) :
    (∀ x : Bool, f (x || x) ≤ max (f false) (f true)) ∧
      ∃ x : Bool, f (x || x) = max (f false) (f true) := by
  simp only [or_self_diag]
  refine ⟨fun x => ?_, ?_⟩
  · cases x
    · exact le_max_left _ _
    · exact le_max_right _ _
  · rcases le_total (f false) (f true) with h | h
    · exact ⟨true, (max_eq_right h).symm⟩
    · exact ⟨false, (max_eq_left h).symm⟩

/-! ## (2) Symmetric 2x2 games -/

/-- Closes a goal `(A ∧ B) ∧ (C ∧ D) ↔ E` with linear facts in context, where `E` is a
disjunction of equalities between concrete constructor pairs. -/
macro "nashcases" : tactic => `(tactic| (
  constructor
  · intro h
    first
      | (simp; done)
      | (obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h; exfalso; linarith)
  · intro h
    first
      | (simp at h; done)
      | (refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)))

inductive Act
  | C
  | D
  deriving DecidableEq, Repr

open Act

instance : Fintype Act := ⟨{C, D}, by intro x; cases x <;> simp⟩

/-- Row payoff of the symmetric 2x2 game with parameters `R S T P`. -/
def u (R S T P : ℝ) : Act → Act → ℝ
  | C, C => R
  | C, D => S
  | D, C => T
  | D, D => P

/-- Pure Nash equilibrium: row `a` is a best response to `b` and column `b` is a best
response to `a` (column payoff is `u` with roles swapped). -/
def IsNash (R S T P : ℝ) (a b : Act) : Prop :=
  (∀ a', u R S T P a' b ≤ u R S T P a b) ∧ (∀ b', u R S T P b' a ≤ u R S T P b a)

theorem isNash_iff_explicit (R S T P : ℝ) (a b : Act) :
    IsNash R S T P a b ↔
      (u R S T P C b ≤ u R S T P a b ∧ u R S T P D b ≤ u R S T P a b) ∧
      (u R S T P C a ≤ u R S T P b a ∧ u R S T P D a ≤ u R S T P b a) := by
  unfold IsNash
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1 C, h1 D⟩, ⟨h2 C, h2 D⟩⟩
  · rintro ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩⟩
    refine ⟨fun a' => ?_, fun b' => ?_⟩
    · cases a' <;> assumption
    · cases b' <;> assumption

open Classical in
/-- The set of pure Nash equilibria as a `Finset` of profiles. -/
noncomputable def nashSet (R S T P : ℝ) : Finset (Act × Act) :=
  Finset.univ.filter (fun p => IsNash R S T P p.1 p.2)

theorem mem_nashSet (R S T P : ℝ) (p : Act × Act) :
    p ∈ nashSet R S T P ↔ IsNash R S T P p.1 p.2 := by
  simp [nashSet]

theorem isNash_iff_pd {R S T P : ℝ} (hTR : T > R) (_hRP : R > P) (hPS : P > S) (a b : Act) :
    IsNash R S T P a b ↔ (a, b) = (D, D) := by
  rw [isNash_iff_explicit]
  cases a <;> cases b <;> simp only [u] <;> nashcases

theorem isNash_iff_stagHunt {R S T P : ℝ} (hRT : R > T) (_hTP : T > P) (hPS : P > S)
    (a b : Act) :
    IsNash R S T P a b ↔ (a, b) = (C, C) ∨ (a, b) = (D, D) := by
  rw [isNash_iff_explicit]
  cases a <;> cases b <;> simp only [u] <;> nashcases

theorem isNash_iff_chicken {R S T P : ℝ} (hTR : T > R) (_hRS : R > S) (hSP : S > P)
    (a b : Act) :
    IsNash R S T P a b ↔ (a, b) = (C, D) ∨ (a, b) = (D, C) := by
  rw [isNash_iff_explicit]
  cases a <;> cases b <;> simp only [u] <;> nashcases

theorem isNash_iff_harmony {R S T P : ℝ} (hRT : R > T) (hSP : S > P) (a b : Act) :
    IsNash R S T P a b ↔ (a, b) = (C, C) := by
  rw [isNash_iff_explicit]
  cases a <;> cases b <;> simp only [u] <;> nashcases

theorem pd_nashSet {R S T P : ℝ} (hTR : T > R) (hRP : R > P) (hPS : P > S) :
    nashSet R S T P = {(D, D)} := by
  ext ⟨a, b⟩
  rw [mem_nashSet, isNash_iff_pd hTR hRP hPS, Finset.mem_singleton]

theorem stagHunt_nashSet {R S T P : ℝ} (hRT : R > T) (hTP : T > P) (hPS : P > S) :
    nashSet R S T P = {(C, C), (D, D)} := by
  ext ⟨a, b⟩
  rw [mem_nashSet, isNash_iff_stagHunt hRT hTP hPS, Finset.mem_insert, Finset.mem_singleton]

theorem chicken_nashSet {R S T P : ℝ} (hTR : T > R) (hRS : R > S) (hSP : S > P) :
    nashSet R S T P = {(C, D), (D, C)} := by
  ext ⟨a, b⟩
  rw [mem_nashSet, isNash_iff_chicken hTR hRS hSP, Finset.mem_insert, Finset.mem_singleton]

theorem harmony_nashSet {R S T P : ℝ} (hRT : R > T) (hSP : S > P) :
    nashSet R S T P = {(C, C)} := by
  ext ⟨a, b⟩
  rw [mem_nashSet, isNash_iff_harmony hRT hSP, Finset.mem_singleton]

/-! ## (3) Program game with CIC and AD -/

inductive Prog
  | CIC
  | AD
  deriving DecidableEq, Repr

open Prog

/-- Row payoff of the program game: `R` when both run CIC, `P` otherwise. -/
def pay (R P : ℝ) : Prog → Prog → ℝ
  | CIC, CIC => R
  | CIC, AD => P
  | AD, CIC => P
  | AD, AD => P

/-- Pure Nash equilibrium of the symmetric program game. -/
def ProgNash (R P : ℝ) (p q : Prog) : Prop :=
  (∀ p', pay R P p' q ≤ pay R P p q) ∧ (∀ q', pay R P q' p ≤ pay R P q p)

/-- `(p', q')` Pareto-dominates `(p, q)`: both weakly better, one strictly. -/
def ParetoDom (R P : ℝ) (p' q' p q : Prog) : Prop :=
  pay R P p q ≤ pay R P p' q' ∧ pay R P q p ≤ pay R P q' p' ∧
    (pay R P p q < pay R P p' q' ∨ pay R P q p < pay R P q' p')

/-- Pareto-optimal among all profiles. -/
def ParetoOptimal (R P : ℝ) (p q : Prog) : Prop :=
  ∀ p' q', ¬ ParetoDom R P p' q' p q

theorem progNash_iff_explicit (R P : ℝ) (p q : Prog) :
    ProgNash R P p q ↔
      (pay R P CIC q ≤ pay R P p q ∧ pay R P AD q ≤ pay R P p q) ∧
      (pay R P CIC p ≤ pay R P q p ∧ pay R P AD p ≤ pay R P q p) := by
  unfold ProgNash
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1 CIC, h1 AD⟩, ⟨h2 CIC, h2 AD⟩⟩
  · rintro ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩⟩
    refine ⟨fun p' => ?_, fun q' => ?_⟩
    · cases p' <;> assumption
    · cases q' <;> assumption

theorem prog_nash_iff {R P : ℝ} (hRP : R > P) (p q : Prog) :
    ProgNash R P p q ↔ (p, q) = (CIC, CIC) ∨ (p, q) = (AD, AD) := by
  rw [progNash_iff_explicit]
  cases p <;> cases q <;> simp only [pay] <;> nashcases

theorem prog_nash_cic {R P : ℝ} (hRP : R > P) : ProgNash R P CIC CIC :=
  (prog_nash_iff hRP CIC CIC).2 (Or.inl rfl)

theorem prog_nash_ad {R P : ℝ} (hRP : R > P) : ProgNash R P AD AD :=
  (prog_nash_iff hRP AD AD).2 (Or.inr rfl)

theorem prog_paretoOptimal_iff {R P : ℝ} (hRP : R > P) (p q : Prog) :
    ParetoOptimal R P p q ↔ (p, q) = (CIC, CIC) := by
  constructor
  · intro h
    by_contra hne
    apply h CIC CIC
    cases p <;> cases q <;> simp_all [ParetoDom, pay] <;> exact le_of_lt hRP
  · intro h p' q' hd
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold ParetoDom at hd
    cases p' <;> cases q' <;> simp [pay] at hd <;> linarith [hd.1]

theorem prog_unique_pareto_nash {R P : ℝ} (hRP : R > P) :
    (ProgNash R P CIC CIC ∧ ParetoOptimal R P CIC CIC) ∧
    (∀ p q, ProgNash R P p q → ParetoOptimal R P p q → (p, q) = (CIC, CIC)) ∧
    (∀ p q, ProgNash R P p q →
      (∀ p' q', ProgNash R P p' q' → ¬ ParetoDom R P p' q' p q) → (p, q) = (CIC, CIC)) := by
  refine ⟨⟨prog_nash_cic hRP, (prog_paretoOptimal_iff hRP CIC CIC).2 rfl⟩, ?_, ?_⟩
  · intro p q _ hpo
    exact (prog_paretoOptimal_iff hRP p q).1 hpo
  · intro p q hn hnd
    rcases (prog_nash_iff hRP p q).1 hn with h | h
    · exact h
    · exfalso
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      apply hnd CIC CIC (prog_nash_cic hRP)
      simp only [ParetoDom, pay]
      exact ⟨le_of_lt hRP, le_of_lt hRP, Or.inl hRP⟩

end MutualReadingGames2x2
