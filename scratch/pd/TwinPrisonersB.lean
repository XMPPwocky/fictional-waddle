import Mathlib

/-!
# One-shot prisoner's dilemma, the twin variant, and the CoCo diagonal

Payoffs `T > R > P > S` (temptation, reward, punishment, sucker).
Row player's payoff `u₁ a b`; column player's payoff `u₂ a b = u₁ b a`.

PROVED
* `defect_strictly_dominates` : for every opponent action `b`, `u₁ D b > u₁ C b`
  (uses `T > R` and `P > S`).
* `defect_strictly_dominates_col` : the same for the column player.
* `isNash_iff` : a pure profile `(a, b)` is a Nash equilibrium iff `a = D ∧ b = D`
  (so `(D, D)` is the unique pure Nash equilibrium).
* `twin_outcome_diagonal` : under the copy constraint `b = a`, the realised outcome lies
  in `{(C,C), (D,D)}`.
* `twin_payoff_le` / `twin_argmax_iff` / `twin_isGreatest` : `a ↦ u₁ a a` is maximised
  exactly at `a = C`, with maximum value `R`, and `u₁ C C = R > P = u₁ D D`.
* `coco_zero_sum_diag` : for any symmetric two-player game on any action type
  (`u₂ a b = u₁ b a`), the zero-sum CoCo component `(u₁ a a − u₂ a a)/2` is `0`.
* `pd_coco_zero_sum_diag` : the PD instance of the previous item.

INTERPRETED
* "Unique Nash equilibrium" is read over pure strategy profiles.
* "Against an exact copy" is modelled as the constraint `b = a` on the opponent's action,
  so the twin's objective is `a ↦ u₁ a a`; "cooperation is optimal" is the statement that
  `C` is the unique maximiser of this function.
* Only `T > R`, `R > P`, `P > S` are assumed; `2R > T + S` is not used.
-/

namespace TwinPrisonersB

/-- Actions: cooperate or defect. -/
inductive Act
  | C
  | D
  deriving DecidableEq, Repr

open Act

/-- Payoff parameters with the prisoner's dilemma ordering `T > R > P > S`. -/
structure PD where
  T : ℝ
  R : ℝ
  P : ℝ
  S : ℝ
  hTR : R < T
  hRP : P < R
  hPS : S < P

variable (g : PD)

/-- Row player's payoff when row plays `a` and column plays `b`. -/
def u₁ : Act → Act → ℝ
  | C, C => g.R
  | C, D => g.S
  | D, C => g.T
  | D, D => g.P

/-- Column player's payoff, by symmetry: `u₂ a b = u₁ b a`. -/
def u₂ (a b : Act) : ℝ := u₁ g b a

/-- (1) Defection strictly dominates cooperation for the row player. -/
theorem defect_strictly_dominates (b : Act) : u₁ g C b < u₁ g D b := by
  cases b
  · simpa [u₁] using g.hTR
  · simpa [u₁] using g.hPS

/-- (1') Defection strictly dominates cooperation for the column player. -/
theorem defect_strictly_dominates_col (a : Act) : u₂ g a C < u₂ g a D := by
  simpa [u₂] using defect_strictly_dominates g a

/-- Pure-strategy Nash equilibrium: no unilateral deviation is profitable. -/
def IsNash (a b : Act) : Prop :=
  (∀ a' : Act, u₁ g a' b ≤ u₁ g a b) ∧ (∀ b' : Act, u₂ g a b' ≤ u₂ g a b)

/-- (2) `(D, D)` is the unique pure Nash equilibrium. -/
theorem isNash_iff (a b : Act) : IsNash g a b ↔ a = D ∧ b = D := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · cases a
      · exact absurd (h₁ D) (not_le.mpr (defect_strictly_dominates g b))
      · rfl
    · cases b
      · exact absurd (h₂ D) (not_le.mpr (defect_strictly_dominates_col g a))
      · rfl
  · rintro ⟨rfl, rfl⟩
    refine ⟨fun a' => ?_, fun b' => ?_⟩
    · cases a'
      · exact (defect_strictly_dominates g D).le
      · exact le_rfl
    · cases b'
      · exact (defect_strictly_dominates_col g D).le
      · exact le_rfl

theorem dd_isNash : IsNash g D D := (isNash_iff g D D).mpr ⟨rfl, rfl⟩

theorem nash_unique (a b : Act) (h : IsNash g a b) : (a, b) = (D, D) := by
  obtain ⟨rfl, rfl⟩ := (isNash_iff g a b).mp h
  rfl

/-- (3a) Against an exact copy (`b = a`) only `(C,C)` and `(D,D)` can occur. -/
theorem twin_outcome_diagonal (a b : Act) (hcopy : b = a) :
    (a, b) = (C, C) ∨ (a, b) = (D, D) := by
  rw [hcopy]
  cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem twin_C_payoff : u₁ g C C = g.R := rfl

theorem twin_D_payoff : u₁ g D D = g.P := rfl

theorem twin_C_beats_D : u₁ g D D < u₁ g C C := g.hRP

/-- (3b) `C` maximises `a ↦ u₁ a a`. -/
theorem twin_payoff_le (a : Act) : u₁ g a a ≤ u₁ g C C := by
  cases a
  · exact le_rfl
  · exact (twin_C_beats_D g).le

/-- (3c) `a` maximises `a ↦ u₁ a a` iff `a = C`. -/
theorem twin_argmax_iff (a : Act) : (∀ a' : Act, u₁ g a' a' ≤ u₁ g a a) ↔ a = C := by
  constructor
  · intro h
    cases a
    · rfl
    · exact absurd (h C) (not_le.mpr (twin_C_beats_D g))
  · rintro rfl
    exact twin_payoff_le g

/-- (3d) The maximum of `a ↦ u₁ a a` is `R`, attained at `C`. -/
theorem twin_isGreatest : IsGreatest (Set.range fun a : Act => u₁ g a a) g.R :=
  ⟨⟨C, rfl⟩, by
    rintro _ ⟨a, rfl⟩
    exact twin_payoff_le g a⟩

/-- CoCo cooperative component `(u₁ + u₂)/2` of a two-player game. -/
noncomputable def cocoCoop {A : Type*} (v₁ v₂ : A → A → ℝ) (a b : A) : ℝ := (v₁ a b + v₂ a b) / 2

/-- CoCo zero-sum (competitive) component `(u₁ − u₂)/2` of a two-player game. -/
noncomputable def cocoZeroSum {A : Type*} (v₁ v₂ : A → A → ℝ) (a b : A) : ℝ := (v₁ a b - v₂ a b) / 2

theorem coco_decomp {A : Type*} (v₁ v₂ : A → A → ℝ) (a b : A) :
    v₁ a b = cocoCoop v₁ v₂ a b + cocoZeroSum v₁ v₂ a b ∧
      v₂ a b = cocoCoop v₁ v₂ a b - cocoZeroSum v₁ v₂ a b := by
  unfold cocoCoop cocoZeroSum
  constructor <;> ring

/-- (4) In a symmetric game the CoCo zero-sum part vanishes on the diagonal. -/
theorem coco_zero_sum_diag {A : Type*} (v₁ v₂ : A → A → ℝ)
    (hsym : ∀ a b, v₂ a b = v₁ b a) (a : A) :
    (v₁ a a - v₂ a a) / 2 = 0 := by
  rw [hsym a a, sub_self, zero_div]

/-- (4') The PD instance. -/
theorem pd_coco_zero_sum_diag (a : Act) : cocoZeroSum (u₁ g) (u₂ g) a a = 0 :=
  coco_zero_sum_diag (u₁ g) (u₂ g) (fun _ _ => rfl) a

end TwinPrisonersB
