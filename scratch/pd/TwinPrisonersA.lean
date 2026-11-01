import Mathlib

/-!
# One-shot prisoner's dilemma, the twin variant, and the CoCo diagonal

Payoffs `T > R > P > S`. Row player's payoff `pay a b` (own action `a`, opponent `b`):
`pay C C = R`, `pay C D = S`, `pay D C = T`, `pay D D = P`.
The column player's payoff is `pay₂ a b = pay b a` (symmetric game).

PROVED
* `defect_strictly_dominates`: for every opponent action `b`, `pay D b > pay C b`.
* `nash_iff`: a profile `(a, b)` is a pure Nash equilibrium iff `(a, b) = (D, D)`.
* `existsUnique_nash`: there is exactly one pure Nash equilibrium profile.
* `copyOutcomes_eq`: the outcomes reachable against an exact copy (profiles with equal
  actions) are exactly `{(C, C), (D, D)}`.
* `twin_argmax`: `C` maximizes `a ↦ pay a a`, and it is the unique maximizer.
* `twin_payoff_C_gt_D`: `pay C C > pay D D` (i.e. `R > P`).
* `coco_zeroSum_diag`: for any symmetric two-player game `u₂ a b = u₁ b a` on any action
  type, the CoCo zero-sum part `(u₁ a a - u₂ a a) / 2` vanishes.
* `coco_coop_diag`: on the diagonal the CoCo cooperative part `(u₁ a a + u₂ a a) / 2`
  equals `u₁ a a`.

INTERPRETED
* "Unique Nash equilibrium" is taken over pure profiles: `(a, b)` with no profitable
  unilateral deviation for either player.
* "Exact copy guaranteed to make the same choice" is modelled by restricting outcomes to the
  diagonal `{p | p.1 = p.2}`; the twin's decision problem is then `max_a pay a a`.
* Only `R > P` is used in (3); only `T > R` and `P > S` are used in (1)-(2).
-/

namespace TwinPrisonersA

inductive Act
  | C
  | D
  deriving DecidableEq, Repr

open Act

/-- Payoff parameters with `T > R > P > S`. -/
structure PD where
  T : ℝ
  R : ℝ
  P : ℝ
  S : ℝ
  hTR : R < T
  hRP : P < R
  hPS : S < P

variable (g : PD)

/-- Row player's payoff for own action `a` against opponent action `b`. -/
def pay : Act → Act → ℝ
  | C, C => g.R
  | C, D => g.S
  | D, C => g.T
  | D, D => g.P

/-- Column player's payoff in the symmetric game. -/
def pay₂ (a b : Act) : ℝ := pay g b a

/-- (1) Defection strictly dominates cooperation. -/
theorem defect_strictly_dominates (b : Act) : pay g C b < pay g D b := by
  cases b
  · exact g.hTR
  · exact g.hPS

/-- Pure Nash equilibrium: no profitable unilateral deviation for either player. -/
def IsNash (a b : Act) : Prop :=
  (∀ a' : Act, pay g a' b ≤ pay g a b) ∧ (∀ b' : Act, pay₂ g a b' ≤ pay₂ g a b)

/-- (2) `(a, b)` is a Nash equilibrium iff it is `(D, D)`. -/
theorem nash_iff (a b : Act) : IsNash g a b ↔ a = D ∧ b = D := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · cases a
      · exact absurd (h1 D) (not_le.mpr (defect_strictly_dominates g b))
      · rfl
    · cases b
      · exact absurd (h2 D) (not_le.mpr (defect_strictly_dominates g a))
      · rfl
  · rintro ⟨rfl, rfl⟩
    refine ⟨fun a' => ?_, fun b' => ?_⟩
    · cases a'
      · exact le_of_lt (defect_strictly_dominates g D)
      · exact le_rfl
    · cases b'
      · exact le_of_lt (defect_strictly_dominates g D)
      · exact le_rfl

/-- (2) The pure Nash equilibrium exists and is unique. -/
theorem existsUnique_nash : ∃! p : Act × Act, IsNash g p.1 p.2 := by
  refine ⟨(D, D), (nash_iff g D D).mpr ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨a, b⟩ h
  obtain ⟨rfl, rfl⟩ := (nash_iff g a b).mp h
  rfl

/-- Outcomes possible against an exact copy: both players choose the same action. -/
def copyOutcomes : Set (Act × Act) := {p | p.1 = p.2}

/-- (3) Against an exact copy only `(C, C)` and `(D, D)` can occur. -/
theorem copyOutcomes_eq : copyOutcomes = {(C, C), (D, D)} := by
  ext ⟨a, b⟩
  cases a <;> cases b <;> simp [copyOutcomes]

/-- (3) Cooperation beats defection on the diagonal: `R > P`. -/
theorem twin_payoff_C_gt_D : pay g D D < pay g C C := g.hRP

/-- (3) `C` maximizes `a ↦ pay a a`, uniquely. -/
theorem twin_argmax :
    (∀ a : Act, pay g a a ≤ pay g C C) ∧
      ∀ a : Act, (∀ a' : Act, pay g a' a' ≤ pay g a a) → a = C := by
  refine ⟨fun a => ?_, fun a h => ?_⟩
  · cases a
    · exact le_rfl
    · exact le_of_lt (twin_payoff_C_gt_D g)
  · cases a
    · rfl
    · exact absurd (h C) (not_le.mpr (twin_payoff_C_gt_D g))

/-- (4) The CoCo zero-sum part of a symmetric game vanishes on the diagonal. -/
theorem coco_zeroSum_diag {A : Type*} (u₁ u₂ : A → A → ℝ)
    (hsym : ∀ a b, u₂ a b = u₁ b a) (a : A) :
    (u₁ a a - u₂ a a) / 2 = 0 := by
  rw [hsym]; ring

/-- On the diagonal the CoCo cooperative part of a symmetric game equals `u₁ a a`. -/
theorem coco_coop_diag {A : Type*} (u₁ u₂ : A → A → ℝ)
    (hsym : ∀ a b, u₂ a b = u₁ b a) (a : A) :
    (u₁ a a + u₂ a a) / 2 = u₁ a a := by
  rw [hsym]; ring

/-- (4) instantiated for the prisoner's dilemma. -/
theorem coco_zeroSum_diag_pd (a : Act) : (pay g a a - pay₂ g a a) / 2 = 0 :=
  coco_zeroSum_diag (pay g) (pay₂ g) (fun _ _ => rfl) a

end TwinPrisonersA
