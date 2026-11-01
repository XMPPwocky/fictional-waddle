import Mathlib

/-!
# PlannerDiagonalB

PROVED
* `diagonal_ne_plan`: for any `plan : A → A → Bool`, the profile
  `diagonal plan x = !(plan x x)` differs from `plan a` for every `a`.
* `diagonal_not_mem_range`: `diagonal plan ∉ Set.range plan`.
* `no_surjective_plan`: no `plan : A → (A → Bool)` is surjective.
* `not_exists_surjective_plan`: `¬ ∃ plan : A → (A → Bool), Function.Surjective plan`.
* `card_profiles`: for finite `A`, `Fintype.card (A → Bool) = 2 ^ Fintype.card A`.
* `card_agents_lt_card_profiles`: for finite `A`,
  `Fintype.card A < Fintype.card (A → Bool)`.
* `card_agents_lt_two_pow`: `Fintype.card A < 2 ^ Fintype.card A`.

INTERPRETED
A plan indexed by its own society (one predicted profile per agent) cannot
anticipate every policy profile the society can adopt: the diagonal profile,
in which each agent does the opposite of what its own indexed plan predicts
for it, is never predicted. Hence some unanticipated (pluralist) behaviour is
always available. This is Cantor's diagonal argument; no claim about
bargaining, equilibrium, or division algebras is formalized here.
-/

namespace PlannerDiagonalB

variable {A : Type*}

/-- The diagonal profile: agent `x` does the opposite of what plan `x` predicts for `x`. -/
def diagonal (plan : A → A → Bool) : A → Bool := fun x => !(plan x x)

theorem diagonal_ne_plan (plan : A → A → Bool) (a : A) : diagonal plan ≠ plan a := by
  intro h
  have h' := congrFun h a
  simp [diagonal] at h'

theorem diagonal_not_mem_range (plan : A → A → Bool) :
    diagonal plan ∉ Set.range plan := by
  rintro ⟨a, ha⟩
  exact diagonal_ne_plan plan a ha.symm

theorem no_surjective_plan (plan : A → (A → Bool)) : ¬ Function.Surjective plan := by
  intro hs
  obtain ⟨a, ha⟩ := hs (diagonal plan)
  exact diagonal_ne_plan plan a ha.symm

theorem not_exists_surjective_plan : ¬ ∃ plan : A → (A → Bool), Function.Surjective plan := by
  rintro ⟨plan, hs⟩
  exact no_surjective_plan plan hs

theorem card_profiles [Fintype A] [DecidableEq A] :
    Fintype.card (A → Bool) = 2 ^ Fintype.card A := by
  simp

theorem card_agents_lt_two_pow [Fintype A] : Fintype.card A < 2 ^ Fintype.card A :=
  Nat.lt_two_pow_self

theorem card_agents_lt_card_profiles [Fintype A] [DecidableEq A] :
    Fintype.card A < Fintype.card (A → Bool) := by
  rw [card_profiles]
  exact card_agents_lt_two_pow

end PlannerDiagonalB
