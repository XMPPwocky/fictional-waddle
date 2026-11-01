import Mathlib

/-!
# No complete central plan (Cantor diagonal)

A planner is a map `plan : A → (A → Bool)`: the plan indexed by agent `a` predicts,
for every agent `x`, the Boolean policy `plan a x`.

PROVED
* `diag_ne_plan` : the diagonal profile `d x = !(plan x x)` differs from `plan a` for every `a`.
* `diag_not_mem_range` : the diagonal profile is not in the range of `plan`.
* `no_surjective_plan` : no `plan : A → (A → Bool)` is surjective.
* `not_exists_surjective_plan` : there is no surjection from `A` onto profiles `A → Bool`.
* `card_profiles` : for finite `A`, `Fintype.card (A → Bool) = 2 ^ Fintype.card A`.
* `card_lt_card_profiles` : for finite `A`, `Fintype.card A < Fintype.card (A → Bool)`.
* `card_lt_two_pow` : for finite `A` with `n` agents, `n < 2 ^ n`.

INTERPRETED (docstring only, not formalized)
A plan indexed by its own society cannot anticipate every policy profile the society can
adopt; some profile always escapes every index, so some pluralism is forced.
-/

namespace PlannerDiagonalA

variable {A : Type*}

/-- The diagonal profile: each agent does the opposite of what the plan indexed by that
agent predicts for them. -/
def diag (plan : A → A → Bool) : A → Bool := fun x => !(plan x x)

/-- (1) Cantor: the diagonal profile is not equal to `plan a` for any `a`. -/
theorem diag_ne_plan (plan : A → A → Bool) (a : A) : diag plan ≠ plan a := by
  intro h
  have h1 : diag plan a = plan a a := congrFun h a
  simp [diag] at h1

theorem diag_not_mem_range (plan : A → A → Bool) : diag plan ∉ Set.range plan := by
  rintro ⟨a, ha⟩
  exact diag_ne_plan plan a ha.symm

/-- (2) No plan is surjective onto profiles. -/
theorem no_surjective_plan (plan : A → A → Bool) : ¬ Function.Surjective plan := by
  intro hs
  obtain ⟨a, ha⟩ := hs (diag plan)
  exact diag_ne_plan plan a ha.symm

/-- (2') There is no surjection from `A` onto profiles `A → Bool`. -/
theorem not_exists_surjective_plan :
    ¬ ∃ plan : A → (A → Bool), Function.Surjective plan := by
  rintro ⟨plan, hs⟩
  exact no_surjective_plan plan hs

/-- (3a) For finite `A` with `n` agents there are `2 ^ n` profiles. -/
theorem card_profiles [Fintype A] [DecidableEq A] :
    Fintype.card (A → Bool) = 2 ^ Fintype.card A := by
  simp [Fintype.card_bool]

/-- (3b) `n < 2 ^ n`. -/
theorem card_lt_two_pow [Fintype A] : Fintype.card A < 2 ^ Fintype.card A :=
  Nat.lt_two_pow_self

/-- (3) For finite `A`, strictly more profiles than agents. -/
theorem card_lt_card_profiles [Fintype A] [DecidableEq A] :
    Fintype.card A < Fintype.card (A → Bool) := by
  rw [card_profiles]
  exact card_lt_two_pow

end PlannerDiagonalA
