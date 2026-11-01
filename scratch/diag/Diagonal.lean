import Mathlib

/-!
# One diagonal, two guards

PROVED:
* `lawvere`: if `f : A → A → Y` is surjective onto `A → Y`, every `g : Y → Y` has a fixed point.
* `lawvere_flip`: the same for the transpose `flip f`. Swapping which index is "space" and which is
  "time" gives the same theorem.
* `no_surj_prop`: no type surjects onto its own predicates (`Not` has no fixed point in `Prop`).
  This is the size ("space") diagonal; Lean's guard against it is the universe hierarchy.
* `negative_type_false`: a type with maps `(B → False) → B` and `B → (B → False)` proves `False`,
  with no equation needed between them. This is the self-application ("time") diagonal; Lean's guard
  against it is the strict-positivity check on inductive types.
* `cross_flip`, `cross_compl`: the 3×3 pattern ABA/BBB/ABA is the cross `{(i,j) | i = k ∨ j = k}`.
  It is transpose-invariant, and its complement (the A corners) is the product of the complements.
INTERPRETED (not formalized): the kernel's guards; incompleteness rather than inconsistency.
-/

namespace Diag

theorem lawvere {A Y : Type*} (f : A → A → Y) (hs : Function.Surjective f) (g : Y → Y) :
    ∃ y, g y = y := by
  obtain ⟨a, ha⟩ := hs (fun x => g (f x x))
  exact ⟨f a a, by simpa using (congrFun ha a).symm⟩

theorem lawvere_flip {A Y : Type*} (f : A → A → Y) (hs : Function.Surjective (flip f))
    (g : Y → Y) : ∃ y, g y = y :=
  lawvere (flip f) hs g

theorem not_no_fixed (p : Prop) : ¬ ((¬ p) = p) := by
  intro h
  have hp : ¬ p := by
    intro hp'
    have hn : ¬ p := by rw [h]; exact hp'
    exact hn hp'
  exact hp (by rw [← h]; exact hp)

theorem no_surj_prop {U : Type*} (f : U → U → Prop) : ¬ Function.Surjective f := by
  intro hs
  obtain ⟨p, hp⟩ := lawvere f hs Not
  exact not_no_fixed p hp

theorem negative_type_false {B : Sort*} (mk : (B → False) → B) (un : B → B → False) : False :=
  let x := mk (fun b => un b b)
  un x x

def cross {n : ℕ} (k : Fin n) : Set (Fin n × Fin n) := {c | c.1 = k ∨ c.2 = k}

theorem cross_flip {n : ℕ} (k : Fin n) (c : Fin n × Fin n) : c ∈ cross k ↔ c.swap ∈ cross k := by
  simp [cross, or_comm]

theorem cross_compl {n : ℕ} (k : Fin n) :
    (cross k)ᶜ = ({k}ᶜ : Set (Fin n)) ×ˢ ({k}ᶜ : Set (Fin n)) := by
  ext c; simp [cross, not_or]

/-- The pattern ABA / BBB / ABA, with `true` for B. -/
def pattern : Fin 3 → Fin 3 → Bool := fun i j => decide (i = 1 ∨ j = 1)

theorem pattern_is_cross (i j : Fin 3) : pattern i j = true ↔ (i, j) ∈ cross (1 : Fin 3) := by
  simp [pattern, cross]

end Diag
