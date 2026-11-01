import Mathlib

/-!
# Repressed, foreclosed, disavowed: three ways a statement can fail to be simply held

A formal model, not a claim about clinical psychology. Lacan distinguishes neurosis, psychosis and perversion by
three operations on a signifier: repression (it is in the subject's language but cannot be said), foreclosure (it was
never admitted to the language at all) and disavowal ("I know very well, but all the same"). Each has an exact
logical counterpart.

PROVED:
* `repressed_is_true_unprovable`: if a sentence `g` says of itself "I am not provable" and provability is sound,
  then `g` is true and not provable: expressible inside the system, inaccessible to it (Gödel's shape).
* `repressed_returns`: adding `g` as an axiom does not end it. Any fixed point `g'` for the extended provability is
  again true and unprovable, and is a different sentence. What is repressed comes back in a new form.
* `foreclosed_is_unnameable`: for any way `e` of letting sentences name predicates, the diagonal predicate
  `a ↦ ¬ e a a` is named by no sentence (Cantor and Lawvere's shape, behind Tarski's undefinability of truth). It is
  perfectly meaningful from outside, and can only arrive from outside.
* `disavowal_does_not_explode`: in Belnap's four-valued logic a statement can be held as both true and false, so
  `P ∧ ¬P` is accepted, while an unrelated `Q` is not. Holding both does not make everything follow.
INTERPRETED (not formalized): neurosis, psychosis and perversion; symptoms; "what is foreclosed in the symbolic
returns in the real".
-/

namespace ThreeStructures

theorem repressed_is_true_unprovable {A : Type*} (val Pr : A → Prop) (g : A)
    (hfix : val g ↔ ¬ Pr g) (hsound : ∀ a, Pr a → val a) : val g ∧ ¬ Pr g := by
  have hnp : ¬ Pr g := fun hp => (hfix.mp (hsound g hp)) hp
  exact ⟨hfix.mpr hnp, hnp⟩

theorem repressed_returns {A : Type*} (val Pr : A → Prop) (g g' : A)
    (hfix : val g ↔ ¬ Pr g) (hsound : ∀ a, Pr a → val a)
    (hfix' : val g' ↔ ¬ (Pr g' ∨ g' = g)) :
    val g' ∧ ¬ (Pr g' ∨ g' = g) ∧ g' ≠ g := by
  have hg := (repressed_is_true_unprovable val Pr g hfix hsound).1
  have hsound' : ∀ a, (Pr a ∨ a = g) → val a := by
    rintro a (h | rfl)
    · exact hsound a h
    · exact hg
  have h := repressed_is_true_unprovable val (fun a => Pr a ∨ a = g) g' hfix' hsound'
  exact ⟨h.1, h.2, fun he => h.2 (Or.inr he)⟩

theorem foreclosed_is_unnameable {A : Type*} (e : A → A → Prop) : ¬ ∃ d, e d = fun a => ¬ e a a := by
  rintro ⟨d, hd⟩
  have h : e d d ↔ ¬ e d d := by
    constructor
    · intro h; rw [hd] at h; exact h
    · intro h; rw [hd]; exact h
  by_cases hdd : e d d
  · exact h.mp hdd hdd
  · exact hdd (h.mpr hdd)

inductive Four | neither | false | true | both
  deriving DecidableEq

namespace Four

def neg : Four → Four
  | neither => neither
  | false => true
  | true => false
  | both => both

def and : Four → Four → Four
  | false, _ => false
  | _, false => false
  | true, y => y
  | x, true => x
  | neither, neither => neither
  | both, both => both
  | neither, both => false
  | both, neither => false

def accepted : Four → Prop
  | true => True
  | both => True
  | _ => False

end Four

theorem disavowal_does_not_explode :
    ∃ P Q : Four, Four.accepted (Four.and P (Four.neg P)) ∧ ¬ Four.accepted Q :=
  ⟨Four.both, Four.false, trivial, id⟩

end ThreeStructures
