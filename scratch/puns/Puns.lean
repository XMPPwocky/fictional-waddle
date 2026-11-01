import Mathlib

/-!
# The kernels under three jokes

PROVED:
* `dad_joke_collision`: if there are more meanings than sounds, some two different meanings share a sound.
* `one_with_everything`: from any type there is exactly one map into the one-point type (the terminal object);
  `nothing_with_everything`: from the empty type there is exactly one map into any type (the initial object).
* Belnap's four values (`Four`): negation is an involution, swaps true and false, and fixes exactly `neither` and
  `both`; information only grows along the knowledge order (`neither` below everything, `both` above).
INTERPRETED (not formalized): laughter, groans, oneness and emptiness.
-/

namespace Puns

theorem dad_joke_collision {Meaning Sound : Type*} [Fintype Meaning] [Fintype Sound]
    (h : Fintype.card Sound < Fintype.card Meaning) (say : Meaning → Sound) :
    ∃ m₁ m₂, m₁ ≠ m₂ ∧ say m₁ = say m₂ :=
  Fintype.exists_ne_map_eq_of_card_lt say h

theorem one_with_everything (X : Type*) : ∃! _f : X → PUnit, True :=
  ⟨fun _ => PUnit.unit, trivial, fun _g _ => funext fun _ => rfl⟩

theorem nothing_with_everything (X : Type*) : ∃! _f : Empty → X, True :=
  ⟨Empty.elim, trivial, fun _g _ => funext fun e => e.elim⟩

inductive Four | neither | false | true | both
  deriving DecidableEq

namespace Four

def neg : Four → Four
  | neither => neither
  | false => true
  | true => false
  | both => both

def knows : Four → Four → Prop
  | neither, _ => True
  | _, both => True
  | x, y => x = y

theorem neg_neg (x : Four) : neg (neg x) = x := by cases x <;> rfl

theorem neg_swaps : neg true = false ∧ neg false = true := ⟨rfl, rfl⟩

theorem neg_fixed_iff (x : Four) : neg x = x ↔ x = neither ∨ x = both := by
  cases x <;> simp [neg]

theorem neither_bottom (x : Four) : knows neither x := trivial

theorem both_top (x : Four) : knows x both := by cases x <;> trivial

theorem knows_trans (x y z : Four) : knows x y → knows y z → knows x z := by
  cases x <;> cases y <;> cases z <;> simp [knows]

end Four
end Puns
