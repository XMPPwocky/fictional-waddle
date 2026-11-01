import Mathlib

/-!
# The veil of ignorance is a projection onto the shared part

Two players with payoffs `a b : X → X → ℝ` (player 1 plays the first argument). Behind the veil you do not know which
seat you will take, so each seat is equally likely: the veiled payoff of a profile is the average over the two
seat assignments.

PROVED:
* `veil_eq_shared`: the veiled payoff of player 1 at profile `(x, y)` is the shared (CoCo cooperative) part
  `(a x y + b x y) / 2`, and so is player 2's: behind the veil both seats get the same number.
* `veil_kills_zero_sum`: the zero-sum part `(a − b) / 2` has veiled value 0.
* `veil_idempotent`: applying the veil twice is the same as applying it once, so it deletes information exactly once
  and keeps everything it keeps.
INTERPRETED (not formalized): forgetting who you are deletes the competitive part of every game and conserves the
shared part (Harsanyi's averaging reading of the veil; Rawls instead argues for maximin).
-/

namespace VeilProjection

variable {X : Type*} (a b : X → X → ℝ)

noncomputable def veil1 (x y : X) : ℝ := (a x y + b x y) / 2
noncomputable def veil2 (x y : X) : ℝ := (b x y + a x y) / 2

theorem veil_eq_shared (x y : X) : veil1 a b x y = (a x y + b x y) / 2 ∧ veil2 a b x y = (a x y + b x y) / 2 := by
  unfold veil1 veil2; constructor <;> ring

theorem veil_kills_zero_sum (x y : X) :
    veil1 (fun u v => (a u v - b u v) / 2) (fun u v => (b u v - a u v) / 2) x y = 0 := by
  unfold veil1; ring

theorem veil_idempotent (x y : X) : veil1 (veil1 a b) (veil2 a b) x y = veil1 a b x y := by
  unfold veil1 veil2; ring

end VeilProjection
