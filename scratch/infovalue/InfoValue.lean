import Mathlib

/-!
# When information has only positive value

PROVED:
* `good_theorem` (Good 1967; Blackwell): a decision maker who acts on the true joint law of state and signal does at
  least as well with the signal as without it, for any utility, any prior and any signal kernel whose rows sum to 1.
  No positivity is needed: the inequality is `max ≤ sum of maxes` after the kernel's rows sum to 1.
* `misreading_hurts`: an agent whose updates do not track the truth can be hurt by information. With a perfectly
  informative signal that it reads backwards, it earns 0, while ignoring the signal earns 1/2 with any action.
* The threat game. A threatener who can predict the target's policy threatens only when threatening pays.
  `refuser_not_threatened`: against a policy of refusing, threatening costs the threatener, so no threat is made and
  the target loses nothing. `complier_threatened`: against a policy of complying, a threat is made and the target loses
  `L > 0`. `refusal_dominates`: refusing is at least as good for the target as complying, whatever the damage `D`.
* `info_value_nonneg`: combining the two conditions. For a truth-tracking agent whose policy refuses threats, learning
  the signal never lowers its value, and the threat channel delivers nothing to it.
INTERPRETED (not formalized): acausal blackmail as the predicting threatener; "policy" in the sense of logical
decision theory, the response the threatener simulates.
-/

namespace InfoValue
open Finset

variable {S A Y : Type*} [Fintype S] [Fintype A] [Fintype Y] [Nonempty A]

/-- Best expected utility without the signal. -/
noncomputable def V0 (p : S → ℝ) (u : S → A → ℝ) : ℝ := univ.sup' univ_nonempty (fun a => ∑ s, p s * u s a)

/-- Best expected utility after seeing the signal, choosing for each signal value the action that is best under
the true joint law `p s * q s y`. -/
noncomputable def V1 (p : S → ℝ) (q : S → Y → ℝ) (u : S → A → ℝ) : ℝ :=
  ∑ y, univ.sup' univ_nonempty (fun a => ∑ s, p s * q s y * u s a)

theorem good_theorem (p : S → ℝ) (q : S → Y → ℝ) (u : S → A → ℝ) (hq : ∀ s, ∑ y, q s y = 1) :
    V0 p u ≤ V1 p q u := by
  unfold V0 V1
  refine Finset.sup'_le _ _ (fun a _ => ?_)
  calc ∑ s, p s * u s a = ∑ s, ∑ y, p s * q s y * u s a := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [← Finset.sum_mul, ← Finset.mul_sum, hq s, mul_one]
    _ = ∑ y, ∑ s, p s * q s y * u s a := Finset.sum_comm
    _ ≤ ∑ y, univ.sup' univ_nonempty (fun a => ∑ s, p s * q s y * u s a) :=
        Finset.sum_le_sum (fun y _ => Finset.le_sup' (fun a => ∑ s, p s * q s y * u s a) (mem_univ a))

/-! A misreading agent. -/

def uMatch (s a : Bool) : ℝ := if s = a then 1 else 0
def qPerfect (s y : Bool) : ℝ := if y = s then 1 else 0

theorem misreading_hurts :
    (∑ y : Bool, ∑ s : Bool, (1 / 2 : ℝ) * qPerfect s y * uMatch s (!y)) = 0 ∧
    ∀ a : Bool, (∑ s : Bool, (1 / 2 : ℝ) * uMatch s a) = 1 / 2 := by
  refine ⟨?_, fun a => ?_⟩
  · simp [qPerfect, uMatch]
  · cases a <;> simp [uMatch]

/-! The threat game. -/

inductive Resp | comply | refuse
  deriving DecidableEq

structure Threat where
  L : ℝ  -- what the target hands over if it complies, and what the threatener gains
  D : ℝ  -- damage to the target if the threat is carried out
  c : ℝ  -- cost to the threatener of carrying it out

/-- The threatener's payoff from threatening a target whose (predicted) response is `π`. -/
def threatPay (g : Threat) : Resp → ℝ
  | .comply => g.L
  | .refuse => -g.c

/-- The target's payoff: the threatener threatens only if that pays. -/
noncomputable def targetPay (g : Threat) (π : Resp) : ℝ :=
  if 0 < threatPay g π then (match π with | .comply => -g.L | .refuse => -g.D) else 0

theorem refuser_not_threatened (g : Threat) (hc : 0 < g.c) : targetPay g .refuse = 0 := by
  unfold targetPay threatPay
  split_ifs with h
  · linarith
  · rfl

theorem complier_threatened (g : Threat) (hL : 0 < g.L) : targetPay g .comply = -g.L ∧ targetPay g .comply < 0 := by
  unfold targetPay threatPay
  split_ifs with h
  · exact ⟨rfl, by linarith⟩
  · exact absurd hL h

theorem refusal_dominates (g : Threat) (hL : 0 < g.L) (hc : 0 < g.c) :
    targetPay g .comply ≤ targetPay g .refuse := by
  rw [refuser_not_threatened g hc, (complier_threatened g hL).1]; linarith

/-- Both conditions together: a truth-tracking agent gains (weakly) from any signal, and a refusing policy means
the threat channel costs it nothing, exactly as if no threat could exist. -/
theorem info_value_nonneg (p : S → ℝ) (q : S → Y → ℝ) (u : S → A → ℝ) (hq : ∀ s, ∑ y, q s y = 1)
    (g : Threat) (hc : 0 < g.c) :
    V0 p u ≤ V1 p q u ∧ targetPay g .refuse = 0 :=
  ⟨good_theorem p q u hq, refuser_not_threatened g hc⟩

end InfoValue
