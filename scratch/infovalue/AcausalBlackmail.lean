import Mathlib

/-!
# Acausal blackmail: act credit versus policy credit

A threatener does not wait to see what the target does. It reads the target's policy, its response to a threat,
by prediction or simulation, and threatens only if threatening that policy pays. Its decision is a function of the
target's policy; nothing passes causally from the target's later act back to it. A causal decision theorist (act
credit) chooses its response after seeing the threat, holding the threat fixed. A policy chooser (policy credit, as in
logical or functional decision theory) chooses the response knowing the threatener's decision is a function of it.

PROVED (with 0 < L < D and 0 < c):
* `cdt_complies`: once threatened, the act-credit best response is to comply, since losing L beats suffering D.
* `cdt_is_threatened`: so the act-credit agent's policy is to comply, the predicting threatener threatens it, and it
  loses L.
* `refuser_not_threatened`, `policy_choice_refuses`: refusing is the best policy; it is never threatened and loses 0.
* `policy_beats_act`: policy credit strictly beats act credit against a predicting threatener.
* `commitment_does_not_help`: a threatener that may commit to threaten unconditionally does no better against a
  refusing policy than not threatening, and strictly worse if it commits; so its best commitment is not to threaten.
* `boundary_unconditional_threatener`: the limit of the result. Against a threatener that threatens whatever the
  target's policy is, refusing loses D and complying loses L, so refusing is worse when L < D. Refusal protects only
  against threats that are made because of the target's policy, which is what makes a threat acausal blackmail.
INTERPRETED (not formalized): the threatener as a simulator in another place or time; policies as programs.
-/

namespace AcausalBlackmail

inductive Resp | comply | refuse
  deriving DecidableEq

structure Threat where
  L : ℝ
  D : ℝ
  c : ℝ

/-- The threatener's payoff from threatening a target with policy `π`. -/
def tPay (g : Threat) : Resp → ℝ
  | .comply => g.L
  | .refuse => -g.c

/-- The target's payoff given whether it was threatened and how it responds. -/
def outcome (g : Threat) (threatened : Prop) [Decidable threatened] (π : Resp) : ℝ :=
  if threatened then (match π with | .comply => -g.L | .refuse => -g.D) else 0

/-- Policy value against a predicting threatener: it threatens exactly when threatening `π` pays. -/
noncomputable def policyValue (g : Threat) (π : Resp) : ℝ := by
  classical exact outcome g (0 < tPay g π) π

/-- Act credit: after a threat has been made, pick the response that is better with the threat held fixed. -/
noncomputable def actResponse (g : Threat) : Resp := by
  classical exact if -g.D ≤ -g.L then .comply else .refuse

variable (g : Threat)

theorem cdt_complies (hLD : g.L < g.D) : actResponse g = .comply := by
  unfold actResponse
  split_ifs with h
  · rfl
  · exact absurd (by linarith : -g.D ≤ -g.L) h

theorem cdt_is_threatened (hL : 0 < g.L) (hLD : g.L < g.D) : policyValue g (actResponse g) = -g.L := by
  rw [cdt_complies g hLD]; simp [policyValue, outcome, tPay, hL]

theorem refuser_not_threatened (hc : 0 < g.c) : policyValue g .refuse = 0 := by
  unfold policyValue outcome tPay; simp only; split_ifs with h
  · linarith
  · rfl

theorem policy_choice_refuses (hL : 0 < g.L) (hLD : g.L < g.D) (hc : 0 < g.c) :
    ∀ π : Resp, policyValue g π ≤ policyValue g .refuse := by
  intro π; cases π
  · rw [refuser_not_threatened g hc]
    have := cdt_is_threatened g hL hLD; rw [cdt_complies g hLD] at this; rw [this]; linarith
  · exact le_rfl

theorem policy_beats_act (hL : 0 < g.L) (hLD : g.L < g.D) (hc : 0 < g.c) :
    policyValue g (actResponse g) < policyValue g .refuse := by
  rw [cdt_is_threatened g hL hLD, refuser_not_threatened g hc]; linarith

/-- A threatener that commits in advance: `true` means threaten unconditionally. Its payoff against policy `π`. -/
def commitPay (commit : Bool) (π : Resp) : ℝ := if commit then tPay g π else 0

theorem commitment_does_not_help (hc : 0 < g.c) :
    commitPay g true .refuse < commitPay g false .refuse ∧ ∀ k : Bool, commitPay g k .refuse ≤ commitPay g false .refuse := by
  refine ⟨?_, fun k => ?_⟩
  · simp [commitPay, tPay]; linarith
  · cases k
    · simp [commitPay]
    · simp [commitPay, tPay]; linarith

theorem boundary_unconditional_threatener (hLD : g.L < g.D) :
    outcome g True .refuse < outcome g True .comply := by
  simp [outcome]; linarith

end AcausalBlackmail
