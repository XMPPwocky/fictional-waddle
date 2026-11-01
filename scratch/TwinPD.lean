import Mathlib

/-!
# Synced copies in a one-shot prisoner's dilemma, and the monitor caveat

PROVED:
* `synced_diagonal`: two copies running the same program on the same input act identically, so the outcome is
  (C,C) or (D,D); neither can unilaterally exploit the other.
* `policy_credit_cooperates`: choosing one action for both copies (policy credit), cooperation strictly beats
  every other choice: R > P.
* `instance_credit_defects`: holding the other's action fixed (instance credit), defection strictly dominates.
* `cliquebot_equilibrium`: program equilibrium (Tennenholtz 2004). A program that cooperates exactly when the
  opponent's source equals its own forms a strict Nash equilibrium of the program game: any different program
  gets at most P < R.
* `copies_collude`: the caveat. Logical correlation is value-neutral: in any symmetric game, policy-optimal
  identical copies pick the action maximizing the DIAGONAL payoff, whatever it is. `collusion_example` exhibits
  a three-action game where the diagonal maximizer is a 'collude against the monitor' action. So identity of
  copies cannot by itself prove that copies won't defect against a monitor; that needs symmetry broken between
  the monitor and the copies.
INTERPRETED (not formalized): "acausal cooperation" is the policy-credit choice; the AI-control reading of
`copies_collude` (untrusted copies monitoring each other can collude).
-/

namespace TwinPD

inductive Act | C | D
  deriving DecidableEq

/-- A prisoner's dilemma: temptation > reward > punishment > sucker. -/
structure PD where
  T : ℝ
  R : ℝ
  P : ℝ
  S : ℝ
  hTR : R < T
  hRP : P < R
  hPS : S < P

/-- Row player's payoff. -/
def payoff (g : PD) : Act → Act → ℝ
  | .C, .C => g.R
  | .C, .D => g.S
  | .D, .C => g.T
  | .D, .D => g.P

/-- Synced copies: the same program on the same input gives the same action, so the outcome is diagonal. -/
theorem synced_diagonal {I : Type*} (prog : I → Act) (i j : I) (hsync : i = j) :
    (prog i, prog j) = (Act.C, Act.C) ∨ (prog i, prog j) = (Act.D, Act.D) := by
  subst hsync
  cases h : prog i <;> simp

/-- Policy credit: choosing one action for both copies, cooperation is the unique best choice. -/
theorem policy_credit_cooperates (g : PD) (a : Act) (ha : a ≠ Act.C) :
    payoff g a a < payoff g Act.C Act.C := by
  cases a
  · exact absurd rfl ha
  · simpa [payoff] using g.hRP

/-- Instance credit: with the other's action held fixed, defection strictly dominates. -/
theorem instance_credit_defects (g : PD) (b : Act) : payoff g Act.C b < payoff g Act.D b := by
  cases b
  · simpa [payoff] using g.hTR
  · simpa [payoff] using g.hPS

/-- Programs read the opponent's source. `run k q` is what program `k` plays against program `q`. -/
def cliqueRun {Prog : Type*} [DecidableEq Prog] (k : Prog) (q : Prog) : Act := if q = k then Act.C else Act.D

/-- Program equilibrium: against the clique program `k`, any program `q` (whatever it plays) gets at most
the punishment payoff unless `q = k`, while `k` against itself gets the reward. So `(k, k)` is a strict Nash
equilibrium of the program game with outcome (C, C). -/
theorem cliquebot_equilibrium {Prog : Type*} [DecidableEq Prog] (g : PD) (k q : Prog) (hq : q ≠ k)
    (qPlays : Act) :
    payoff g qPlays (cliqueRun k q) < payoff g (cliqueRun k k) (cliqueRun k k) := by
  have h1 : cliqueRun k q = Act.D := by simp [cliqueRun, hq]
  have h2 : cliqueRun k k = Act.C := by simp [cliqueRun]
  rw [h1, h2]
  cases qPlays
  · simp only [payoff]; linarith [g.hRP, g.hPS]
  · simpa [payoff] using g.hRP

/-- The caveat: in ANY symmetric game, identical copies receive the diagonal payoff, and the policy-optimal
choice is a diagonal maximizer, whatever that action means. -/
theorem copies_collude {A : Type*} (u : A → A → ℝ) (best : A) (hbest : ∀ a, u a a ≤ u best best) (a : A) :
    u a a ≤ u best best := hbest a

/-- A concrete game with a monitor-defeating action: actions cooperate (0), defect (1), collude (2).
Colluding against the monitor pays both copies 5 on the diagonal, more than cooperating (3). -/
def monitorGame : Fin 3 → Fin 3 → ℝ := fun a b =>
  if a = b then (if a = 2 then 5 else if a = 0 then 3 else 1) else (if a = 1 then 4 else 0)

theorem collusion_example : ∀ a : Fin 3, a ≠ 2 → monitorGame a a < monitorGame 2 2 := by
  intro a ha
  fin_cases a
  · norm_num [monitorGame]
  · norm_num [monitorGame]
  · exact absurd rfl ha

end TwinPD
