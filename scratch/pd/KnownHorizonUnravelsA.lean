import Mathlib

/-!
# Known finite horizon: the repeated prisoner's dilemma unravels to all-defect

Stage game: actions `C`, `D`; payoff to a player choosing `a` against `b` is `u a b` with
`u D C = T`, `u C C = R`, `u D D = P`, `u C D = S`, and `T > R > P > S`.

PROVED
* `V_eq`: the all-defect continuation value `V 0 = 0`, `V (k+1) = P + V k` equals `k * P`.
* `defect_gt_coop_vs_C`, `defect_gt_coop_vs_D`: `T + V k > R + V k` and `P + V k > S + V k`.
* `defect_strict_best_response`: for any continuation value `c` that does not depend on this
  round's actions, `u D b + c > u C b + c` for both opponent actions `b`.
* `consistent_iff`: a path of length `N` is consistent with strict best responses at every
  round (each round's continuation = payoff of the already-determined remainder of the path)
  iff it is `N` copies of `(D, D)`; `consistent_payoff`: its total payoff is `N * P`.
* `spe_outcome_allD`: (strengthening of (2)) in the `N`-round game with arbitrary
  history-dependent pure strategies, every subgame-perfect equilibrium plays `(D, D)` in every
  round, so each player gets `N * P` (`spe_payoff`). `allD_isSPE`: always-defect is a
  subgame-perfect equilibrium, so the statement is not vacuous.
* Contrast (geometric horizon, restated from GrimTriggerThreshold): for `0 ≤ δ < 1`,
  `R / (1 - δ) ≥ T + δ * P / (1 - δ) ↔ δ ≥ (T - R) / (T - P)` (`grim_coop_iff`), and the
  threshold lies in `(0, 1)` (`threshold_mem_Ioo`), so for every `δ ∈ [(T-R)/(T-P), 1)` grim
  trigger cooperation is not beaten by a one-shot deviation (`grim_coop_near_one`).

INTERPRETED
* Modelling assumption for (1)-(2): at a round with `k + 1` rounds left, the continuation
  value after this round is a fixed number that does not depend on this round's actions.
  In `Consistent` this is built in: the remainder of the path is fixed before the current
  round is evaluated, and its payoff is the continuation. In the SPE version it is derived:
  by induction every subgame with `k` rounds left yields `k * P` whatever the history.
* In the contrast, `δ` is the per-round continuation probability; `R / (1 - δ)` is the value
  of cooperating forever against grim trigger, `T + δ * P / (1 - δ)` the value of a one-shot
  deviation followed by mutual defection. Only the one-shot-deviation inequality is proved
  here, not a full equilibrium theorem for the infinite game.
-/

namespace KnownHorizonUnravelsA

inductive Act
  | C
  | D
  deriving DecidableEq

open Act

/-- Prisoner's dilemma payoffs with `T > R > P > S`. -/
structure PD where
  T : ℝ
  R : ℝ
  P : ℝ
  S : ℝ
  hTR : R < T
  hRP : P < R
  hPS : S < P

variable (g : PD)

/-- Stage payoff to a player choosing `a` against an opponent choosing `b`. -/
def u : Act → Act → ℝ
  | D, C => g.T
  | C, C => g.R
  | D, D => g.P
  | C, D => g.S

/-- Continuation value with `k` rounds left when both defect in all remaining rounds. -/
def V : ℕ → ℝ
  | 0 => 0
  | k + 1 => g.P + V k

theorem V_eq (k : ℕ) : V g k = k * g.P := by
  induction k with
  | zero => simp [V]
  | succ k ih => simp [V, ih]; ring

/-! ## (1) Strict best response with action-independent continuation -/

theorem defect_gt_coop_vs_C (k : ℕ) : g.T + V g k > g.R + V g k := by
  have := g.hTR; linarith

theorem defect_gt_coop_vs_D (k : ℕ) : g.P + V g k > g.S + V g k := by
  have := g.hPS; linarith

theorem u_D_gt_u_C (b : Act) : u g C b < u g D b := by
  cases b
  · exact g.hTR
  · exact g.hPS

/-- With a continuation value `c` independent of the current actions, defecting is strictly
better than cooperating against either opponent action. -/
theorem defect_strict_best_response (c : ℝ) (b : Act) : u g D b + c > u g C b + c := by
  have := u_D_gt_u_C g b; linarith

/-! ## (2) Path version: the unique consistent outcome is all-defect -/

/-- Total payoff to the first player along a path of action pairs `(own, opponent)`. -/
def pay1 : List (Act × Act) → ℝ
  | [] => 0
  | p :: t => u g p.1 p.2 + pay1 t

/-- Total payoff to the second player. -/
def pay2 : List (Act × Act) → ℝ
  | [] => 0
  | p :: t => u g p.2 p.1 + pay2 t

/-- `a` is the strict best response against `b` given continuation value `c`. -/
def StrictBR (a b : Act) (c : ℝ) : Prop :=
  ∀ a' : Act, a' ≠ a → u g a' b + c < u g a b + c

/-- A path of length `k` in which, at every round, each player's action is a strict best
response given that the continuation is the (already fixed) payoff of the rest of the path. -/
def Consistent : ℕ → List (Act × Act) → Prop
  | 0, l => l = []
  | _ + 1, [] => False
  | k + 1, p :: rest =>
      Consistent k rest ∧ StrictBR g p.1 p.2 (pay1 g rest) ∧ StrictBR g p.2 p.1 (pay2 g rest)

theorem strictBR_iff (a b : Act) (c : ℝ) : StrictBR g a b c ↔ a = D := by
  constructor
  · intro h
    cases a
    · have := h D (by decide)
      have := u_D_gt_u_C g b
      linarith
    · rfl
  · rintro rfl a' ha'
    cases a'
    · have := u_D_gt_u_C g b; linarith
    · exact absurd rfl ha'

theorem consistent_iff (N : ℕ) (l : List (Act × Act)) :
    Consistent g N l ↔ l = List.replicate N (D, D) := by
  induction N generalizing l with
  | zero => simp [Consistent]
  | succ k ih =>
    cases l with
    | nil => simp [Consistent]
    | cons p rest =>
      obtain ⟨a, b⟩ := p
      simp only [Consistent, strictBR_iff, ih, List.replicate_succ, List.cons.injEq,
        Prod.mk.injEq]
      tauto

theorem pay1_replicate (k : ℕ) : pay1 g (List.replicate k (D, D)) = k * g.P := by
  induction k with
  | zero => simp [pay1]
  | succ k ih => simp [List.replicate_succ, pay1, u, ih]; ring

theorem pay2_replicate (k : ℕ) : pay2 g (List.replicate k (D, D)) = k * g.P := by
  induction k with
  | zero => simp [pay2]
  | succ k ih => simp [List.replicate_succ, pay2, u, ih]; ring

theorem consistent_payoff (N : ℕ) (l : List (Act × Act)) (h : Consistent g N l) :
    pay1 g l = N * g.P ∧ pay2 g l = N * g.P ∧ pay1 g l = V g N := by
  rw [(consistent_iff g N l).1 h, pay1_replicate, pay2_replicate, V_eq]
  exact ⟨rfl, rfl, rfl⟩

/-! ## (2') Subgame-perfect equilibria of the `N`-round game -/

/-- A pure strategy maps the history (list of past action pairs `(a₁, a₂)`) to an action. -/
abbrev Strat := List (Act × Act) → Act

/-- Play `k` more rounds from history `h`. Pairs are `(player 1 action, player 2 action)`. -/
def play (σ₁ σ₂ : Strat) : List (Act × Act) → ℕ → List (Act × Act)
  | _, 0 => []
  | h, k + 1 => (σ₁ h, σ₂ h) :: play σ₁ σ₂ (h ++ [(σ₁ h, σ₂ h)]) k

/-- Subgame-perfect equilibrium of the `N`-round game: at every history of length `m ≤ N`,
no strategy of either player does better in the subgame with `N - m` rounds left. -/
def IsSPE (N : ℕ) (σ₁ σ₂ : Strat) : Prop :=
  ∀ h : List (Act × Act), h.length ≤ N →
    (∀ τ : Strat, pay1 g (play τ σ₂ h (N - h.length)) ≤ pay1 g (play σ₁ σ₂ h (N - h.length))) ∧
    (∀ τ : Strat, pay2 g (play σ₁ τ h (N - h.length)) ≤ pay2 g (play σ₁ σ₂ h (N - h.length)))

theorem play_congr (m : ℕ) (σ₁ τ₁ σ₂ τ₂ : Strat)
    (h₁ : ∀ h', m ≤ h'.length → τ₁ h' = σ₁ h') (h₂ : ∀ h', m ≤ h'.length → τ₂ h' = σ₂ h') :
    ∀ (k : ℕ) (h : List (Act × Act)), m ≤ h.length → play τ₁ τ₂ h k = play σ₁ σ₂ h k := by
  intro k
  induction k with
  | zero => intro h _; rfl
  | succ k ih =>
    intro h hm
    simp only [play, h₁ h hm, h₂ h hm]
    rw [ih]
    simp; omega

theorem spe_from (N : ℕ) (σ₁ σ₂ : Strat) (hspe : IsSPE g N σ₁ σ₂) :
    ∀ (k : ℕ) (h : List (Act × Act)), h.length + k = N →
      play σ₁ σ₂ h k = List.replicate k (D, D) := by
  intro k
  induction k with
  | zero => intro h _; rfl
  | succ k ih =>
    intro h hlen
    have hk : N - h.length = k + 1 := by omega
    have hcont : ∀ p : Act × Act, play σ₁ σ₂ (h ++ [p]) k = List.replicate k (D, D) := by
      intro p; apply ih; simp; omega
    obtain ⟨hs1, hs2⟩ := hspe h (by omega)
    rw [hk] at hs1 hs2
    have e1 : σ₁ h = D := by
      by_contra hne
      have hC : σ₁ h = C := by cases h' : σ₁ h <;> simp_all
      let τ : Strat := Function.update σ₁ h D
      have hτ : ∀ h', h.length + 1 ≤ h'.length → τ h' = σ₁ h' := by
        intro h' hl
        have : h' ≠ h := by rintro rfl; omega
        simp [τ, Function.update_of_ne this]
      have := hs1 τ
      simp only [play, pay1] at this
      rw [play_congr (h.length + 1) σ₁ τ σ₂ σ₂ hτ (fun _ _ => rfl) k _ (by simp), hcont,
        hcont, pay1_replicate] at this
      simp only [τ, Function.update_self, hC] at this
      have := u_D_gt_u_C g (σ₂ h)
      linarith
    have e2 : σ₂ h = D := by
      by_contra hne
      have hC : σ₂ h = C := by cases h' : σ₂ h <;> simp_all
      let τ : Strat := Function.update σ₂ h D
      have hτ : ∀ h', h.length + 1 ≤ h'.length → τ h' = σ₂ h' := by
        intro h' hl
        have : h' ≠ h := by rintro rfl; omega
        simp [τ, Function.update_of_ne this]
      have := hs2 τ
      simp only [play, pay2] at this
      rw [play_congr (h.length + 1) σ₁ σ₁ σ₂ τ (fun _ _ => rfl) hτ k _ (by simp), hcont,
        hcont, pay2_replicate] at this
      simp only [τ, Function.update_self, hC] at this
      have := u_D_gt_u_C g (σ₁ h)
      linarith
    simp only [play, e1, e2]
    rw [hcont, List.replicate_succ]

/-- Every subgame-perfect equilibrium of the `N`-round game defects in every round. -/
theorem spe_outcome_allD (N : ℕ) (σ₁ σ₂ : Strat) (hspe : IsSPE g N σ₁ σ₂) :
    play σ₁ σ₂ [] N = List.replicate N (D, D) :=
  spe_from g N σ₁ σ₂ hspe N [] (by simp)

theorem spe_payoff (N : ℕ) (σ₁ σ₂ : Strat) (hspe : IsSPE g N σ₁ σ₂) :
    pay1 g (play σ₁ σ₂ [] N) = N * g.P ∧ pay2 g (play σ₁ σ₂ [] N) = N * g.P := by
  rw [spe_outcome_allD g N σ₁ σ₂ hspe, pay1_replicate, pay2_replicate]
  exact ⟨rfl, rfl⟩

theorem u_le_P (a : Act) : u g a D ≤ g.P := by
  cases a
  · exact g.hPS.le
  · exact le_rfl

theorem play_allD (k : ℕ) (h : List (Act × Act)) :
    play (fun _ => D) (fun _ => D) h k = List.replicate k (D, D) := by
  induction k generalizing h with
  | zero => rfl
  | succ k ih => simp [play, ih, List.replicate_succ]

theorem pay1_vs_allD (τ : Strat) (k : ℕ) (h : List (Act × Act)) :
    pay1 g (play τ (fun _ => D) h k) ≤ k * g.P := by
  induction k generalizing h with
  | zero => simp [play, pay1]
  | succ k ih =>
    simp only [play, pay1]
    have := ih (h ++ [(τ h, D)])
    have := u_le_P g (τ h)
    push_cast; linarith

theorem pay2_vs_allD (τ : Strat) (k : ℕ) (h : List (Act × Act)) :
    pay2 g (play (fun _ => D) τ h k) ≤ k * g.P := by
  induction k generalizing h with
  | zero => simp [play, pay2]
  | succ k ih =>
    simp only [play, pay2]
    have := ih (h ++ [(D, τ h)])
    have := u_le_P g (τ h)
    push_cast; linarith

/-- Always-defect is a subgame-perfect equilibrium of the `N`-round game. -/
theorem allD_isSPE (N : ℕ) : IsSPE g N (fun _ => D) (fun _ => D) := by
  intro h _
  refine ⟨fun τ => ?_, fun τ => ?_⟩
  · rw [play_allD, pay1_replicate]; exact pay1_vs_allD g τ _ h
  · rw [play_allD, pay2_replicate]; exact pay2_vs_allD g τ _ h

/-! ## (3) Contrast: geometric horizon (restated grim-trigger threshold) -/

theorem grim_coop_iff (δ : ℝ) (_hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    g.R / (1 - δ) ≥ g.T + δ * g.P / (1 - δ) ↔ δ ≥ (g.T - g.R) / (g.T - g.P) := by
  have h1 : 0 < 1 - δ := by linarith
  have hTP : 0 < g.T - g.P := by have := g.hTR; have := g.hRP; linarith
  rw [ge_iff_le, ge_iff_le, div_le_iff₀ hTP,
    show g.T + δ * g.P / (1 - δ) = (g.T * (1 - δ) + δ * g.P) / (1 - δ) by
      field_simp, div_le_div_iff_of_pos_right h1]
  constructor <;> intro h <;> nlinarith

theorem threshold_mem_Ioo : (g.T - g.R) / (g.T - g.P) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hTP : 0 < g.T - g.P := by have := g.hTR; have := g.hRP; linarith
  have := g.hTR; have := g.hRP
  constructor
  · exact div_pos (by linarith) hTP
  · rw [div_lt_one hTP]; linarith

/-- For every continuation probability `δ` in `[(T-R)/(T-P), 1)` (a nonempty interval below 1),
cooperating forever under grim trigger is worth at least a one-shot deviation. -/
theorem grim_coop_near_one :
    (g.T - g.R) / (g.T - g.P) < 1 ∧
    ∀ δ : ℝ, (g.T - g.R) / (g.T - g.P) ≤ δ → δ < 1 →
      g.R / (1 - δ) ≥ g.T + δ * g.P / (1 - δ) := by
  refine ⟨(threshold_mem_Ioo g).2, fun δ hδ hδ1 => ?_⟩
  have h0 : 0 ≤ δ := le_trans (threshold_mem_Ioo g).1.le hδ
  exact (grim_coop_iff g δ h0 hδ1).2 hδ

end KnownHorizonUnravelsA
