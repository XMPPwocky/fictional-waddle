/-
# Elua cooperation theorems (notes/BOOK_THEOREM/elua_cooperation.md, notes/BOOK_THEOREM.md §7)

This file formalizes

* **Theorem B** (§3): the efficiency frontier of the two-player donation game with reading
  fidelity `f` is `W*(f) = (b − c)·min(1, f b / c)`, and full mutual cooperation is a program
  equilibrium payoff iff `f b ≥ c`;
* **Theorem A.1–A.2** (§2): sufficiency (trigger programs with minmax-style punishment) and
  necessity (best punishment) for a pure profile `a*` of a general finite `n`-player game to be
  sustained on every branch of the reads in the noisy program game `G^f`;
* **Theorem C** (§4): the selfish policy-level gradient through a reader of fidelity `f` and rule
  `φ` is `(b f φ′(p) − c) p (1 − p)`, the action-level gradient is `−c p (1 − p)`, for a
  mirror the sign of the policy-level gradient is the sign of `f b − c` (C.1–C.2), the
  continuous-time flow has `p → 1` iff `f b > c`, `p → 0` iff `f b < c`, stationary iff
  `f b = c` (C.2), and the homo moralis first-order identity (C.3).

Not formalized: Theorem A.3 (endpoints `f = 0`, `f = 1`, monotonicity of `D̃`), A.4 (legibility
as a discount factor), and Theorem D.

See `lean/FIDELITY_cooperation.md` for the statement-by-statement fidelity table.
-/
import Mathlib

open Finset

noncomputable section

namespace BoundaryTheorem.Cooperation

/-! ## Part B: the two-player donation game with reading fidelity `f` (note §1, §3)

The note's model (§2, specialised to `n = 2`): each player `i` submits a program `π_i` from a
language `Π_i`; a total evaluator `ev_i : Π_i × (Π_{−i} ⊔ {⊥}) → Δ(A_i)` gives the mixed action
the program plays on a successful read of the other's text, or on a failed read `⊥`.  In the
donation game `A_i = {C, D}`, so a mixed action is its cooperation probability `P(C) ∈ [0,1]`.
Reads succeed independently with probability `f` (the same for both players, note §3), and
actions are then drawn independently.
-/

/-- Bernoulli law on `Bool` (`true` = cooperate `C`) with cooperation probability `p`. -/
def bern (p : ℝ) : Bool → ℝ := fun a => if a then p else 1 - p

/-- The two-player noisy program game over the donation game (note §1 "Donation game", §2
"noisy program game" with `n = 2`, §3 "the same `f` for both").

* `b`, `c`: cooperating costs the actor `c > 0` and gives the partner `b > c`;
* `f ∈ [0,1]`: reading fidelity, the probability that a read succeeds;
* `ev₁ π₁ r` (resp. `ev₂`): the cooperation probability `P(C)` of the mixed action
  `ev_1(π_1, read_1)`, where `r = none` is the failed read `⊥` and `r = some π₂` a successful
  read of the opponent's text. -/
structure DonationProgramGame (Prog₁ Prog₂ : Type*) where
  b : ℝ
  c : ℝ
  f : ℝ
  ev₁ : Prog₁ → Option Prog₂ → ℝ
  ev₂ : Prog₂ → Option Prog₁ → ℝ
  c_pos : 0 < c
  c_lt_b : c < b
  f_mem : f ∈ Set.Icc (0 : ℝ) 1
  ev₁_mem : ∀ π r, ev₁ π r ∈ Set.Icc (0 : ℝ) 1
  ev₂_mem : ∀ π r, ev₂ π r ∈ Set.Icc (0 : ℝ) 1

namespace DonationProgramGame

variable {Prog₁ Prog₂ : Type*} (G : DonationProgramGame Prog₁ Prog₂)

/-- The donation-game payoff `u_1(a_1, a_2)` to player 1 (note §1): `b` if the partner
cooperates, minus `c` if I cooperate. -/
def u₁ (a₁ a₂ : Bool) : ℝ := (if a₂ then G.b else 0) - (if a₁ then G.c else 0)

/-- Payoff to player 2: the same game from the other seat. -/
def u₂ (a₁ a₂ : Bool) : ℝ := G.u₁ a₂ a₁

/-- Expected payoff of `u` under independent action draws `a₁ ∼ Bern(p)`, `a₂ ∼ Bern(q)`. -/
def expAct (u : Bool → Bool → ℝ) (p q : ℝ) : ℝ :=
  ∑ a₁ : Bool, ∑ a₂ : Bool, bern p a₁ * bern q a₂ * u a₁ a₂

/-- Probability of a read outcome (`true` = read succeeded) at fidelity `f`. -/
def readProb (f : ℝ) : Bool → ℝ := bern f

/-- Player 1's realised mixed action given its read outcome `r₁`. -/
def act₁ (π₁ : Prog₁) (π₂ : Prog₂) (r₁ : Bool) : ℝ :=
  G.ev₁ π₁ (if r₁ then some π₂ else none)

/-- Player 2's realised mixed action given its read outcome `r₂`. -/
def act₂ (π₁ : Prog₁) (π₂ : Prog₂) (r₂ : Bool) : ℝ :=
  G.ev₂ π₂ (if r₂ then some π₁ else none)

/-- Payoff `U_1(π) = E[u_1(a)]` of the noisy program game (note §2): expectation over the two
independent read coins and then over the independent action draws. -/
def U₁ (π₁ : Prog₁) (π₂ : Prog₂) : ℝ :=
  ∑ r₁ : Bool, ∑ r₂ : Bool,
    readProb G.f r₁ * readProb G.f r₂ * expAct G.u₁ (G.act₁ π₁ π₂ r₁) (G.act₂ π₁ π₂ r₂)

/-- Payoff `U_2(π)`. -/
def U₂ (π₁ : Prog₁) (π₂ : Prog₂) : ℝ :=
  ∑ r₁ : Bool, ∑ r₂ : Bool,
    readProb G.f r₁ * readProb G.f r₂ * expAct G.u₂ (G.act₁ π₁ π₂ r₁) (G.act₂ π₁ π₂ r₂)

/-- A **program equilibrium** is a Nash equilibrium of `G^f` (note §2): no player gains by
submitting any other program of its language. -/
def IsProgramEquilibrium (π₁ : Prog₁) (π₂ : Prog₂) : Prop :=
  (∀ π₁', G.U₁ π₁' π₂ ≤ G.U₁ π₁ π₂) ∧ (∀ π₂', G.U₂ π₁ π₂' ≤ G.U₂ π₁ π₂)

/-- On-path cooperation rate `x_1 = f ρ_1 + (1 − f) d_1` of player 1 (note §3, proof of B). -/
def x₁ (π₁ : Prog₁) (π₂ : Prog₂) : ℝ :=
  G.f * G.ev₁ π₁ (some π₂) + (1 - G.f) * G.ev₁ π₁ none

/-- On-path cooperation rate `x_2`. -/
def x₂ (π₁ : Prog₁) (π₂ : Prog₂) : ℝ :=
  G.f * G.ev₂ π₂ (some π₁) + (1 - G.f) * G.ev₂ π₂ none

/-- The average payoff `(U_1 + U_2)/2` (note §3, Theorem B.2). -/
def avg (π₁ : Prog₁) (π₂ : Prog₂) : ℝ := (G.U₁ π₁ π₂ + G.U₂ π₁ π₂) / 2

/-- The frontier `W*(f) = (b − c)·min(1, f b / c)` (note §3, Theorem B.2). -/
def Wstar : ℝ := (G.b - G.c) * min 1 (G.f * G.b / G.c)

/-- The optimal default `d* = min(1, f(b − c)/(c(1 − f)))` (note §3, Theorem B.3).  At `f = 1`
the note's expression divides by zero; Lean's convention makes it `min 1 0 = 0`, and the default
is never used at `f = 1`, so nothing depends on this. -/
def dstar : ℝ := min 1 (G.f * (G.b - G.c) / (G.c * (1 - G.f)))

/-- (P1) The language contains the constant program `K[D]` ("always defect") — the only
constant program Theorem B's proof uses. -/
def HasAllD : Prop :=
  (∃ K : Prog₁, ∀ r, G.ev₁ K r = 0) ∧ (∃ K : Prog₂, ∀ r, G.ev₂ K r = 0)

/-- (P1) in full: the language contains every constant program `K[α]`, `α ∈ Δ({C,D}) ≅ [0,1]`. -/
def HasConstants : Prop :=
  (∀ α ∈ Set.Icc (0 : ℝ) 1, ∃ K : Prog₁, ∀ r, G.ev₁ K r = α) ∧
  (∀ α ∈ Set.Icc (0 : ℝ) 1, ∃ K : Prog₂, ∀ r, G.ev₂ K r = α)

/-- `(T₁, T₂)` is the **grounded trigger with default `d`** of note §3: on a failed read it
cooperates with probability `d`; on a successful read it cooperates iff the other's text is its
twin trigger, else defects. -/
def IsTrigger (d : ℝ) (T₁ : Prog₁) (T₂ : Prog₂) : Prop :=
  G.ev₁ T₁ none = d ∧ G.ev₂ T₂ none = d ∧
  G.ev₁ T₁ (some T₂) = 1 ∧ G.ev₂ T₂ (some T₁) = 1 ∧
  (∀ π, π ≠ T₂ → G.ev₁ T₁ (some π) = 0) ∧ (∀ π, π ≠ T₁ → G.ev₂ T₂ (some π) = 0)

/-- (P2′) The language contains the grounded trigger with every default `d ∈ [0,1]`.  This is
note §2's (P2) for `a* = (C, C)` extended to a *mixed* default, which the attainment construction
of Theorem B.3 needs (`d*` is in general interior). -/
def HasTriggers : Prop := ∀ d ∈ Set.Icc (0 : ℝ) 1, ∃ T₁ T₂, G.IsTrigger d T₁ T₂

/-! ### Basic computations -/

lemma expAct_u₁ (p q : ℝ) : expAct G.u₁ p q = G.b * q - G.c * p := by
  simp [expAct, bern, u₁]; ring

lemma expAct_u₂ (p q : ℝ) : expAct G.u₂ p q = G.b * p - G.c * q := by
  simp [expAct, bern, u₁, u₂]; ring

/-- `U_1 = b x_2 − c x_1` (note §3). -/
lemma U₁_eq (π₁ : Prog₁) (π₂ : Prog₂) : G.U₁ π₁ π₂ = G.b * G.x₂ π₁ π₂ - G.c * G.x₁ π₁ π₂ := by
  simp [U₁, expAct_u₁, readProb, bern, act₁, act₂, x₁, x₂]; ring

/-- `U_2 = b x_1 − c x_2`. -/
lemma U₂_eq (π₁ : Prog₁) (π₂ : Prog₂) : G.U₂ π₁ π₂ = G.b * G.x₁ π₁ π₂ - G.c * G.x₂ π₁ π₂ := by
  simp [U₂, expAct_u₂, readProb, bern, act₁, act₂, x₁, x₂]; ring

lemma avg_eq (π₁ : Prog₁) (π₂ : Prog₂) :
    G.avg π₁ π₂ = (G.b - G.c) * ((G.x₁ π₁ π₂ + G.x₂ π₁ π₂) / 2) := by
  simp only [avg, U₁_eq, U₂_eq]; ring

lemma f_nonneg : 0 ≤ G.f := G.f_mem.1
lemma f_le_one : G.f ≤ 1 := G.f_mem.2
lemma b_pos : 0 < G.b := G.c_pos.trans G.c_lt_b

lemma x₁_mem (π₁ : Prog₁) (π₂ : Prog₂) : G.x₁ π₁ π₂ ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 := G.ev₁_mem π₁ (some π₂); have h2 := G.ev₁_mem π₁ none
  have := G.f_mem
  simp only [Set.mem_Icc, x₁] at *
  constructor <;> nlinarith

lemma x₂_mem (π₁ : Prog₁) (π₂ : Prog₂) : G.x₂ π₁ π₂ ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 := G.ev₂_mem π₂ (some π₁); have h2 := G.ev₂_mem π₂ none
  have := G.f_mem
  simp only [Set.mem_Icc, x₂] at *
  constructor <;> nlinarith

/-! ### The upper bound: `c x_i ≤ b f` at every program equilibrium (note §3, proof of B) -/

/-- At any program equilibrium, player 1's on-path cooperation rate obeys `c x_1 ≤ b f ρ_2 ≤ b f`
(deviation of player 1 to `K[D]`). -/
lemma c_mul_x₁_le (hK : ∃ K : Prog₁, ∀ r, G.ev₁ K r = 0) {π₁ : Prog₁} {π₂ : Prog₂}
    (h : G.IsProgramEquilibrium π₁ π₂) : G.c * G.x₁ π₁ π₂ ≤ G.b * G.f := by
  obtain ⟨K, hK⟩ := hK
  have hdev := h.1 K
  rw [U₁_eq, U₁_eq] at hdev
  have hx1K : G.x₁ K π₂ = 0 := by simp [x₁, hK]
  have hρD := G.ev₂_mem π₂ (some K)
  have hρ := G.ev₂_mem π₂ (some π₁)
  have hd := G.ev₂_mem π₂ none
  have hf := G.f_mem
  have hb := G.b_pos
  simp only [Set.mem_Icc] at *
  simp only [x₂, hx1K] at hdev
  nlinarith [mul_nonneg (mul_nonneg hb.le hf.1) hρD.1,
    mul_nonneg (mul_nonneg hb.le hf.1) (sub_nonneg.2 hρ.2)]

/-- Symmetric bound for player 2. -/
lemma c_mul_x₂_le (hK : ∃ K : Prog₂, ∀ r, G.ev₂ K r = 0) {π₁ : Prog₁} {π₂ : Prog₂}
    (h : G.IsProgramEquilibrium π₁ π₂) : G.c * G.x₂ π₁ π₂ ≤ G.b * G.f := by
  obtain ⟨K, hK⟩ := hK
  have hdev := h.2 K
  rw [U₂_eq, U₂_eq] at hdev
  have hx2K : G.x₂ π₁ K = 0 := by simp [x₂, hK]
  have hρD := G.ev₁_mem π₁ (some K)
  have hρ := G.ev₁_mem π₁ (some π₂)
  have hd := G.ev₁_mem π₁ none
  have hf := G.f_mem
  have hb := G.b_pos
  simp only [Set.mem_Icc] at *
  simp only [x₁, hx2K] at hdev
  nlinarith [mul_nonneg (mul_nonneg hb.le hf.1) hρD.1,
    mul_nonneg (mul_nonneg hb.le hf.1) (sub_nonneg.2 hρ.2)]

lemma x_le_min (hK : G.HasAllD) {π₁ : Prog₁} {π₂ : Prog₂} (h : G.IsProgramEquilibrium π₁ π₂) :
    G.x₁ π₁ π₂ ≤ min 1 (G.f * G.b / G.c) ∧ G.x₂ π₁ π₂ ≤ min 1 (G.f * G.b / G.c) := by
  have h1 := G.c_mul_x₁_le hK.1 h
  have h2 := G.c_mul_x₂_le hK.2 h
  have hc := G.c_pos
  refine ⟨le_min (G.x₁_mem π₁ π₂).2 ?_, le_min (G.x₂_mem π₁ π₂).2 ?_⟩
  · rw [le_div_iff₀ hc]; linarith
  · rw [le_div_iff₀ hc]; linarith

/-- **Theorem B.2, upper bound.**  Every program equilibrium has average payoff `≤ W*(f)`. -/
theorem avg_le_Wstar (hK : G.HasAllD) {π₁ : Prog₁} {π₂ : Prog₂}
    (h : G.IsProgramEquilibrium π₁ π₂) : G.avg π₁ π₂ ≤ G.Wstar := by
  obtain ⟨h1, h2⟩ := G.x_le_min hK h
  rw [avg_eq, Wstar]
  have hbc : 0 ≤ G.b - G.c := by linarith [G.c_lt_b]
  exact mul_le_mul_of_nonneg_left (by linarith) hbc

/-! ### Attainment: the grounded trigger with default `d` -/

/-- The trigger with default `d` is a program equilibrium iff `(b − c) f ≥ c (1 − f) d`
(note §3: "the equilibrium condition `(b−c)(f + (1−f)d) ≥ b(1−f)d`").  Sufficiency direction. -/
theorem trigger_isEquilibrium {d : ℝ} {T₁ : Prog₁} {T₂ : Prog₂}
    (hT : G.IsTrigger d T₁ T₂) (hcond : G.c * (1 - G.f) * d ≤ (G.b - G.c) * G.f) :
    G.IsProgramEquilibrium T₁ T₂ := by
  obtain ⟨hd₁, hd₂, hρ₁, hρ₂, hpun₁, hpun₂⟩ := hT
  have hf := G.f_mem
  have hc := G.c_pos
  have hb := G.b_pos
  simp only [Set.mem_Icc] at hf
  constructor
  · intro π'
    by_cases hπ : π' = T₁
    · subst hπ; exact le_rfl
    rw [U₁_eq, U₁_eq]
    have hx2' : G.x₂ π' T₂ = (1 - G.f) * d := by simp [x₂, hpun₂ π' hπ, hd₂]
    have hx2 : G.x₂ T₁ T₂ = G.f + (1 - G.f) * d := by simp [x₂, hρ₂, hd₂]
    have hx1 : G.x₁ T₁ T₂ = G.f + (1 - G.f) * d := by simp [x₁, hρ₁, hd₁]
    have hx1' := (G.x₁_mem π' T₂).1
    rw [hx2', hx2, hx1]
    nlinarith [mul_nonneg hc.le hx1']
  · intro π'
    by_cases hπ : π' = T₂
    · subst hπ; exact le_rfl
    rw [U₂_eq, U₂_eq]
    have hx1' : G.x₁ T₁ π' = (1 - G.f) * d := by simp [x₁, hpun₁ π' hπ, hd₁]
    have hx2 : G.x₂ T₁ T₂ = G.f + (1 - G.f) * d := by simp [x₂, hρ₂, hd₂]
    have hx1 : G.x₁ T₁ T₂ = G.f + (1 - G.f) * d := by simp [x₁, hρ₁, hd₁]
    have hx2' := (G.x₂_mem T₁ π').1
    rw [hx1', hx2, hx1]
    nlinarith [mul_nonneg hc.le hx2']

/-- Necessity direction of the trigger equilibrium condition (needs `K[D]` for the deviation). -/
theorem trigger_isEquilibrium_iff (hK : G.HasAllD) {d : ℝ}
    {T₁ : Prog₁} {T₂ : Prog₂} (hT : G.IsTrigger d T₁ T₂) :
    G.IsProgramEquilibrium T₁ T₂ ↔ G.c * (1 - G.f) * d ≤ (G.b - G.c) * G.f := by
  refine ⟨fun h => ?_, G.trigger_isEquilibrium hT⟩
  have := G.c_mul_x₁_le hK.1 h
  have hx1 : G.x₁ T₁ T₂ = G.f + (1 - G.f) * d := by simp [x₁, hT.2.2.1, hT.1]
  rw [hx1] at this
  nlinarith

/-- Average payoff of the trigger with default `d` on path: `(b − c)(f + (1 − f) d)`. -/
lemma avg_trigger {d : ℝ} {T₁ : Prog₁} {T₂ : Prog₂} (hT : G.IsTrigger d T₁ T₂) :
    G.avg T₁ T₂ = (G.b - G.c) * (G.f + (1 - G.f) * d) := by
  obtain ⟨hd₁, hd₂, hρ₁, hρ₂, -, -⟩ := hT
  rw [avg_eq]
  have hx2 : G.x₂ T₁ T₂ = G.f + (1 - G.f) * d := by simp [x₂, hρ₂, hd₂]
  have hx1 : G.x₁ T₁ T₂ = G.f + (1 - G.f) * d := by simp [x₁, hρ₁, hd₁]
  rw [hx1, hx2]; ring

lemma dstar_mem : G.dstar ∈ Set.Icc (0 : ℝ) 1 := by
  have hf := G.f_mem; have hc := G.c_pos; have hbc := G.c_lt_b
  simp only [Set.mem_Icc] at hf
  refine ⟨le_min zero_le_one ?_, min_le_left _ _⟩
  apply div_nonneg (mul_nonneg hf.1 (by linarith)) (mul_nonneg hc.le (by linarith))

/-- The trigger with default `d*` satisfies the equilibrium condition. -/
lemma dstar_cond : G.c * (1 - G.f) * G.dstar ≤ (G.b - G.c) * G.f := by
  have hf := G.f_mem; have hc := G.c_pos; have hbc := G.c_lt_b
  simp only [Set.mem_Icc] at hf
  unfold dstar
  rcases eq_or_lt_of_le hf.2 with h1 | h1
  · rw [h1]; simp; linarith
  have hpos : 0 < G.c * (1 - G.f) := mul_pos hc (by linarith)
  rcases min_cases 1 (G.f * (G.b - G.c) / (G.c * (1 - G.f))) with ⟨h, hle⟩ | ⟨h, hlt⟩
  · rw [h]; rw [le_div_iff₀ hpos] at hle; linarith
  · rw [h, mul_div_cancel₀ _ hpos.ne']; ring_nf; exact le_rfl

/-- On-path cooperation rate of the `d*` trigger: `f + (1 − f) d* = min(1, f b / c)`. -/
lemma f_add_dstar : G.f + (1 - G.f) * G.dstar = min 1 (G.f * G.b / G.c) := by
  have hf := G.f_mem; have hc := G.c_pos; have hbc := G.c_lt_b
  simp only [Set.mem_Icc] at hf
  unfold dstar
  rcases eq_or_lt_of_le hf.2 with h1 | h1
  · rw [h1]; simp
    rw [one_le_div₀ hc]; linarith
  have hpos : 0 < G.c * (1 - G.f) := mul_pos hc (by linarith)
  rcases min_cases 1 (G.f * (G.b - G.c) / (G.c * (1 - G.f))) with ⟨h, hle⟩ | ⟨h, hlt⟩
  · rw [h]; rw [le_div_iff₀ hpos] at hle
    rw [min_eq_left]; · ring
    rw [le_div_iff₀ hc]; nlinarith
  · rw [h]
    rw [div_lt_iff₀ hpos] at hlt
    rw [min_eq_right]
    · field_simp; ring
    · rw [div_le_iff₀ hc]; nlinarith

/-- **Theorem B.3 (attainment).**  The grounded trigger with default `d*` is a program
equilibrium with average payoff exactly `W*(f)`. -/
theorem trigger_dstar_attains {T₁ : Prog₁} {T₂ : Prog₂} (hT : G.IsTrigger G.dstar T₁ T₂) :
    G.IsProgramEquilibrium T₁ T₂ ∧ G.avg T₁ T₂ = G.Wstar := by
  refine ⟨G.trigger_isEquilibrium hT G.dstar_cond, ?_⟩
  rw [G.avg_trigger hT, f_add_dstar, Wstar]

/-- **Theorem B.3 (grim bound).**  The default-defect grim trigger (`d = 0`) is a program
equilibrium at every `f` but earns only `f (b − c) ≤ W*(f)`. -/
theorem grim_trigger {T₁ : Prog₁} {T₂ : Prog₂} (hT : G.IsTrigger 0 T₁ T₂) :
    G.IsProgramEquilibrium T₁ T₂ ∧ G.avg T₁ T₂ = G.f * (G.b - G.c) ∧
      G.f * (G.b - G.c) ≤ G.Wstar := by
  have hf := G.f_mem; have hc := G.c_pos; have hbc := G.c_lt_b
  simp only [Set.mem_Icc] at hf
  refine ⟨G.trigger_isEquilibrium hT (by
    simp; exact mul_nonneg (by linarith) hf.1), ?_, ?_⟩
  · rw [G.avg_trigger hT]; ring
  · unfold Wstar
    have hbc' : 0 ≤ G.b - G.c := by linarith
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hbc'
    apply le_min hf.2
    rw [le_div_iff₀ hc]; nlinarith

/-! ### Theorem B, assembled -/

/-- **Theorem B.2 (the efficiency frontier).**  In the two-player donation game with reading
fidelity `f`, if the language contains `K[D]` (P1) and the grounded triggers (P2′), the maximum
of the average payoff `(U_1 + U_2)/2` over *all* program equilibria (any defaults, any rules,
symmetric or not) is exactly `W*(f) = (b − c)·min(1, f b / c)`. -/
theorem theoremB_frontier (hK : G.HasAllD) (hT : G.HasTriggers) :
    IsGreatest {w : ℝ | ∃ π₁ π₂, G.IsProgramEquilibrium π₁ π₂ ∧ G.avg π₁ π₂ = w} G.Wstar := by
  constructor
  · obtain ⟨T₁, T₂, hT⟩ := hT G.dstar G.dstar_mem
    obtain ⟨heq, havg⟩ := G.trigger_dstar_attains hT
    exact ⟨T₁, T₂, heq, havg⟩
  · rintro w ⟨π₁, π₂, heq, rfl⟩
    exact G.avg_le_Wstar hK heq

/-- **Theorem B.1.**  Full mutual cooperation (the payoff profile `(b − c, b − c)`, equivalently
`x_1 = x_2 = 1`) is a program equilibrium payoff iff `f b ≥ c`. -/
theorem theoremB_cooperation_iff (hK : G.HasAllD) (hT : G.HasTriggers) :
    (∃ π₁ π₂, G.IsProgramEquilibrium π₁ π₂ ∧ G.U₁ π₁ π₂ = G.b - G.c ∧ G.U₂ π₁ π₂ = G.b - G.c)
      ↔ G.c ≤ G.f * G.b := by
  have hf := G.f_mem; have hc := G.c_pos; have hbc := G.c_lt_b
  simp only [Set.mem_Icc] at hf
  constructor
  · rintro ⟨π₁, π₂, heq, h1, h2⟩
    -- `U_1 = U_2 = b − c` forces `x_1 = x_2 = 1`, then `c x_1 ≤ b f`.
    rw [U₁_eq] at h1; rw [U₂_eq] at h2
    have hx1 := G.x₁_mem π₁ π₂; have hx2 := G.x₂_mem π₁ π₂
    simp only [Set.mem_Icc] at hx1 hx2
    have hx1' : G.x₁ π₁ π₂ = 1 := by nlinarith
    have := G.c_mul_x₁_le hK.1 heq
    rw [hx1'] at this; linarith
  · intro h
    obtain ⟨T₁, T₂, hT⟩ := hT 1 ⟨zero_le_one, le_rfl⟩
    refine ⟨T₁, T₂, G.trigger_isEquilibrium hT (by nlinarith), ?_, ?_⟩
    · rw [U₁_eq]
      have hx2 : G.x₂ T₁ T₂ = 1 := by simp [x₂, hT.2.2.2.1, hT.2.1]
      have hx1 : G.x₁ T₁ T₂ = 1 := by simp [x₁, hT.2.2.1, hT.1]
      rw [hx1, hx2]; ring
    · rw [U₂_eq]
      have hx2 : G.x₂ T₁ T₂ = 1 := by simp [x₂, hT.2.2.2.1, hT.2.1]
      have hx1 : G.x₁ T₁ T₂ = 1 := by simp [x₁, hT.2.2.1, hT.1]
      rw [hx1, hx2]; ring

/-- Variant of B.1 phrased on cooperation on every branch: there is a program equilibrium in
which both programs cooperate with probability one on every read branch iff `f b ≥ c`. -/
theorem theoremB_cooperation_iff' (hK : G.HasAllD) (hT : G.HasTriggers) :
    (∃ π₁ π₂, G.IsProgramEquilibrium π₁ π₂ ∧ G.x₁ π₁ π₂ = 1 ∧ G.x₂ π₁ π₂ = 1)
      ↔ G.c ≤ G.f * G.b := by
  rw [← G.theoremB_cooperation_iff hK hT]
  constructor
  · rintro ⟨π₁, π₂, heq, h1, h2⟩
    exact ⟨π₁, π₂, heq, by rw [U₁_eq, h1, h2]; ring, by rw [U₂_eq, h1, h2]; ring⟩
  · rintro ⟨π₁, π₂, heq, h1, h2⟩
    rw [U₁_eq] at h1; rw [U₂_eq] at h2
    have hx1 := G.x₁_mem π₁ π₂; have hx2 := G.x₂_mem π₁ π₂
    simp only [Set.mem_Icc] at hx1 hx2
    exact ⟨π₁, π₂, heq, by nlinarith [G.c_lt_b], by nlinarith [G.c_lt_b]⟩

end DonationProgramGame

/-! ## Part A: the noisy program game `G^f` for a general finite game (note §2)

Base game `G = (N, (A_i), (u_i))` with `N = ι` finite, finite action sets `A i`, payoffs
`u i : (∀ j, A j) → ℝ` extended multilinearly to independent mixed profiles.  Each player `i`
submits a program from `Prog i`; `ev i π r` is the mixed action `ev_i(π_i, read_i)` with
`r = none` the failed read `⊥` and `r = some π_{−i}` a successful read of the others' texts.
Reads succeed independently with probabilities `f i`. -/

/-- A mixed action on a finite action set `A`: nonnegative weights summing to one
(`Δ(A_i)` in the note). -/
def IsMixed {A : Type*} [Fintype A] (α : A → ℝ) : Prop := (∀ a, 0 ≤ α a) ∧ ∑ a, α a = 1

/-- The pure action `a` as a mixed action (Dirac mass). -/
def pureAct {A : Type*} [DecidableEq A] (a : A) : A → ℝ := fun a' => if a' = a then 1 else 0

lemma pureAct_isMixed {A : Type*} [Fintype A] [DecidableEq A] (a : A) : IsMixed (pureAct a) :=
  ⟨fun a' => by unfold pureAct; split_ifs <;> norm_num, by simp [pureAct]⟩

/-- A product of mixed actions has nonnegative weights. -/
lemma prod_mixed_nonneg {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, Fintype (A i)]
    (α : ∀ j, A j → ℝ) (hα : ∀ j, IsMixed (α j)) (a : ∀ j, A j) : 0 ≤ ∏ j, α j (a j) :=
  Finset.prod_nonneg fun j _ => (hα j).1 (a j)

/-- A product of mixed actions has weights summing to one. -/
lemma sum_prod_mixed {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]
    (α : ∀ j, A j → ℝ) (hα : ∀ j, IsMixed (α j)) : ∑ a : ∀ j, A j, ∏ j, α j (a j) = 1 := by
  have := Finset.prod_univ_sum (fun j : ι => (Finset.univ : Finset (A j))) (fun j a => α j a)
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  simp [(hα _).2]

/-- The noisy program game `G^f` of note §2. -/
structure NoisyProgramGame (ι : Type*) [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] (Prog : ι → Type*) where
  /-- payoff `u_i(a)` of the base game at the pure profile `a` -/
  u : ι → (∀ j, A j) → ℝ
  /-- reading fidelity `f_i` of player `i` -/
  f : ι → ℝ
  f_mem : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1
  /-- total evaluator `ev_i : Π_i × (Π_{−i} ⊔ {⊥}) → Δ(A_i)` -/
  ev : ∀ i, Prog i → Option (∀ j : {j // j ≠ i}, Prog j) → (A i → ℝ)
  ev_mixed : ∀ i π r, IsMixed (ev i π r)

namespace NoisyProgramGame

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Fintype (A i)]
  [∀ i, DecidableEq (A i)] {Prog : ι → Type*} (G : NoisyProgramGame ι A Prog)

/-- The multilinear extension `u_i(α)` of `u_i` to an independent mixed profile `α`. -/
def uMix (i : ι) (α : ∀ j, A j → ℝ) : ℝ := ∑ a : ∀ j, A j, (∏ j, α j (a j)) * G.u i a

/-- Probability of the read-outcome vector `R` (`R j = true` iff player `j`'s read succeeded):
reads are independent with success probabilities `f_j`. -/
def w (R : ι → Bool) : ℝ := ∏ j, (if R j then G.f j else 1 - G.f j)

/-- The texts of everyone but `j`, as seen by `j` on a successful read. -/
def others (π : ∀ j, Prog j) (j : ι) : ∀ k : {k // k ≠ j}, Prog k := fun k => π k

/-- The mixed action player `j` realises under the program profile `π` and reads `R`. -/
def play (π : ∀ j, Prog j) (R : ι → Bool) (j : ι) : A j → ℝ :=
  G.ev j (π j) (if R j then some (others π j) else none)

/-- Payoff `U_i(π) = E[u_i(a)]`, the expectation over the independent read coins and the
independent action draws (note §2). -/
def U (i : ι) (π : ∀ j, Prog j) : ℝ := ∑ R : ι → Bool, G.w R * G.uMix i (G.play π R)

/-- A **program equilibrium**: a Nash equilibrium of `G^f`. -/
def IsProgramEquilibrium (π : ∀ j, Prog j) : Prop :=
  ∀ i (π' : Prog i), G.U i (Function.update π i π') ≤ G.U i π

/-- (P1) the language of every player contains all constant programs `K[α_i]`. -/
def HasConstants : Prop :=
  ∀ i (α : A i → ℝ), IsMixed α → ∃ K : Prog i, ∀ r, G.ev i K r = α

/-- `T` is a **trigger profile** for the pure profile `a*` with (text-independent) punishment
profiles `m i : ∏_{j ≠ i} Δ(A_j)` (note §2, (P2)): `ev_j(T_j, ⊥) = a*_j`, `ev_j(T_j, T_{−j}) = a*_j`,
and `ev_j(T_j, π_{−j}) = m^i_j` whenever exactly one index `i ≠ j` has `π_i ≠ T_i`. -/
def IsTriggerProfile (astar : ∀ j, A j) (m : ∀ i : ι, ∀ j : {j // j ≠ i}, A j.1 → ℝ)
    (T : ∀ j, Prog j) : Prop :=
  (∀ j, G.ev j (T j) none = pureAct (astar j)) ∧
  (∀ j, G.ev j (T j) (some (others T j)) = pureAct (astar j)) ∧
  (∀ j i (hij : j ≠ i) (π' : Prog i), π' ≠ T i →
    G.ev j (T j) (some (others (Function.update T i π') j)) = m i ⟨j, hij⟩)

/-- The profile in which the non-readers (`R j = false`) play `a*_j`, the readers play the
punishment `β_j`, and the deviator's own slot `i` holds a placeholder (`a*_i`). -/
def punishBase (astar : ∀ j, A j) (i : ι) (β : ∀ j : {j // j ≠ i}, A j → ℝ) (R : ι → Bool)
    (j : ι) : A j → ℝ :=
  if h : j = i then pureAct (astar j) else if R j then β ⟨j, h⟩ else pureAct (astar j)

/-- The deviation profile `(α_i, a*_{−i∖S}, β_S)` with `S = {j ≠ i | R j}`. -/
def devProf (astar : ∀ j, A j) (i : ι) (α : A i → ℝ) (β : ∀ j : {j // j ≠ i}, A j → ℝ)
    (R : ι → Bool) : ∀ j, A j → ℝ :=
  Function.update (punishBase astar i β R) i α

/-- `E_S [u_i(α_i, a*_{−i∖S}, β_S)]`: expectation over the read outcomes of the others. (The
summation also runs over the deviator's own read coin `R i`, on which the summand does not
depend, so this is the note's expectation over `S ⊆ N ∖ {i}`.) -/
def devValue (astar : ∀ j, A j) (i : ι) (α : A i → ℝ) (β : ∀ j : {j // j ≠ i}, A j → ℝ) : ℝ :=
  ∑ R : ι → Bool, G.w R * G.uMix i (devProf astar i α β R)

/-- The `f`-deviation value `D_i(f) = max_{a_i} E_S[u_i(a_i, a*_{−i∖S}, m^i_S)]` with the fixed
punishment profile `m^i` (note §2; there `m^i` is a minmax profile, but the definition and
Theorem A.1 make sense for any punishment profile). -/
def D (astar : ∀ j, A j) (m : ∀ i : ι, ∀ j : {j // j ≠ i}, A j.1 → ℝ) (i : ι) : ℝ :=
  (Finset.univ : Finset (A i)).sup' ⟨astar i, Finset.mem_univ _⟩
    (fun a => G.devValue astar i (pureAct a) (m i))

/-- The best-punishment deviation value
`D̃_i(f) = max_{α_i ∈ Δ(A_i)} min_{β_{−i} ∈ ∏ Δ(A_j)} E_S[u_i(α_i, a*_{−i∖S}, β_S)]` (note §2). -/
def Dtilde (astar : ∀ j, A j) (i : ι) : ℝ :=
  ⨆ α : {α : A i → ℝ // IsMixed α},
    ⨅ β : ∀ j : {j // j ≠ i}, {β : A j → ℝ // IsMixed β},
      G.devValue astar i α.1 (fun j => (β j).1)

/-! ### Lemmas on weights and the multilinear extension -/

lemma w_nonneg (R : ι → Bool) : 0 ≤ G.w R := by
  unfold w
  apply Finset.prod_nonneg
  intro j _
  have := G.f_mem j
  simp only [Set.mem_Icc] at this
  split_ifs <;> linarith

lemma sum_w : ∑ R : ι → Bool, G.w R = 1 := by
  unfold w
  have := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset Bool))
    (fun j (b : Bool) => if b then G.f j else 1 - G.f j)
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  simp

/-- The read vector `R` with coordinate `i` replaced by `b`. -/
lemma sum_w_split (i : ι) (F : (ι → Bool) → ℝ) :
    ∑ R : ι → Bool, G.w R * F R =
      ∑ R' : {j // j ≠ i} → Bool,
        (∏ j : {j // j ≠ i}, (if R' j then G.f j else 1 - G.f j)) *
          (G.f i * F (Function.update (fun j => if h : j = i then true else R' ⟨j, h⟩) i true) +
           (1 - G.f i) *
             F (Function.update (fun j => if h : j = i then true else R' ⟨j, h⟩) i false)) := by
  classical
  -- split the sum over `ι → Bool` as a sum over `Bool × ({j // j ≠ i} → Bool)`
  let e := (Equiv.piSplitAt i (fun _ : ι => Bool)).symm
  rw [← Fintype.sum_equiv e (fun p => G.w (e p) * F (e p)) (fun R => G.w R * F R) (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun R' _ => ?_
  have he : ∀ b, e (b, R') = Function.update (fun j => if h : j = i then true else R' ⟨j, h⟩) i b := by
    intro b; funext j
    simp only [e, Equiv.piSplitAt_symm_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  have hw : ∀ b, G.w (e (b, R')) =
      (if b then G.f i else 1 - G.f i) *
        ∏ j : {j // j ≠ i}, (if R' j then G.f j else 1 - G.f j) := by
    intro b
    unfold w
    rw [Fintype.prod_eq_mul_prod_compl i]
    congr 1
    · rw [he]; simp
    · rw [Finset.prod_subtype (p := fun j => j ≠ i) ({i}ᶜ : Finset ι) (by simp)]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [he]
      have hj : (j : ι) ≠ i := j.2
      simp [Function.update_apply, hj]
  have hwt : G.w (e (true, R')) = G.f i * ∏ j : {j // j ≠ i}, (if R' j then G.f j else 1 - G.f j) := by
    rw [hw]; simp
  have hwf : G.w (e (false, R')) =
      (1 - G.f i) * ∏ j : {j // j ≠ i}, (if R' j then G.f j else 1 - G.f j) := by
    rw [hw]; simp
  rw [Fintype.sum_bool, hwt, hwf, he, he]
  ring

/-- Marginalising the deviator's own read coin: if `F` does not depend on `R i`, the expectation
over all reads equals the expectation over the others' reads. -/
lemma sum_w_mul_indep (i : ι) (h : Bool → ℝ) (F : (ι → Bool) → ℝ)
    (hF : ∀ R b, F (Function.update R i b) = F R) :
    ∑ R : ι → Bool, G.w R * (h (R i) * F R) =
      (G.f i * h true + (1 - G.f i) * h false) * ∑ R : ι → Bool, G.w R * F R := by
  rw [G.sum_w_split i (fun R => h (R i) * F R), G.sum_w_split i F]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun R' _ => ?_
  simp only [Function.update_self, hF]
  ring

lemma uMix_pure (i : ι) (a : ∀ j, A j) : G.uMix i (fun j => pureAct (a j)) = G.u i a := by
  unfold uMix pureAct
  have : ∀ x : ∀ j, A j, (∏ j, (if x j = a j then (1 : ℝ) else 0)) = if x = a then 1 else 0 := by
    intro x
    rw [Finset.prod_boole]
    congr 1
    simp [funext_iff]
  simp_rw [this]
  simp [Finset.sum_ite_eq']

/-- Pulling the `i`-th coordinate out of the multilinear extension:
`u_i(α) = Σ_{a_i} α_i(a_i) u_i(a_i, α_{−i})`. -/
lemma uMix_eq_sum_update (i : ι) (α : ∀ j, A j → ℝ) :
    G.uMix i α = ∑ a : A i, α i a * G.uMix i (Function.update α i (pureAct a)) := by
  unfold uMix
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hsplit : ∀ (β : ∀ j, A j → ℝ), (∏ j, β j (x j)) = β i (x i) * ∏ j ∈ {i}ᶜ, β j (x j) :=
    fun β => Fintype.prod_eq_mul_prod_compl i _
  rw [hsplit]
  have : ∀ a : A i, (∏ j, Function.update α i (pureAct a) j (x j)) =
      (if x i = a then 1 else 0) * ∏ j ∈ {i}ᶜ, α j (x j) := by
    intro a
    rw [hsplit]
    congr 1
    · simp [pureAct]
    · refine Finset.prod_congr rfl fun j hj => ?_
      have : j ≠ i := by simpa using hj
      simp [Function.update_of_ne this]
  simp_rw [this]
  have : ∀ a : A i, α i a * ((if x i = a then (1 : ℝ) else 0) * (∏ j ∈ {i}ᶜ, α j (x j)) * G.u i x) =
      if x i = a then α i a * (∏ j ∈ {i}ᶜ, α j (x j)) * G.u i x else 0 := by
    intro a; split_ifs <;> simp <;> ring
  simp_rw [this]
  rw [Finset.sum_ite_eq]
  simp

/-- A convex combination of payoffs is at least the minimum payoff. -/
lemma uMix_ge_inf (i : ι) (α : ∀ j, A j → ℝ) (hα : ∀ j, IsMixed (α j)) (a₀ : ∀ j, A j) :
    (Finset.univ : Finset (∀ j, A j)).inf' ⟨a₀, Finset.mem_univ _⟩ (G.u i) ≤ G.uMix i α := by
  unfold uMix
  calc (Finset.univ : Finset (∀ j, A j)).inf' ⟨a₀, Finset.mem_univ _⟩ (G.u i)
      = ∑ a : ∀ j, A j, (∏ j, α j (a j)) *
          (Finset.univ : Finset (∀ j, A j)).inf' ⟨a₀, Finset.mem_univ _⟩ (G.u i) := by
        rw [← Finset.sum_mul, sum_prod_mixed α hα, one_mul]
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ a))
        exact prod_mixed_nonneg α hα a

lemma punishBase_mixed (astar : ∀ j, A j) (i : ι) (β : ∀ j : {j // j ≠ i}, A j → ℝ)
    (hβ : ∀ j, IsMixed (β j)) (R : ι → Bool) (j : ι) : IsMixed (punishBase astar i β R j) := by
  unfold punishBase
  split_ifs
  · exact pureAct_isMixed _
  · exact hβ _
  · exact pureAct_isMixed _

lemma devProf_mixed (astar : ∀ j, A j) (i : ι) (α : A i → ℝ) (hα : IsMixed α)
    (β : ∀ j : {j // j ≠ i}, A j → ℝ) (hβ : ∀ j, IsMixed (β j)) (R : ι → Bool) (j : ι) :
    IsMixed (devProf astar i α β R j) := by
  unfold devProf
  by_cases h : j = i
  · subst h; simpa using hα
  · rw [Function.update_of_ne h]; exact punishBase_mixed astar i β hβ R j

/-- `E_S[·]` is bounded below by the minimum payoff (needed for the `⨅` in `D̃`). -/
lemma devValue_ge_inf (astar : ∀ j, A j) (i : ι) (α : A i → ℝ) (hα : IsMixed α)
    (β : ∀ j : {j // j ≠ i}, A j → ℝ) (hβ : ∀ j, IsMixed (β j)) :
    (Finset.univ : Finset (∀ j, A j)).inf' ⟨astar, Finset.mem_univ _⟩ (G.u i) ≤
      G.devValue astar i α β := by
  unfold devValue
  calc (Finset.univ : Finset (∀ j, A j)).inf' ⟨astar, Finset.mem_univ _⟩ (G.u i)
      = ∑ R : ι → Bool, G.w R *
          (Finset.univ : Finset (∀ j, A j)).inf' ⟨astar, Finset.mem_univ _⟩ (G.u i) := by
        rw [← Finset.sum_mul, G.sum_w, one_mul]
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro R _
        apply mul_le_mul_of_nonneg_left _ (G.w_nonneg R)
        exact G.uMix_ge_inf i _ (devProf_mixed astar i α hα β hβ R) astar

/-- On-path payoff of a profile that plays `a*` on every branch. -/
lemma U_eq_of_plays (i : ι) (astar : ∀ j, A j) (π : ∀ j, Prog j)
    (h₀ : ∀ j, G.ev j (π j) none = pureAct (astar j))
    (h₁ : ∀ j, G.ev j (π j) (some (others π j)) = pureAct (astar j)) :
    G.U i π = G.u i astar := by
  unfold U
  have : ∀ R, G.play π R = fun j => pureAct (astar j) := by
    intro R; funext j
    unfold play
    split_ifs
    · exact h₁ j
    · exact h₀ j
  simp_rw [this, G.uMix_pure]
  rw [← Finset.sum_mul, G.sum_w, one_mul]

/-! ### Theorem A.1 (sufficiency) -/

/-- **Theorem A.1 (sufficiency).**  If `u_i(a*) ≥ D_i(f)` for all `i`, the trigger profile `T`
is a program equilibrium of `G^f` with payoff `u(a*)` (it plays `a*` on every branch of the
reads).  The punishment profiles `m^i` need not even be mixed for this direction; in the note
they are minmax profiles, which is the special case. -/
theorem theoremA_sufficiency (astar : ∀ j, A j) (m : ∀ i : ι, ∀ j : {j // j ≠ i}, A j.1 → ℝ)
    (T : ∀ j, Prog j) (hT : G.IsTriggerProfile astar m T)
    (hD : ∀ i, G.D astar m i ≤ G.u i astar) :
    G.IsProgramEquilibrium T ∧ ∀ i, G.U i T = G.u i astar := by
  obtain ⟨hT₀, hT₁, hT₂⟩ := hT
  have hUT : ∀ i, G.U i T = G.u i astar := fun i => G.U_eq_of_plays i astar T hT₀ hT₁
  refine ⟨fun i π' => ?_, hUT⟩
  rw [hUT i]
  by_cases hπ : π' = T i
  · rw [hπ, Function.update_eq_self, hUT i]
  -- the deviator's own realised mixture, as a function of its read coin
  set α : Bool → A i → ℝ := fun b => G.ev i π' (if b then some (others T i) else none) with hα
  have hothers : others (Function.update T i π') i = others T i := by
    funext k; simp [others, Function.update_of_ne k.2]
  have hplay : ∀ R, G.play (Function.update T i π') R =
      Function.update (punishBase astar i (m i) R) i (α (R i)) := by
    intro R; funext j
    unfold play
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self, hα, hothers]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      unfold punishBase
      rw [dif_neg hj]
      split_ifs with hR
      · exact hT₂ j i hj π' hπ
      · exact hT₀ j
  -- expand `U_i` and pull the deviator's coordinate out
  unfold U
  have hexp : ∀ R, G.uMix i (G.play (Function.update T i π') R) =
      ∑ a : A i, α (R i) a * G.uMix i (devProf astar i (pureAct a) (m i) R) := by
    intro R
    rw [hplay, G.uMix_eq_sum_update i]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Function.update_self]
    unfold devProf
    rw [Function.update_idem]
  simp_rw [hexp]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- each inner sum factorises through the read-independent deviation profile
  have hindep : ∀ (a : A i) (R : ι → Bool) (b : Bool),
      G.uMix i (devProf astar i (pureAct a) (m i) (Function.update R i b)) =
        G.uMix i (devProf astar i (pureAct a) (m i) R) := by
    intro a R b
    congr 1
    unfold devProf punishBase
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj, hj]
  have hfac : ∀ a : A i, ∑ R : ι → Bool, G.w R * (α (R i) a * G.uMix i (devProf astar i (pureAct a) (m i) R))
      = (G.f i * α true a + (1 - G.f i) * α false a) *
          G.devValue astar i (pureAct a) (m i) := by
    intro a
    unfold devValue
    exact G.sum_w_mul_indep i (fun b => α b a) _ (hindep a)
  calc ∑ a : A i, ∑ R : ι → Bool, G.w R * (α (R i) a * G.uMix i (devProf astar i (pureAct a) (m i) R))
      = ∑ a : A i, (G.f i * α true a + (1 - G.f i) * α false a) *
          G.devValue astar i (pureAct a) (m i) := Finset.sum_congr rfl fun a _ => hfac a
    _ ≤ ∑ a : A i, (G.f i * α true a + (1 - G.f i) * α false a) * G.D astar m i := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left
        · exact Finset.le_sup' (fun a => G.devValue astar i (pureAct a) (m i)) (Finset.mem_univ a)
        · have hf := G.f_mem i
          simp only [Set.mem_Icc] at hf
          have h1 := (G.ev_mixed i π' (some (others T i))).1 a
          have h2 := (G.ev_mixed i π' none).1 a
          simp only [hα, Bool.false_eq_true, ite_true, ite_false]
          nlinarith
    _ = G.D astar m i := by
        rw [← Finset.sum_mul]
        have h1 := (G.ev_mixed i π' (some (others T i))).2
        have h2 := (G.ev_mixed i π' none).2
        simp only [hα, Bool.false_eq_true, ite_true, ite_false]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1, h2]
        ring
    _ ≤ G.u i astar := hD i

/-! ### Theorem A.2 (necessity) -/

/-- **Theorem A.2 (necessity).**  If a program profile plays `a*` on every branch
(`ev_j(π_j, ⊥) = ev_j(π_j, π_{−j}) = a*_j`) and is a program equilibrium, and the languages
contain the constant programs (P1), then `u_i(a*) ≥ D̃_i(f)` for all `i`. -/
theorem theoremA_necessity (hK : G.HasConstants) (astar : ∀ j, A j) (π : ∀ j, Prog j)
    (h₀ : ∀ j, G.ev j (π j) none = pureAct (astar j))
    (h₁ : ∀ j, G.ev j (π j) (some (others π j)) = pureAct (astar j))
    (heq : G.IsProgramEquilibrium π) :
    ∀ i, G.Dtilde astar i ≤ G.u i astar := by
  intro i
  unfold Dtilde
  have : Nonempty {α : A i → ℝ // IsMixed α} := ⟨⟨pureAct (astar i), pureAct_isMixed _⟩⟩
  apply ciSup_le
  rintro ⟨α, hα⟩
  obtain ⟨K, hKα⟩ := hK i α hα
  -- the readers' responses to the constant deviation `K[α]`
  set β₀ : ∀ j : {j // j ≠ i}, {β : A j → ℝ // IsMixed β} :=
    fun j => ⟨G.ev j (π j) (some (others (Function.update π i K) j)), G.ev_mixed _ _ _⟩ with hβ₀
  have hbdd : BddBelow (Set.range fun β : ∀ j : {j // j ≠ i}, {β : A j → ℝ // IsMixed β} =>
      G.devValue astar i α (fun j => (β j).1)) := by
    refine ⟨(Finset.univ : Finset (∀ j, A j)).inf' ⟨astar, Finset.mem_univ _⟩ (G.u i), ?_⟩
    rintro _ ⟨β, rfl⟩
    exact G.devValue_ge_inf astar i α hα _ (fun j => (β j).2)
  refine ciInf_le_of_le hbdd β₀ ?_
  -- the deviation `K[α]` pays exactly `E_S u_i(α, a*_{−i∖S}, β₀_S)`
  have hplay : ∀ R, G.play (Function.update π i K) R = devProf astar i α (fun j => (β₀ j).1) R := by
    intro R; funext j
    unfold play devProf
    by_cases hj : j = i
    · subst hj; simp [hKα]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      unfold punishBase
      rw [dif_neg hj]
      split_ifs with hR
      · rfl
      · exact h₀ j
  have hU : G.U i (Function.update π i K) = G.devValue astar i α (fun j => (β₀ j).1) := by
    unfold U devValue
    simp_rw [hplay]
  rw [← hU, ← G.U_eq_of_plays i astar π h₀ h₁]
  exact heq i K

end NoisyProgramGame

/-! ## Part C: training reveals the same threshold (note §4, Theorem C)

The agent's cooperation probability is `p = σ(z)` (logit `z`); its partner is a reader of
fidelity `f`, rule `φ` and default `d`, playing `q = (1 − f) d + f φ(p)` (note §1), so the
legibility is `r = f φ′(p)`.  The donation-game payoff is `u = b q − c p`. -/

namespace Revelation

open Real

/-- Reader's realised cooperation probability `q = (1 − f) d + f φ(p)` (note §1). -/
def readerPlay (f d : ℝ) (φ : ℝ → ℝ) (p : ℝ) : ℝ := (1 - f) * d + f * φ p

/-- Donation-game expected payoff `u(p, q) = b q − c p` (note §1). -/
def payoff (b c p q : ℝ) : ℝ := b * q - c * p

/-- The agent's expected reward as a function of its logit, with the reader's response to the
*policy* included: the objective whose total derivative policy-level credit estimates. -/
def policyObjective (b c f d : ℝ) (φ : ℝ → ℝ) (z : ℝ) : ℝ :=
  payoff b c (sigmoid z) (readerPlay f d φ (sigmoid z))

/-- The same reward with the reader's realised action `q` held fixed (a stop-gradient through
the read): the objective whose derivative action-level credit estimates. -/
def actionObjective (b c q : ℝ) (z : ℝ) : ℝ := payoff b c (sigmoid z) q

/-- **Theorem C.1 (policy-level credit).**  `dE[u]/dz = (b f φ′(p) − c) p (1 − p)` with
`p = σ(z)`, i.e. `(r b − c) p (1 − p)` with `r = f φ′(p)`. -/
theorem hasDerivAt_policyObjective (b c f d : ℝ) {φ : ℝ → ℝ} {φ' z : ℝ}
    (hφ : HasDerivAt φ φ' (sigmoid z)) :
    HasDerivAt (policyObjective b c f d φ)
      ((b * (f * φ') - c) * (sigmoid z * (1 - sigmoid z))) z := by
  have hσ := hasDerivAt_sigmoid z
  have hφσ : HasDerivAt (fun z => φ (sigmoid z)) (φ' * (sigmoid z * (1 - sigmoid z))) z :=
    hφ.comp z hσ
  unfold policyObjective payoff readerPlay
  have := ((hφσ.const_mul f).const_add ((1 - f) * d)).const_mul b |>.sub (hσ.const_mul c)
  convert this using 1
  ring

/-- **Theorem C.1 (action-level credit).**  With the reader's realised action held fixed,
`∂E[u]/∂z = −c p (1 − p)`, at every fidelity. -/
theorem hasDerivAt_actionObjective (b c q z : ℝ) :
    HasDerivAt (actionObjective b c q) (-c * (sigmoid z * (1 - sigmoid z))) z := by
  have hσ := hasDerivAt_sigmoid z
  unfold actionObjective payoff
  have := (hasDerivAt_const z (b * q)).sub (hσ.const_mul c)
  convert this using 1
  ring

/-- The derivative of the policy-level objective through a **mirror** (`φ = id`, `r = f`). -/
theorem hasDerivAt_policyObjective_mirror (b c f d z : ℝ) :
    HasDerivAt (policyObjective b c f d id) ((f * b - c) * (sigmoid z * (1 - sigmoid z))) z := by
  have := hasDerivAt_policyObjective b c f d (φ := id) (z := z) (hasDerivAt_id _)
  convert this using 1; ring

/-- **Theorem C.2 (the threshold).**  Through a mirror of fidelity `f`, the selfish policy-level
gradient is positive at every logit iff `f b > c`, negative at every logit iff `f b < c`, and
zero iff `f b = c`; so the sign of the drift toward cooperation is the sign of `f b − c`,
exactly Theorem B.1's threshold (equilibrium: `f b ≥ c`; positive drift: `f b > c`). -/
theorem policy_gradient_sign (b c f d z : ℝ) :
    (0 < deriv (policyObjective b c f d id) z ↔ c < f * b) ∧
    (deriv (policyObjective b c f d id) z < 0 ↔ f * b < c) ∧
    (deriv (policyObjective b c f d id) z = 0 ↔ f * b = c) := by
  rw [(hasDerivAt_policyObjective_mirror b c f d z).deriv]
  have hp : 0 < sigmoid z * (1 - sigmoid z) :=
    mul_pos (sigmoid_pos z) (by linarith [sigmoid_lt_one z])
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h; by_contra h'; push_neg at h'
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 h') hp.le]
    · intro h; exact mul_pos (by linarith) hp
  · constructor
    · intro h; by_contra h'; push_neg at h'
      nlinarith [mul_nonneg (sub_nonneg.2 h') hp.le]
    · intro h; exact mul_neg_of_neg_of_pos (by linarith) hp
  · rw [mul_eq_zero, or_iff_left hp.ne']; constructor <;> intro h <;> linarith

/-- **Theorem C.2 (action-level credit defects at every `r`).**  The action-level gradient is
strictly negative at every logit and every fidelity, rule and default. -/
theorem action_gradient_neg {c : ℝ} (hc : 0 < c) (b q z : ℝ) :
    deriv (actionObjective b c q) z < 0 := by
  rw [(hasDerivAt_actionObjective b c q z).deriv]
  have hp : 0 < sigmoid z * (1 - sigmoid z) :=
    mul_pos (sigmoid_pos z) (by linarith [sigmoid_lt_one z])
  nlinarith

/-- **Theorem C.3 (homo moralis).**  For any payoff `u : ℝ × ℝ → ℝ` differentiable at the
symmetric profile `(x, x)` with derivative `L` (so `u₁ = L(1,0)`, `u₂ = L(0,1)`), the selfish
legible agent's first-order condition through a mirror of fidelity `f` with default `y`,
`d/dx u(x, (1 − f) y + f x)`, evaluated at `y = x`, equals `u₁(x,x) + f u₂(x,x)`, which is
also `d/dx [(1 − κ) u(x, y) + κ u(x, x)]` at `y = x` with `κ = f`: Alger–Weibull's homo moralis
with degree of morality `κ = r`.  (The note states this for the multilinear payoff of a
symmetric finite game, which is differentiable; this is the general chain-rule identity.) -/
theorem homo_moralis {u : ℝ × ℝ → ℝ} {x f : ℝ} {L : ℝ × ℝ →L[ℝ] ℝ}
    (hu : HasFDerivAt u L (x, x)) :
    HasDerivAt (fun t => u (t, (1 - f) * x + f * t)) (L (1, 0) + f * L (0, 1)) x ∧
    HasDerivAt (fun t => (1 - f) * u (t, x) + f * u (t, t)) (L (1, 0) + f * L (0, 1)) x := by
  have hpath : HasDerivAt (fun t : ℝ => ((t, (1 - f) * x + f * t) : ℝ × ℝ)) ((1 : ℝ), f) x := by
    refine HasDerivAt.prodMk (hasDerivAt_id x) ?_
    have := ((hasDerivAt_id x).const_mul f).const_add ((1 - f) * x)
    simpa using this
  have hpt : ((x, (1 - f) * x + f * x) : ℝ × ℝ) = (x, x) := by ext <;> simp; ring
  have hdiag : HasDerivAt (fun t : ℝ => ((t, t) : ℝ × ℝ)) ((1 : ℝ), (1 : ℝ)) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_id x)
  have hhor : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x x)
  have hL : ∀ v w : ℝ, L (v, w) = v * L (1, 0) + w * L (0, 1) := by
    intro v w
    have : ((v, w) : ℝ × ℝ) = v • ((1 : ℝ), (0 : ℝ)) + w • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  constructor
  · have hu' : HasFDerivAt u L (x, (1 - f) * x + f * x) := by rw [hpt]; exact hu
    have := HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => ((t, (1 - f) * x + f * t) : ℝ × ℝ))
      x hu' hpath
    exact this.congr_deriv (by rw [hL]; ring)
  · have h1 := (HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => ((t, x) : ℝ × ℝ)) x hu hhor).const_mul
      (1 - f)
    have h2 := (HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => ((t, t) : ℝ × ℝ)) x hu hdiag).const_mul f
    exact (h1.add h2).congr_deriv (by rw [hL 1 1]; ring)

/-! ### Theorem C.2, the continuous-time flow -/

open Filter Topology

/-- A logit obeying `ż = k σ(z)(1 − σ(z))` with `k > 0` escapes to `+∞`. -/
lemma tendsto_atTop_of_flow {z : ℝ → ℝ} {k : ℝ} (hk : 0 < k)
    (hz : ∀ t, HasDerivAt z (k * (sigmoid (z t) * (1 - sigmoid (z t)))) t) :
    Tendsto z atTop atTop := by
  have hdiff : Differentiable ℝ z := fun t => (hz t).differentiableAt
  have hpos : ∀ t, 0 < deriv z t := fun t => by
    rw [(hz t).deriv]
    exact mul_pos hk (mul_pos (sigmoid_pos _) (by linarith [sigmoid_lt_one (z t)]))
  have hmono : Monotone z := monotone_of_deriv_nonneg hdiff fun t => (hpos t).le
  apply hmono.tendsto_atTop_atTop
  intro b
  by_contra hcon
  push_neg at hcon
  -- on `[0, ∞)` the logit stays in `[z 0, b)`, so its speed is at least `δ > 0`
  set δ := k * (sigmoid (z 0) * (1 - sigmoid b)) with hδ
  have hδpos : 0 < δ :=
    mul_pos hk (mul_pos (sigmoid_pos _) (by linarith [sigmoid_lt_one b]))
  have hg : MonotoneOn (fun t => z t - δ * t) (Set.Ici 0) := by
    have hd : ∀ t, HasDerivAt (fun t => z t - δ * t)
        (k * (sigmoid (z t) * (1 - sigmoid (z t))) - δ) t := fun t =>
      (hz t).sub (((hasDerivAt_id t).const_mul δ).congr_deriv (by ring))
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hd t).deriv, hδ, sub_nonneg]
      apply mul_le_mul_of_nonneg_left _ hk.le
      have h1 : sigmoid (z 0) ≤ sigmoid (z t) := sigmoid_le (hmono (le_of_lt ht))
      have h2 : sigmoid (z t) ≤ sigmoid b := sigmoid_le (hcon t).le
      have h3 := sigmoid_pos (z 0)
      have h4 := sigmoid_lt_one b
      nlinarith
  -- hence `z t ≥ z 0 + δ t`, which exceeds `b` for large `t`
  set T := (b - z 0) / δ + 1 with hT
  have hT0 : 0 ≤ T := by
    have : 0 ≤ (b - z 0) / δ := div_nonneg (by linarith [hcon 0]) hδpos.le
    linarith
  have := hg (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hT0) hT0
  simp only [mul_zero, sub_zero] at this
  have hδT : δ * T = (b - z 0) + δ := by rw [hT, mul_add, mul_div_cancel₀ _ hδpos.ne', mul_one]
  have := hcon T
  linarith

/-- **Theorem C.2 (the policy-level flow through a mirror).**  Let `z : ℝ → ℝ` solve the
continuous-time policy-level flow `ż = p(1 − p)(f b − c)`, `p = σ(z)`.  Then `p → 1` iff
`f b > c`; `p → 0` iff `f b < c`; and `p` is stationary iff `f b = c`.  Every start is interior
since `p = σ(z) ∈ (0,1)`. -/
theorem flow_mirror {b c f : ℝ} {z : ℝ → ℝ}
    (hz : ∀ t, HasDerivAt z ((f * b - c) * (sigmoid (z t) * (1 - sigmoid (z t)))) t) :
    (Tendsto (fun t => sigmoid (z t)) atTop (𝓝 1) ↔ c < f * b) ∧
    (Tendsto (fun t => sigmoid (z t)) atTop (𝓝 0) ↔ f * b < c) ∧
    ((∀ t, z t = z 0) ↔ f * b = c) := by
  -- the three regimes
  have hup : c < f * b → Tendsto (fun t => sigmoid (z t)) atTop (𝓝 1) := fun h =>
    tendsto_sigmoid_atTop.comp (tendsto_atTop_of_flow (by linarith) hz)
  have hdown : f * b < c → Tendsto (fun t => sigmoid (z t)) atTop (𝓝 0) := by
    intro h
    have hz' : ∀ t, HasDerivAt (fun t => -z t)
        ((c - f * b) * (sigmoid (-z t) * (1 - sigmoid (-z t)))) t := fun t => by
      have := (hz t).neg
      refine this.congr_deriv ?_
      rw [sigmoid_neg]; ring
    have hneg := tendsto_atTop_of_flow (by linarith) hz'
    have : Tendsto (fun t => sigmoid (-(-z t))) atTop (𝓝 0) :=
      (tendsto_sigmoid_atBot.comp (tendsto_neg_atTop_atBot.comp hneg))
    simpa using this
  have hconst : f * b = c → ∀ t, z t = z 0 := by
    intro h t
    have hd : ∀ t, deriv z t = 0 := fun t => by rw [(hz t).deriv, h]; ring
    exact is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt) hd t 0
  have hne : ∀ t, sigmoid (z t) ≠ 1 := fun t => (sigmoid_lt_one _).ne
  have hne0 : ∀ t, sigmoid (z t) ≠ 0 := fun t => (sigmoid_pos _).ne'
  refine ⟨⟨fun h => ?_, hup⟩, ⟨fun h => ?_, hdown⟩, ⟨fun h => ?_, hconst⟩⟩
  · rcases lt_trichotomy c (f * b) with h1 | h1 | h1
    · exact h1
    · exfalso
      have hc := hconst h1.symm
      have : Tendsto (fun t => sigmoid (z t)) atTop (𝓝 (sigmoid (z 0))) := by
        simp_rw [hc]; exact tendsto_const_nhds
      exact hne 0 (tendsto_nhds_unique this h)
    · exfalso
      have := tendsto_nhds_unique (hdown h1) h
      norm_num at this
  · rcases lt_trichotomy (f * b) c with h1 | h1 | h1
    · exact h1
    · exfalso
      have hc := hconst h1
      have : Tendsto (fun t => sigmoid (z t)) atTop (𝓝 (sigmoid (z 0))) := by
        simp_rw [hc]; exact tendsto_const_nhds
      exact hne0 0 (tendsto_nhds_unique this h)
    · exfalso
      have := tendsto_nhds_unique (hup h1) h
      norm_num at this
  · by_contra hne'
    rcases lt_or_gt_of_ne hne' with h1 | h1
    · -- `z` strictly decreasing contradicts constancy
      have := (hz 1).deriv
      have hd : deriv z 1 = 0 := by
        have hc : z = fun _ => z 0 := funext h
        rw [hc]; simp
      rw [hd] at this
      have hp : 0 < sigmoid (z 1) * (1 - sigmoid (z 1)) :=
        mul_pos (sigmoid_pos _) (by linarith [sigmoid_lt_one (z 1)])
      nlinarith [mul_pos (sub_pos.2 h1) hp]
    · have := (hz 1).deriv
      have hd : deriv z 1 = 0 := by
        have hc : z = fun _ => z 0 := funext h
        rw [hc]; simp
      rw [hd] at this
      have hp : 0 < sigmoid (z 1) * (1 - sigmoid (z 1)) :=
        mul_pos (sigmoid_pos _) (by linarith [sigmoid_lt_one (z 1)])
      nlinarith [mul_pos (sub_pos.2 h1) hp]

end Revelation

end BoundaryTheorem.Cooperation

end
