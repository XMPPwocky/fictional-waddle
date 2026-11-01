import Mathlib

/-!
# Known finite horizon unravels cooperation; a geometric horizon need not

MODELLING ASSUMPTION. Two players play the stage prisoner's dilemma with payoffs
`S < P < R < T` (stage payoff `u a b` to a player choosing `a` against `b`) for exactly `N`
rounds, with `N` common knowledge, undiscounted total payoff. A history is the list of past
action pairs (most recent first, first component = player 1); a strategy maps every history
(on or off the path of play) to an action. "Subgame-perfect reasoning" is modelled as
`IsSPE`: at every history `h` with `h.length ≤ N`, each player's strategy maximizes their
total payoff over the remaining `N - h.length` rounds against the other's strategy, among
all alternative strategies. The continuation value under all-defect play is
`V 0 = 0`, `V (k+1) = P + V k`.

PROVED.
* `V_eq`: `V k = k * P`.
* `stage_strict`: `R + V k < T + V k` and `S + V k < P + V k`.
* `stage_strict_of_indep`: for any continuation `cont : Act → Act → ℝ` that does not depend
  on this round's own action, `u C b + cont C b < u D b + cont D b` for each opponent action
  `b`.
* `pay1_allD`, `pay2_allD`: if both strategies defect at every history of the remaining
  rounds, the continuation is `V k` for each player, whatever history (in particular whatever
  this round's actions) led there. This is the induction hypothesis that makes the
  continuation independent of the current round's actions.
* `spe_defects`: in every SPE of the `N`-round game, both players defect at every history of
  length `< N` (on and off path); proof by backward induction using a one-history deviation.
* `allD_isSPE`, `isSPE_iff`: conversely, any profile defecting at every history of length
  `< N` is an SPE; so the SPEs are exactly those profiles. `isSPE_allD` gives existence.
* `spe_outcome`, `spe_pay1`, `spe_pay2`: every SPE has outcome path `replicate N (D, D)` and
  total payoff `N * P` for each player.
* Geometric horizon (restated, not imported): `coop_hasSum`, `dev_hasSum` give
  `∑ R δ^t = R/(1-δ)` and `T + ∑_{t≥1} P δ^t = T + δ P/(1-δ)`; `grim_threshold`:
  for `0 ≤ δ < 1`, `T + δ P/(1-δ) ≤ R/(1-δ) ↔ (T-R)/(T-P) ≤ δ`; `punish_strict`:
  `S + δ P/(1-δ) < P/(1-δ)`; `threshold_lt_one`, `coop_near_one`: the threshold lies in
  `[0,1)`, so every `δ ∈ [(T-R)/(T-P), 1)` passes the grim-trigger checks.

INTERPRETED (not formalized as theorems about an infinite game).
* `δ` is read as the probability that another round is played (a geometric, unknown
  horizon); for a risk-neutral player the expected total equals the `δ`-discounted sum.
* `grim_threshold` and `punish_strict` are the two one-shot-deviation checks for grim
  trigger (on the cooperative path, and in the punishment phase). That these checks
  suffice for subgame perfection in the infinite game (one-shot deviation principle) is
  not proved here.
-/

namespace KnownHorizonUnravelsB

inductive Act
  | C
  | D
  deriving DecidableEq, Repr

open Act

/-- Stage payoff to a player choosing `a` against an opponent choosing `b`. -/
def u (T R P S : ℝ) : Act → Act → ℝ
  | C, C => R
  | C, D => S
  | D, C => T
  | D, D => P

/-- Continuation value with `k` rounds left when both defect in every remaining round. -/
def V (P : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => P + V P k

theorem V_eq (P : ℝ) (k : ℕ) : V P k = k * P := by
  induction k with
  | zero => simp [V]
  | succ k ih => simp only [V, ih]; push_cast; ring

/-- Past action pairs, most recent first; first component is player 1's action. -/
abbrev History := List (Act × Act)

abbrev Strategy := History → Act

/-- Player 1's total payoff over `k` remaining rounds starting from history `h`. -/
def pay1 (T R P S : ℝ) (σ1 σ2 : Strategy) : History → ℕ → ℝ
  | _, 0 => 0
  | h, k + 1 => u T R P S (σ1 h) (σ2 h) + pay1 T R P S σ1 σ2 ((σ1 h, σ2 h) :: h) k

/-- Player 2's total payoff over `k` remaining rounds starting from history `h`. -/
def pay2 (T R P S : ℝ) (σ1 σ2 : Strategy) : History → ℕ → ℝ
  | _, 0 => 0
  | h, k + 1 => u T R P S (σ2 h) (σ1 h) + pay2 T R P S σ1 σ2 ((σ1 h, σ2 h) :: h) k

/-- Outcome path over `k` remaining rounds starting from history `h`, in play order. -/
def outcome (σ1 σ2 : Strategy) : History → ℕ → List (Act × Act)
  | _, 0 => []
  | h, k + 1 => (σ1 h, σ2 h) :: outcome σ1 σ2 ((σ1 h, σ2 h) :: h) k

/-- Subgame perfect equilibrium of the `N`-round game: at every history of length `≤ N`,
each player's strategy is a best response over the remaining rounds. -/
def IsSPE (T R P S : ℝ) (N : ℕ) (σ1 σ2 : Strategy) : Prop :=
  ∀ h : History, h.length ≤ N →
    (∀ τ : Strategy, pay1 T R P S τ σ2 h (N - h.length) ≤ pay1 T R P S σ1 σ2 h (N - h.length)) ∧
    (∀ τ : Strategy, pay2 T R P S σ1 τ h (N - h.length) ≤ pay2 T R P S σ1 σ2 h (N - h.length))

variable {T R P S : ℝ}

/-- (1) Defection is a strict best response in a round with `k+1` rounds left when the
continuation is `V k` regardless of this round's actions. -/
theorem stage_strict (hTR : R < T) (hPS : S < P) (k : ℕ) :
    R + V P k < T + V P k ∧ S + V P k < P + V P k :=
  ⟨by linarith, by linarith⟩

/-- (1), general form: any continuation independent of the player's own current action. -/
theorem stage_strict_of_indep (hTR : R < T) (hPS : S < P) (b : Act)
    (cont : Act → Act → ℝ) (hc : cont C b = cont D b) :
    u T R P S C b + cont C b < u T R P S D b + cont D b := by
  rw [hc]; cases b <;> simp [u] <;> linarith

/-- Defecting on every remaining history yields continuation `V k` for player 1. -/
theorem pay1_allD (σ1 σ2 : Strategy) (k : ℕ) : ∀ h : History,
    (∀ h' : History, h.length ≤ h'.length → h'.length < h.length + k →
      σ1 h' = D ∧ σ2 h' = D) →
    pay1 T R P S σ1 σ2 h k = V P k := by
  induction k with
  | zero => intro h _; simp [pay1, V]
  | succ k ih =>
    intro h hD
    obtain ⟨h1, h2⟩ := hD h le_rfl (by omega)
    simp only [pay1, V, h1, h2, u]
    rw [ih]
    intro h' hl hl'
    simp only [List.length_cons] at hl hl'
    exact hD h' (by omega) (by omega)

/-- Defecting on every remaining history yields continuation `V k` for player 2. -/
theorem pay2_allD (σ1 σ2 : Strategy) (k : ℕ) : ∀ h : History,
    (∀ h' : History, h.length ≤ h'.length → h'.length < h.length + k →
      σ1 h' = D ∧ σ2 h' = D) →
    pay2 T R P S σ1 σ2 h k = V P k := by
  induction k with
  | zero => intro h _; simp [pay2, V]
  | succ k ih =>
    intro h hD
    obtain ⟨h1, h2⟩ := hD h le_rfl (by omega)
    simp only [pay2, V, h1, h2, u]
    rw [ih]
    intro h' hl hl'
    simp only [List.length_cons] at hl hl'
    exact hD h' (by omega) (by omega)

/-- Against an opponent defecting on every remaining history, player 1 gets at most `V k`. -/
theorem pay1_le_of_opp_allD (hPS : S < P) (τ σ2 : Strategy) (k : ℕ) : ∀ h : History,
    (∀ h' : History, h.length ≤ h'.length → h'.length < h.length + k → σ2 h' = D) →
    pay1 T R P S τ σ2 h k ≤ V P k := by
  induction k with
  | zero => intro h _; simp [pay1, V]
  | succ k ih =>
    intro h hD
    have h2 := hD h le_rfl (by omega)
    simp only [pay1, V, h2]
    have hu : u T R P S (τ h) D ≤ P := by
      cases τ h <;> simp only [u] <;> linarith
    have hrest : pay1 T R P S τ σ2 ((τ h, D) :: h) k ≤ V P k := by
      apply ih
      intro h' hl hl'
      simp only [List.length_cons] at hl hl'
      exact hD h' (by omega) (by omega)
    linarith

/-- Against an opponent defecting on every remaining history, player 2 gets at most `V k`. -/
theorem pay2_le_of_opp_allD (hPS : S < P) (σ1 τ : Strategy) (k : ℕ) : ∀ h : History,
    (∀ h' : History, h.length ≤ h'.length → h'.length < h.length + k → σ1 h' = D) →
    pay2 T R P S σ1 τ h k ≤ V P k := by
  induction k with
  | zero => intro h _; simp [pay2, V]
  | succ k ih =>
    intro h hD
    have h1 := hD h le_rfl (by omega)
    simp only [pay2, V, h1]
    have hu : u T R P S (τ h) D ≤ P := by
      cases τ h <;> simp only [u] <;> linarith
    have hrest : pay2 T R P S σ1 τ ((D, τ h) :: h) k ≤ V P k := by
      apply ih
      intro h' hl hl'
      simp only [List.length_cons] at hl hl'
      exact hD h' (by omega) (by omega)
    linarith

/-- (2) Backward induction: in every SPE both players defect at every history of
length `< N`, on and off the path of play. -/
theorem spe_defects (hTR : R < T) (hPS : S < P) {N : ℕ} {σ1 σ2 : Strategy}
    (hS : IsSPE T R P S N σ1 σ2) :
    ∀ h : History, h.length < N → σ1 h = D ∧ σ2 h = D := by
  suffices key : ∀ k : ℕ, ∀ h : History, N - k ≤ h.length → h.length < N →
      σ1 h = D ∧ σ2 h = D by
    intro h hlt
    exact key N h (by omega) hlt
  intro k
  induction k with
  | zero => intro h hlo hlt; omega
  | succ k ih =>
    intro h hlo hlt
    by_cases hk : N - k ≤ h.length
    · exact ih h hk hlt
    have hrem : N - h.length = k + 1 := by omega
    obtain ⟨hs1, hs2⟩ := hS h hlt.le
    rw [hrem] at hs1 hs2
    -- every history strictly after `h` and before the end is all-defect
    have later : ∀ h' : History, (h.length + 1) ≤ h'.length →
        h'.length < (h.length + 1) + k → σ1 h' = D ∧ σ2 h' = D := by
      intro h' hl hl'
      exact ih h' (by omega) (by omega)
    have ne_of_len : ∀ h' : History, (h.length + 1) ≤ h'.length → h' ≠ h := by
      intro h' hl heq
      rw [heq] at hl
      omega
    constructor
    · -- player 1
      let τ : Strategy := fun h' => if h' = h then D else σ1 h'
      have hτh : τ h = D := by simp [τ]
      have hdev := hs1 τ
      simp only [pay1] at hdev
      rw [hτh] at hdev
      have c1 : pay1 T R P S τ σ2 ((D, σ2 h) :: h) k = V P k := by
        apply pay1_allD
        intro h' hl hl'
        simp only [List.length_cons] at hl hl'
        have hne := ne_of_len h' hl
        have := later h' hl hl'
        simpa [τ, hne] using this
      have c2 : pay1 T R P S σ1 σ2 ((σ1 h, σ2 h) :: h) k = V P k := by
        apply pay1_allD
        intro h' hl hl'
        simp only [List.length_cons] at hl hl'
        exact later h' hl hl'
      rw [c1, c2] at hdev
      cases ha : σ1 h with
      | D => rfl
      | C =>
        rw [ha] at hdev
        cases hb : σ2 h <;> rw [hb] at hdev <;> simp [u] at hdev <;> linarith
    · -- player 2
      let τ : Strategy := fun h' => if h' = h then D else σ2 h'
      have hτh : τ h = D := by simp [τ]
      have hdev := hs2 τ
      simp only [pay2] at hdev
      rw [hτh] at hdev
      have c1 : pay2 T R P S σ1 τ ((σ1 h, D) :: h) k = V P k := by
        apply pay2_allD
        intro h' hl hl'
        simp only [List.length_cons] at hl hl'
        have hne := ne_of_len h' hl
        have := later h' hl hl'
        simpa [τ, hne] using this
      have c2 : pay2 T R P S σ1 σ2 ((σ1 h, σ2 h) :: h) k = V P k := by
        apply pay2_allD
        intro h' hl hl'
        simp only [List.length_cons] at hl hl'
        exact later h' hl hl'
      rw [c1, c2] at hdev
      cases hb : σ2 h with
      | D => rfl
      | C =>
        rw [hb] at hdev
        cases ha : σ1 h <;> rw [ha] at hdev <;> simp [u] at hdev <;> linarith

/-- Conversely, any profile defecting at every history of length `< N` is an SPE. -/
theorem allD_isSPE (hPS : S < P) {N : ℕ} {σ1 σ2 : Strategy}
    (hD : ∀ h : History, h.length < N → σ1 h = D ∧ σ2 h = D) :
    IsSPE T R P S N σ1 σ2 := by
  intro h hl
  have cond : ∀ h' : History, h.length ≤ h'.length →
      h'.length < h.length + (N - h.length) → σ1 h' = D ∧ σ2 h' = D := by
    intro h' _ hl'
    exact hD h' (by omega)
  refine ⟨fun τ => ?_, fun τ => ?_⟩
  · rw [pay1_allD σ1 σ2 _ h cond]
    exact pay1_le_of_opp_allD hPS τ σ2 _ h (fun h' a b => (cond h' a b).2)
  · rw [pay2_allD σ1 σ2 _ h cond]
    exact pay2_le_of_opp_allD hPS σ1 τ _ h (fun h' a b => (cond h' a b).1)

/-- The SPEs of the `N`-round game are exactly the profiles defecting at every history
of length `< N`. -/
theorem isSPE_iff (hTR : R < T) (hPS : S < P) (N : ℕ) (σ1 σ2 : Strategy) :
    IsSPE T R P S N σ1 σ2 ↔ ∀ h : History, h.length < N → σ1 h = D ∧ σ2 h = D :=
  ⟨spe_defects hTR hPS, allD_isSPE hPS⟩

/-- Existence: unconditional defection is an SPE. -/
theorem isSPE_allD (hPS : S < P) (N : ℕ) :
    IsSPE T R P S N (fun _ => D) (fun _ => D) :=
  allD_isSPE hPS (fun _ _ => ⟨rfl, rfl⟩)

theorem outcome_allD (σ1 σ2 : Strategy) (k : ℕ) : ∀ h : History,
    (∀ h' : History, h.length ≤ h'.length → h'.length < h.length + k →
      σ1 h' = D ∧ σ2 h' = D) →
    outcome σ1 σ2 h k = List.replicate k (D, D) := by
  induction k with
  | zero => intro h _; simp [outcome]
  | succ k ih =>
    intro h hD
    obtain ⟨h1, h2⟩ := hD h le_rfl (by omega)
    simp only [outcome, h1, h2, List.replicate_succ]
    rw [ih]
    intro h' hl hl'
    simp only [List.length_cons] at hl hl'
    exact hD h' (by omega) (by omega)

/-- (2) Every SPE has outcome path: defect in every one of the `N` rounds. -/
theorem spe_outcome (hTR : R < T) (hPS : S < P) {N : ℕ} {σ1 σ2 : Strategy}
    (hS : IsSPE T R P S N σ1 σ2) :
    outcome σ1 σ2 [] N = List.replicate N (D, D) :=
  outcome_allD σ1 σ2 N [] (fun h' _ hl' => spe_defects hTR hPS hS h' (by simpa using hl'))

/-- (2) Every SPE gives player 1 total payoff `N * P`. -/
theorem spe_pay1 (hTR : R < T) (hPS : S < P) {N : ℕ} {σ1 σ2 : Strategy}
    (hS : IsSPE T R P S N σ1 σ2) :
    pay1 T R P S σ1 σ2 [] N = N * P := by
  rw [pay1_allD σ1 σ2 N [] (fun h' _ hl' => spe_defects hTR hPS hS h' (by simpa using hl')),
    V_eq]

/-- (2) Every SPE gives player 2 total payoff `N * P`. -/
theorem spe_pay2 (hTR : R < T) (hPS : S < P) {N : ℕ} {σ1 σ2 : Strategy}
    (hS : IsSPE T R P S N σ1 σ2) :
    pay2 T R P S σ1 σ2 [] N = N * P := by
  rw [pay2_allD σ1 σ2 N [] (fun h' _ hl' => spe_defects hTR hPS hS h' (by simpa using hl')),
    V_eq]

/-! ### (3) Contrast: geometric horizon (continuation probability `δ`) -/

/-- Value of perpetual mutual cooperation. -/
theorem coop_hasSum {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1) :
    HasSum (fun t : ℕ => R * δ ^ t) (R / (1 - δ)) := by
  have := (hasSum_geometric_of_lt_one h0 h1).mul_left R
  simpa [div_eq_mul_inv] using this

/-- Value of the punishment stream after a first-round deviation: `∑_{t≥1} P δ^t`. -/
theorem dev_hasSum {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1) :
    HasSum (fun t : ℕ => P * δ ^ (t + 1)) (δ * P / (1 - δ)) := by
  have := (hasSum_geometric_of_lt_one h0 h1).mul_left (P * δ)
  convert this using 1
  · funext t; ring
  · field_simp

/-- Grim-trigger check on the cooperative path: cooperating forever is at least as good
as defecting once and then receiving `P` forever iff `δ ≥ (T-R)/(T-P)`. -/
theorem grim_threshold (hTR : R < T) (hRP : P < R) {δ : ℝ} (h1 : δ < 1) :
    T + δ * P / (1 - δ) ≤ R / (1 - δ) ↔ (T - R) / (T - P) ≤ δ := by
  have hd : 0 < 1 - δ := by linarith
  have hTP : 0 < T - P := by linarith
  have key : R / (1 - δ) - (T + δ * P / (1 - δ)) = (δ * (T - P) - (T - R)) / (1 - δ) := by
    field_simp; ring
  rw [← sub_nonneg, key, le_div_iff₀ hd, zero_mul, div_le_iff₀ hTP, sub_nonneg]

/-- Grim-trigger check in the punishment phase: continuing to defect beats a one-round
switch to cooperation. -/
theorem punish_strict (hPS : S < P) {δ : ℝ} (h1 : δ < 1) :
    S + δ * P / (1 - δ) < P / (1 - δ) := by
  have hd : 1 - δ ≠ 0 := by linarith
  have : P / (1 - δ) = P + δ * P / (1 - δ) := by field_simp; ring
  rw [this]; linarith

theorem threshold_nonneg (hTR : R < T) (hRP : P < R) : 0 ≤ (T - R) / (T - P) :=
  div_nonneg (by linarith) (by linarith)

theorem threshold_lt_one (hTR : R < T) (hRP : P < R) : (T - R) / (T - P) < 1 := by
  rw [div_lt_one (by linarith)]; linarith

/-- (3) For `δ` close enough to `1` (all `δ ∈ [(T-R)/(T-P), 1)`, a nonempty interval), both
grim-trigger one-shot-deviation checks pass, whereas for every known finite `N` the only SPE
outcome is all-defect. -/
theorem coop_near_one (hTR : R < T) (hRP : P < R) (hPS : S < P) :
    ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧ ∀ δ : ℝ, δ₀ ≤ δ → δ < 1 →
      T + δ * P / (1 - δ) ≤ R / (1 - δ) ∧ S + δ * P / (1 - δ) < P / (1 - δ) :=
  ⟨(T - R) / (T - P), threshold_nonneg hTR hRP, threshold_lt_one hTR hRP,
    fun _ hδ h1 => ⟨(grim_threshold hTR hRP h1).2 hδ, punish_strict hPS h1⟩⟩

/-- Contrast, packaged: known finite horizon forces all-defect in every SPE, while a
geometric horizon with `δ` above the threshold supports grim-trigger cooperation checks. -/
theorem contrast (hTR : R < T) (hRP : P < R) (hPS : S < P) :
    (∀ (N : ℕ) (σ1 σ2 : Strategy), IsSPE T R P S N σ1 σ2 →
        outcome σ1 σ2 [] N = List.replicate N (D, D)) ∧
    (∀ δ : ℝ, (T - R) / (T - P) ≤ δ → δ < 1 →
        T + δ * P / (1 - δ) ≤ R / (1 - δ) ∧ S + δ * P / (1 - δ) < P / (1 - δ)) :=
  ⟨fun _ _ _ hS => spe_outcome hTR hPS hS,
    fun _ hδ h1 => ⟨(grim_threshold hTR hRP h1).2 hδ, punish_strict hPS h1⟩⟩

end KnownHorizonUnravelsB
