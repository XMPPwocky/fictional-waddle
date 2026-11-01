import Mathlib

/-!
# Coase with action-dependent breakdown risk

Setting of `CoaseNashTUA` (reproduced here, self-contained): two parties choose an action
`x : X` and a transfer `t : ℝ` from party 2 to party 1; party `i`'s gain over disagreement is
`gain₁ v₁ d₁ x t = v₁ x + t - d₁` and `gain₂ v₂ d₂ x t = v₂ x - t - d₂`; joint surplus is
`S x = v₁ x + v₂ x`. Added: `eps : X → ℝ` with `0 < eps x ≤ 1` for all `x`. The weighted gains
are `G₁ x t = eps x * gain₁ x t`, `G₂ x t = eps x * gain₂ x t`. `IsNashEps x t` means
`0 < G₁ x t`, `0 < G₂ x t`, and `G₁ y s * G₂ y s ≤ G₁ x t * G₂ x t` for every `(y, s)` with
`0 < G₁ y s` and `0 < G₂ y s` (equivalently, by `G₁_pos_iff`/`G₂_pos_iff`, with both raw gains
positive). Throughout `D = d₁ + d₂`.

PROVED
* `G₁_pos_iff`, `G₂_pos_iff`: positivity of a weighted gain is positivity of the raw gain.
* (a) `isNashEps_iff`: `IsNashEps x t` iff `D < S x`, `eps y * (S y - D) ≤ eps x * (S x - D)`
  for every `y` with `D < S y`, and `t = halfTransfer v₁ v₂ d₁ d₂ x`.
  `transfer_indep_eps`: two Nash outcomes at the same action under two admissible risk
  functions `eps`, `eps'` have the same transfer.
* (b) `isNashEps_iff_max`, `exists_isNashEps_iff_max`: equivalently, `x` maximizes
  `D + eps y * (S y - D)` over `{y | D < S y}` (and `t = halfTransfer x`).
* (c) `nashEpsActions_eq`: the set `{x | ∃ t, IsNashEps x t}` equals `actionSet v₁ v₂ eps D`,
  a set defined from `D` alone; `nashEpsActions_eq_of_sum_eq`: equal `d₁ + d₂` give equal sets.
  `nashEpsActions_const`: if `eps` is constant the set equals `{x | ∃ t, IsNash v₁ v₂ d₁ d₂ x t}`.
* (d) `crossover`: if `eps y < eps x` and `S x < S y`, with
  `D* = (eps x * S x - eps y * S y) / (eps x - eps y)`: `D* < S x`;
  `eps x * (S x - D) - eps y * (S y - D) = (eps x - eps y) * (D* - D)` for all `D`;
  `D < D*` gives `eps y * (S y - D) < eps x * (S x - D)`; `D* < D` gives the reverse strict
  inequality; at `D = D*` the two are equal; and if `S x ≤ D < S y` then `x` admits no
  feasible transfer while `y` does.
* `two_action`: if moreover `X` consists of exactly the two actions `x ≠ y`, then the set of
  Nash actions is `{x}` iff `D < D*`, `{y}` iff `D* < D < S y`, `{x, y}` iff `D = D*`,
  and `∅` iff `S y ≤ D`.
* Instance `instance_main` (`Act = {x, y}`, `S x = 3`, `eps x = 9/10`, `S y = 5`,
  `eps y = 1/2`, arbitrary `v₁ v₂` with these surpluses): `D* = 1/2`, and the Nash action set
  is `{x}` iff `D < 1/2`, `{y}` iff `1/2 < D < 5`, `{x, y}` iff `D = 1/2`, `∅` iff `5 ≤ D`.

INTERPRETED
* `eps x` is the probability that bargaining over action `x` does not break down, so `G₁, G₂`
  are expected gains. The bargained action depends on the rights `(d₁, d₂)` only through their
  sum `D`, and no longer only through `S`: a larger total disagreement value `D` shifts the
  choice from the safe, lower-surplus action `x` to the risky, higher-surplus action `y`.
  The transfer is the equal-split transfer of the risk-free model; risk does not enter it.
* The bound `eps ≤ 1` is part of the setting; no proof here uses it.
-/

namespace Bridge3B

variable {X : Type*}

/-- Joint surplus. -/
def S (v₁ v₂ : X → ℝ) (x : X) : ℝ := v₁ x + v₂ x

/-- Party 1's gain over disagreement. -/
def gain₁ (v₁ : X → ℝ) (d₁ : ℝ) (x : X) (t : ℝ) : ℝ := v₁ x + t - d₁

/-- Party 2's gain over disagreement. -/
def gain₂ (v₂ : X → ℝ) (d₂ : ℝ) (x : X) (t : ℝ) : ℝ := v₂ x - t - d₂

/-- Both parties gain strictly. -/
def Feasible (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ) (x : X) (t : ℝ) : Prop :=
  0 < gain₁ v₁ d₁ x t ∧ 0 < gain₂ v₂ d₂ x t

/-- The Nash product. -/
def nashProduct (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ) (x : X) (t : ℝ) : ℝ :=
  gain₁ v₁ d₁ x t * gain₂ v₂ d₂ x t

/-- A feasible outcome maximizing the Nash product over all feasible outcomes. -/
def IsNash (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ) (x : X) (t : ℝ) : Prop :=
  Feasible v₁ v₂ d₁ d₂ x t ∧
    ∀ y s, Feasible v₁ v₂ d₁ d₂ y s → nashProduct v₁ v₂ d₁ d₂ y s ≤ nashProduct v₁ v₂ d₁ d₂ x t

/-- The transfer splitting the gain at action `x` equally. -/
noncomputable def halfTransfer (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ) (x : X) : ℝ :=
  (v₂ x - v₁ x + d₁ - d₂) / 2

/-- Party 1's risk-weighted gain. -/
def G₁ (v₁ eps : X → ℝ) (d₁ : ℝ) (x : X) (t : ℝ) : ℝ := eps x * gain₁ v₁ d₁ x t

/-- Party 2's risk-weighted gain. -/
def G₂ (v₂ eps : X → ℝ) (d₂ : ℝ) (x : X) (t : ℝ) : ℝ := eps x * gain₂ v₂ d₂ x t

/-- Nash solution of the risk-weighted bargaining problem. -/
def IsNashEps (v₁ v₂ eps : X → ℝ) (d₁ d₂ : ℝ) (x : X) (t : ℝ) : Prop :=
  0 < G₁ v₁ eps d₁ x t ∧ 0 < G₂ v₂ eps d₂ x t ∧
    ∀ y s, 0 < G₁ v₁ eps d₁ y s → 0 < G₂ v₂ eps d₂ y s →
      G₁ v₁ eps d₁ y s * G₂ v₂ eps d₂ y s ≤ G₁ v₁ eps d₁ x t * G₂ v₂ eps d₂ x t

/-- Actions of risk-weighted Nash solutions. -/
def nashEpsActions (v₁ v₂ eps : X → ℝ) (d₁ d₂ : ℝ) : Set X :=
  {x | ∃ t, IsNashEps v₁ v₂ eps d₁ d₂ x t}

/-- The action set determined by the total disagreement value `D` alone. -/
def actionSet (v₁ v₂ eps : X → ℝ) (D : ℝ) : Set X :=
  {x | D < S v₁ v₂ x ∧ ∀ y, D < S v₁ v₂ y → eps y * (S v₁ v₂ y - D) ≤ eps x * (S v₁ v₂ x - D)}

section General

variable (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ)

theorem gain_add (x : X) (t : ℝ) :
    gain₁ v₁ d₁ x t + gain₂ v₂ d₂ x t = S v₁ v₂ x - (d₁ + d₂) := by
  unfold gain₁ gain₂ S; ring

theorem nashProduct_le (x : X) (t : ℝ) :
    nashProduct v₁ v₂ d₁ d₂ x t ≤ (S v₁ v₂ x - (d₁ + d₂)) ^ 2 / 4 := by
  rw [← gain_add v₁ v₂ d₁ d₂ x t]
  unfold nashProduct
  nlinarith [sq_nonneg (gain₁ v₁ d₁ x t - gain₂ v₂ d₂ x t)]

theorem gain₁_halfTransfer (x : X) :
    gain₁ v₁ d₁ x (halfTransfer v₁ v₂ d₁ d₂ x) = (S v₁ v₂ x - (d₁ + d₂)) / 2 := by
  unfold gain₁ halfTransfer S; ring

theorem gain₂_halfTransfer (x : X) :
    gain₂ v₂ d₂ x (halfTransfer v₁ v₂ d₁ d₂ x) = (S v₁ v₂ x - (d₁ + d₂)) / 2 := by
  unfold gain₂ halfTransfer S; ring

theorem nashProduct_halfTransfer (x : X) :
    nashProduct v₁ v₂ d₁ d₂ x (halfTransfer v₁ v₂ d₁ d₂ x) = (S v₁ v₂ x - (d₁ + d₂)) ^ 2 / 4 := by
  unfold nashProduct
  rw [gain₁_halfTransfer, gain₂_halfTransfer]; ring

theorem feasible_halfTransfer {x : X} (hx : d₁ + d₂ < S v₁ v₂ x) :
    Feasible v₁ v₂ d₁ d₂ x (halfTransfer v₁ v₂ d₁ d₂ x) := by
  unfold Feasible
  rw [gain₁_halfTransfer, gain₂_halfTransfer]
  constructor <;> linarith

theorem lt_of_feasible {x : X} {t : ℝ} (h : Feasible v₁ v₂ d₁ d₂ x t) :
    d₁ + d₂ < S v₁ v₂ x := by
  have := gain_add v₁ v₂ d₁ d₂ x t
  linarith [h.1, h.2]

theorem exists_feasible_iff (x : X) :
    (∃ t, Feasible v₁ v₂ d₁ d₂ x t) ↔ d₁ + d₂ < S v₁ v₂ x :=
  ⟨fun ⟨_, h⟩ => lt_of_feasible v₁ v₂ d₁ d₂ h, fun hx => ⟨_, feasible_halfTransfer v₁ v₂ d₁ d₂ hx⟩⟩

/-- A transfer attaining the maximal Nash product at `x` is the equal-split transfer. -/
theorem eq_halfTransfer_of_le {x : X} {t : ℝ}
    (h : (S v₁ v₂ x - (d₁ + d₂)) ^ 2 / 4 ≤ nashProduct v₁ v₂ d₁ d₂ x t) :
    t = halfTransfer v₁ v₂ d₁ d₂ x := by
  have hs := gain_add v₁ v₂ d₁ d₂ x t
  rw [← hs] at h
  unfold nashProduct at h
  have hsq : (gain₁ v₁ d₁ x t - gain₂ v₂ d₂ x t) ^ 2 = 0 := by
    apply le_antisymm _ (sq_nonneg _)
    nlinarith
  have heq : gain₁ v₁ d₁ x t = gain₂ v₂ d₂ x t := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
    linarith
  unfold gain₁ gain₂ at heq
  unfold halfTransfer
  linarith

theorem isNash_iff (x : X) (t : ℝ) :
    IsNash v₁ v₂ d₁ d₂ x t ↔
      (d₁ + d₂ < S v₁ v₂ x ∧ ∀ y, d₁ + d₂ < S v₁ v₂ y → S v₁ v₂ y ≤ S v₁ v₂ x) ∧
        t = halfTransfer v₁ v₂ d₁ d₂ x := by
  constructor
  · intro h
    have hx := lt_of_feasible v₁ v₂ d₁ d₂ h.1
    have ht : t = halfTransfer v₁ v₂ d₁ d₂ x := by
      apply eq_halfTransfer_of_le
      have := h.2 x _ (feasible_halfTransfer v₁ v₂ d₁ d₂ hx)
      rwa [nashProduct_halfTransfer] at this
    refine ⟨⟨hx, fun y hy => ?_⟩, ht⟩
    have h1 := h.2 y _ (feasible_halfTransfer v₁ v₂ d₁ d₂ hy)
    rw [nashProduct_halfTransfer] at h1
    have h2 := nashProduct_le v₁ v₂ d₁ d₂ x t
    nlinarith
  · rintro ⟨⟨hx, hmax⟩, rfl⟩
    refine ⟨feasible_halfTransfer v₁ v₂ d₁ d₂ hx, ?_⟩
    intro y s hys
    have hy := lt_of_feasible v₁ v₂ d₁ d₂ hys
    have h1 := nashProduct_le v₁ v₂ d₁ d₂ y s
    have h2 := hmax y hy
    rw [nashProduct_halfTransfer]
    have : (S v₁ v₂ y - (d₁ + d₂)) ^ 2 ≤ (S v₁ v₂ x - (d₁ + d₂)) ^ 2 := by
      apply pow_le_pow_left₀ <;> linarith
    linarith

variable {eps : X → ℝ} (heps : ∀ x, 0 < eps x ∧ eps x ≤ 1)
include heps

theorem G₁_pos_iff (x : X) (t : ℝ) : 0 < G₁ v₁ eps d₁ x t ↔ 0 < gain₁ v₁ d₁ x t := by
  unfold G₁; exact mul_pos_iff_of_pos_left (heps x).1

theorem G₂_pos_iff (x : X) (t : ℝ) : 0 < G₂ v₂ eps d₂ x t ↔ 0 < gain₂ v₂ d₂ x t := by
  unfold G₂; exact mul_pos_iff_of_pos_left (heps x).1

omit heps in
theorem G_mul (x : X) (t : ℝ) :
    G₁ v₁ eps d₁ x t * G₂ v₂ eps d₂ x t = eps x ^ 2 * nashProduct v₁ v₂ d₁ d₂ x t := by
  unfold G₁ G₂ nashProduct; ring

/-- (a) Characterization of risk-weighted Nash solutions. -/
theorem isNashEps_iff (x : X) (t : ℝ) :
    IsNashEps v₁ v₂ eps d₁ d₂ x t ↔
      (d₁ + d₂ < S v₁ v₂ x ∧
        ∀ y, d₁ + d₂ < S v₁ v₂ y →
          eps y * (S v₁ v₂ y - (d₁ + d₂)) ≤ eps x * (S v₁ v₂ x - (d₁ + d₂))) ∧
        t = halfTransfer v₁ v₂ d₁ d₂ x := by
  have feas_iff : ∀ y s, (0 < G₁ v₁ eps d₁ y s ∧ 0 < G₂ v₂ eps d₂ y s) ↔
      Feasible v₁ v₂ d₁ d₂ y s := fun y s => by
    rw [G₁_pos_iff v₁ d₁ heps, G₂_pos_iff v₂ d₂ heps]; rfl
  have hex := (heps x).1
  constructor
  · rintro ⟨h1, h2, hmax⟩
    have hfx : Feasible v₁ v₂ d₁ d₂ x t := (feas_iff x t).1 ⟨h1, h2⟩
    have hx := lt_of_feasible v₁ v₂ d₁ d₂ hfx
    have hub := nashProduct_le v₁ v₂ d₁ d₂ x t
    have ht : t = halfTransfer v₁ v₂ d₁ d₂ x := by
      apply eq_halfTransfer_of_le
      obtain ⟨a, b⟩ := (feas_iff x _).2 (feasible_halfTransfer v₁ v₂ d₁ d₂ hx)
      have := hmax x _ a b
      rw [G_mul, G_mul, nashProduct_halfTransfer] at this
      have hpos : 0 < eps x ^ 2 := by positivity
      nlinarith
    refine ⟨⟨hx, fun y hy => ?_⟩, ht⟩
    have hey := (heps y).1
    obtain ⟨a, b⟩ := (feas_iff y _).2 (feasible_halfTransfer v₁ v₂ d₁ d₂ hy)
    have h3 := hmax y _ a b
    rw [G_mul, G_mul, nashProduct_halfTransfer] at h3
    have hsq : (eps y * (S v₁ v₂ y - (d₁ + d₂))) ^ 2 ≤ (eps x * (S v₁ v₂ x - (d₁ + d₂))) ^ 2 := by
      have : eps x ^ 2 * nashProduct v₁ v₂ d₁ d₂ x t ≤
          eps x ^ 2 * ((S v₁ v₂ x - (d₁ + d₂)) ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left hub (by positivity)
      nlinarith
    have hxpos : 0 ≤ eps x * (S v₁ v₂ x - (d₁ + d₂)) := by
      apply mul_nonneg hex.le; linarith
    exact (pow_le_pow_iff_left₀ (mul_nonneg hey.le (by linarith)) hxpos (by norm_num)).1 hsq
  · rintro ⟨⟨hx, hmax⟩, rfl⟩
    obtain ⟨a, b⟩ := (feas_iff x _).2 (feasible_halfTransfer v₁ v₂ d₁ d₂ hx)
    refine ⟨a, b, fun y s h1 h2 => ?_⟩
    have hfy := (feas_iff y s).1 ⟨h1, h2⟩
    have hy := lt_of_feasible v₁ v₂ d₁ d₂ hfy
    have hey := (heps y).1
    rw [G_mul, G_mul, nashProduct_halfTransfer]
    have h3 : eps y ^ 2 * nashProduct v₁ v₂ d₁ d₂ y s ≤
        eps y ^ 2 * ((S v₁ v₂ y - (d₁ + d₂)) ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left (nashProduct_le v₁ v₂ d₁ d₂ y s) (by positivity)
    have h4 : (eps y * (S v₁ v₂ y - (d₁ + d₂))) ^ 2 ≤ (eps x * (S v₁ v₂ x - (d₁ + d₂))) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hey.le (by linarith)) (hmax y hy) 2
    nlinarith

/-- (a) The transfer does not depend on the risk function. -/
theorem transfer_indep_eps {eps' : X → ℝ} (heps' : ∀ x, 0 < eps' x ∧ eps' x ≤ 1)
    {x : X} {t t' : ℝ} (h : IsNashEps v₁ v₂ eps d₁ d₂ x t)
    (h' : IsNashEps v₁ v₂ eps' d₁ d₂ x t') : t = t' := by
  rw [((isNashEps_iff v₁ v₂ d₁ d₂ heps x t).1 h).2,
    ((isNashEps_iff v₁ v₂ d₁ d₂ heps' x t').1 h').2]

/-- (b) The Nash action maximizes `D + eps y * (S y - D)` over `{y | D < S y}`. -/
theorem isNashEps_iff_max (x : X) (t : ℝ) :
    IsNashEps v₁ v₂ eps d₁ d₂ x t ↔
      (d₁ + d₂ < S v₁ v₂ x ∧
        ∀ y, d₁ + d₂ < S v₁ v₂ y →
          (d₁ + d₂) + eps y * (S v₁ v₂ y - (d₁ + d₂)) ≤
            (d₁ + d₂) + eps x * (S v₁ v₂ x - (d₁ + d₂))) ∧
        t = halfTransfer v₁ v₂ d₁ d₂ x := by
  rw [isNashEps_iff v₁ v₂ d₁ d₂ heps]
  simp only [add_le_add_iff_left]

/-- (b) The same, for the action alone. -/
theorem exists_isNashEps_iff_max (x : X) :
    (∃ t, IsNashEps v₁ v₂ eps d₁ d₂ x t) ↔
      d₁ + d₂ < S v₁ v₂ x ∧
        ∀ y, d₁ + d₂ < S v₁ v₂ y →
          (d₁ + d₂) + eps y * (S v₁ v₂ y - (d₁ + d₂)) ≤
            (d₁ + d₂) + eps x * (S v₁ v₂ x - (d₁ + d₂)) := by
  simp only [isNashEps_iff_max v₁ v₂ d₁ d₂ heps]
  exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

/-- (c) The set of Nash actions is a function of `D = d₁ + d₂`. -/
theorem nashEpsActions_eq :
    nashEpsActions v₁ v₂ eps d₁ d₂ = actionSet v₁ v₂ eps (d₁ + d₂) := by
  ext x
  simp only [nashEpsActions, actionSet, Set.mem_ofPred_eq, isNashEps_iff v₁ v₂ d₁ d₂ heps]
  exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

/-- (c) Equal totals `d₁ + d₂` give equal sets of Nash actions. -/
theorem nashEpsActions_eq_of_sum_eq {d₁' d₂' : ℝ} (hD : d₁ + d₂ = d₁' + d₂') :
    nashEpsActions v₁ v₂ eps d₁ d₂ = nashEpsActions v₁ v₂ eps d₁' d₂' := by
  rw [nashEpsActions_eq v₁ v₂ d₁ d₂ heps, nashEpsActions_eq v₁ v₂ d₁' d₂' heps, hD]

/-- (c) With constant `eps`, the Nash actions are those of the risk-free problem. -/
theorem nashEpsActions_const (hc : ∀ x y, eps x = eps y) :
    nashEpsActions v₁ v₂ eps d₁ d₂ = {x | ∃ t, IsNash v₁ v₂ d₁ d₂ x t} := by
  rw [nashEpsActions_eq v₁ v₂ d₁ d₂ heps]
  ext x
  simp only [actionSet, Set.mem_ofPred_eq, isNash_iff]
  have hex := (heps x).1
  have key : ∀ y, eps y * (S v₁ v₂ y - (d₁ + d₂)) ≤ eps x * (S v₁ v₂ x - (d₁ + d₂)) ↔
      S v₁ v₂ y ≤ S v₁ v₂ x := by
    intro y
    rw [hc y x, mul_le_mul_iff_right₀ hex, sub_le_sub_iff_right]
  simp only [key]
  exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩

end General

section Crossover

variable (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ) {eps : X → ℝ}

/-- The critical total disagreement value. -/
noncomputable def Dstar (v₁ v₂ eps : X → ℝ) (x y : X) : ℝ :=
  (eps x * S v₁ v₂ x - eps y * S v₁ v₂ y) / (eps x - eps y)

theorem crossover_identity {x y : X} (hxy : eps y < eps x) (D : ℝ) :
    eps x * (S v₁ v₂ x - D) - eps y * (S v₁ v₂ y - D) =
      (eps x - eps y) * (Dstar v₁ v₂ eps x y - D) := by
  have hne : eps x - eps y ≠ 0 := by linarith
  unfold Dstar
  field_simp
  ring

/-- (d) Crossover in the total disagreement value. -/
theorem crossover (heps : ∀ x, 0 < eps x ∧ eps x ≤ 1) {x y : X} (hxy : eps y < eps x)
    (hS : S v₁ v₂ x < S v₁ v₂ y) :
    Dstar v₁ v₂ eps x y < S v₁ v₂ x ∧
      (∀ D, D < Dstar v₁ v₂ eps x y → eps y * (S v₁ v₂ y - D) < eps x * (S v₁ v₂ x - D)) ∧
      (∀ D, Dstar v₁ v₂ eps x y < D → eps x * (S v₁ v₂ x - D) < eps y * (S v₁ v₂ y - D)) ∧
      eps x * (S v₁ v₂ x - Dstar v₁ v₂ eps x y) = eps y * (S v₁ v₂ y - Dstar v₁ v₂ eps x y) ∧
      (S v₁ v₂ x ≤ d₁ + d₂ → d₁ + d₂ < S v₁ v₂ y →
        (¬ ∃ t, Feasible v₁ v₂ d₁ d₂ x t) ∧ ∃ t, Feasible v₁ v₂ d₁ d₂ y t) := by
  have hpos : 0 < eps x - eps y := by linarith
  have hey := (heps y).1
  refine ⟨?_, fun D hD => ?_, fun D hD => ?_, ?_, fun h1 h2 => ?_⟩
  · unfold Dstar
    rw [div_lt_iff₀ hpos]
    nlinarith
  · have := crossover_identity v₁ v₂ hxy D
    nlinarith
  · have := crossover_identity v₁ v₂ hxy D
    nlinarith
  · have := crossover_identity v₁ v₂ hxy (Dstar v₁ v₂ eps x y)
    linarith [show (eps x - eps y) * (Dstar v₁ v₂ eps x y - Dstar v₁ v₂ eps x y) = 0 by ring]
  · rw [exists_feasible_iff, exists_feasible_iff]
    exact ⟨not_lt.2 h1, h2⟩

theorem set_eq_singleton_iff {x y : X} (hne : x ≠ y) (hX : ∀ z, z = x ∨ z = y) (s : Set X) :
    s = {x} ↔ x ∈ s ∧ y ∉ s := by
  constructor
  · rintro rfl; simp [hne.symm]
  · rintro ⟨hx, hy⟩
    ext z
    rcases hX z with rfl | rfl <;> simp [hx, hy, hne.symm]

theorem set_eq_pair_iff {x y : X} (hX : ∀ z, z = x ∨ z = y) (s : Set X) :
    s = {x, y} ↔ x ∈ s ∧ y ∈ s := by
  constructor
  · rintro rfl; simp
  · rintro ⟨hx, hy⟩
    ext z
    rcases hX z with rfl | rfl <;> simp [hx, hy]

theorem set_eq_empty_iff {x y : X} (hX : ∀ z, z = x ∨ z = y) (s : Set X) :
    s = ∅ ↔ x ∉ s ∧ y ∉ s := by
  constructor
  · rintro rfl; simp
  · rintro ⟨hx, hy⟩
    ext z
    rcases hX z with rfl | rfl <;> simp [hx, hy]

/-- (d) Two-action case: the Nash action as a function of `D`. -/
theorem two_action (heps : ∀ x, 0 < eps x ∧ eps x ≤ 1) {x y : X} (hne : x ≠ y)
    (hX : ∀ z, z = x ∨ z = y) (hxy : eps y < eps x) (hS : S v₁ v₂ x < S v₁ v₂ y) :
    (nashEpsActions v₁ v₂ eps d₁ d₂ = {x} ↔ d₁ + d₂ < Dstar v₁ v₂ eps x y) ∧
      (nashEpsActions v₁ v₂ eps d₁ d₂ = {y} ↔
        Dstar v₁ v₂ eps x y < d₁ + d₂ ∧ d₁ + d₂ < S v₁ v₂ y) ∧
      (nashEpsActions v₁ v₂ eps d₁ d₂ = {x, y} ↔ d₁ + d₂ = Dstar v₁ v₂ eps x y) ∧
      (nashEpsActions v₁ v₂ eps d₁ d₂ = ∅ ↔ S v₁ v₂ y ≤ d₁ + d₂) := by
  have hpos : 0 < eps x - eps y := by linarith
  have hlt := (crossover v₁ v₂ d₁ d₂ heps hxy hS).1
  have hid := crossover_identity v₁ v₂ hxy (d₁ + d₂)
  have hforall : ∀ (P : X → Prop), (∀ z, P z) ↔ P x ∧ P y := fun P =>
    ⟨fun h => ⟨h x, h y⟩, fun ⟨hx, hy⟩ z => by rcases hX z with rfl | rfl <;> assumption⟩
  have memx : x ∈ nashEpsActions v₁ v₂ eps d₁ d₂ ↔ d₁ + d₂ ≤ Dstar v₁ v₂ eps x y := by
    rw [nashEpsActions_eq v₁ v₂ d₁ d₂ heps]
    simp only [actionSet, Set.mem_ofPred_eq]
    rw [hforall]
    constructor
    · rintro ⟨h1, -, h2⟩
      have := h2 (by linarith)
      by_contra hc
      push Not at hc
      nlinarith
    · intro h
      refine ⟨by linarith, fun _ => le_refl _, fun _ => ?_⟩
      nlinarith
  have memy : y ∈ nashEpsActions v₁ v₂ eps d₁ d₂ ↔
      Dstar v₁ v₂ eps x y ≤ d₁ + d₂ ∧ d₁ + d₂ < S v₁ v₂ y := by
    rw [nashEpsActions_eq v₁ v₂ d₁ d₂ heps]
    simp only [actionSet, Set.mem_ofPred_eq]
    rw [hforall]
    constructor
    · rintro ⟨h1, h2, -⟩
      refine ⟨?_, h1⟩
      by_cases hx : d₁ + d₂ < S v₁ v₂ x
      · have := h2 hx
        by_contra hc
        push Not at hc
        nlinarith
      · push Not at hx; linarith
    · rintro ⟨h1, h2⟩
      refine ⟨h2, fun _ => ?_, fun _ => le_refl _⟩
      nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [set_eq_singleton_iff hne hX, memx, memy]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h1.lt_or_eq with h | h
      · exact h
      · exact absurd ⟨h.ge, by linarith⟩ h2
    · intro h; exact ⟨h.le, fun ⟨h', _⟩ => absurd h' (not_le.2 h)⟩
  · rw [set_eq_singleton_iff hne.symm (fun z => (hX z).symm), memx, memy]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨lt_of_le_of_ne h1 (fun h => h3 h.ge), h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1.le, h2⟩, not_le.2 h1⟩
  · rw [set_eq_pair_iff hX, memx, memy]
    constructor
    · rintro ⟨h1, h2, -⟩; exact le_antisymm h1 h2
    · intro h; exact ⟨h.le, h.ge, by linarith⟩
  · rw [set_eq_empty_iff hX, memx, memy]
    constructor
    · rintro ⟨h1, h2⟩
      push Not at h1
      by_contra hc; push Not at hc
      exact h2 ⟨h1.le, hc⟩
    · intro h
      refine ⟨by push Not; linarith, fun ⟨_, h'⟩ => by linarith⟩

end Crossover

section Instance

/-- Two actions: `x` safe with lower surplus, `y` risky with higher surplus. -/
inductive Act
  | x
  | y
  deriving DecidableEq

/-- Agreement probabilities `eps x = 9/10`, `eps y = 1/2`. -/
noncomputable def epsI : Act → ℝ
  | .x => 9 / 10
  | .y => 1 / 2

theorem epsI_bounds : ∀ a, 0 < epsI a ∧ epsI a ≤ 1 := by
  intro a; cases a <;> norm_num [epsI]

/-- Instance: `S x = 3`, `eps x = 9/10`, `S y = 5`, `eps y = 1/2`. Here `D* = 1/2`. -/
theorem instance_main (v₁ v₂ : Act → ℝ) (d₁ d₂ : ℝ)
    (hx : S v₁ v₂ Act.x = 3) (hy : S v₁ v₂ Act.y = 5) :
    Dstar v₁ v₂ epsI Act.x Act.y = 1 / 2 ∧
      (nashEpsActions v₁ v₂ epsI d₁ d₂ = {Act.x} ↔ d₁ + d₂ < 1 / 2) ∧
      (nashEpsActions v₁ v₂ epsI d₁ d₂ = {Act.y} ↔ 1 / 2 < d₁ + d₂ ∧ d₁ + d₂ < 5) ∧
      (nashEpsActions v₁ v₂ epsI d₁ d₂ = {Act.x, Act.y} ↔ d₁ + d₂ = 1 / 2) ∧
      (nashEpsActions v₁ v₂ epsI d₁ d₂ = ∅ ↔ 5 ≤ d₁ + d₂) := by
  have hD : Dstar v₁ v₂ epsI Act.x Act.y = 1 / 2 := by
    unfold Dstar; rw [hx, hy]; norm_num [epsI]
  have hX : ∀ z : Act, z = Act.x ∨ z = Act.y := fun z => by cases z <;> simp
  have h := two_action v₁ v₂ d₁ d₂ epsI_bounds (x := Act.x) (y := Act.y) (by decide) hX
    (by norm_num [epsI]) (by rw [hx, hy]; norm_num)
  rw [hD, hy] at h
  exact ⟨hD, h⟩

end Instance

end Bridge3B
