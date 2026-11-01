import Mathlib

/-!
# Coase theorem through Nash bargaining with transferable utility

Two parties choose an action `x : X` (with `X` finite where existence is needed) and a
transfer `t : ℝ` from party 2 to party 1. Party 1 receives `v₁ x + t`, party 2 receives
`v₂ x - t`; joint surplus is `S x = v₁ x + v₂ x`. Disagreement payoffs `d₁, d₂` encode the
initial assignment of rights. An outcome is feasible when both gains over disagreement are
strictly positive. A Nash solution is a feasible outcome maximizing the Nash product
`(v₁ x + t - d₁) * (v₂ x - t - d₂)` over all feasible outcomes.

PROVED
* `nashProduct_le`: for every `(x, t)`, the Nash product is at most `(S x - d₁ - d₂)^2 / 4`.
* `nashProduct_halfTransfer`, `gain₁_halfTransfer`, `gain₂_halfTransfer`: at the transfer
  `halfTransfer x = (v₂ x - v₁ x + d₁ - d₂) / 2` each party gains exactly
  `(S x - d₁ - d₂) / 2` and the Nash product equals `(S x - d₁ - d₂)^2 / 4`.
* `exists_feasible_iff`: action `x` admits a feasible transfer iff `S x > d₁ + d₂`.
* `efficiency` (target 1): if `(x*, t*)` is a Nash solution then `S y ≤ S x*` for all `y`
  with `S y > d₁ + d₂`.
* `equal_split` (target 2): at a Nash solution each party gains exactly
  `(S x* - d₁ - d₂) / 2`, and `t* = halfTransfer x*`.
* `isNash_iff` (target 2, characterization): `(x, t)` is a Nash solution iff
  `S x > d₁ + d₂`, `x` maximizes `S` over all actions with `S > d₁ + d₂`, and
  `t = halfTransfer x`. The condition on the action does not mention the transfer.
* `isNash_iff_global`: equivalently, `S x > d₁ + d₂`, `x` maximizes `S` over all of `X`,
  and `t = halfTransfer x`.
* `rights_invariance` (target 3): if `(x*, t*)` is a Nash solution under `(d₁, d₂)` and
  `S x* > d₁' + d₂'`, then for every action `y`, `y` is the action of some Nash solution under
  `(d₁, d₂)` iff it is under `(d₁', d₂')`; `x*` with `halfTransfer' x*` is a Nash solution
  under `(d₁', d₂')`; and the transfer moves by exactly `((d₁' - d₁) - (d₂' - d₂)) / 2`.
* `exists_isNash`: for finite nonempty `X`, a Nash solution exists iff some action has
  `S x > d₁ + d₂`.

INTERPRETED
* With zero transaction costs (frictionless bargaining modelled by the Nash solution with
  transferable utility), the parties reach the surplus-maximizing action whichever party holds
  the rights; the assignment of rights `(d₁, d₂)` only changes the transfer, i.e. who pays
  whom.
-/

namespace CoaseNashTUA

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
noncomputable def halfTransfer (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ) (x : X) : ℝ := (v₂ x - v₁ x + d₁ - d₂) / 2

variable (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ)

theorem gain_add (x : X) (t : ℝ) :
    gain₁ v₁ d₁ x t + gain₂ v₂ d₂ x t = S v₁ v₂ x - d₁ - d₂ := by
  unfold gain₁ gain₂ S; ring

theorem nashProduct_le (x : X) (t : ℝ) :
    nashProduct v₁ v₂ d₁ d₂ x t ≤ (S v₁ v₂ x - d₁ - d₂) ^ 2 / 4 := by
  rw [← gain_add v₁ v₂ d₁ d₂ x t]
  unfold nashProduct
  nlinarith [sq_nonneg (gain₁ v₁ d₁ x t - gain₂ v₂ d₂ x t)]

theorem gain₁_halfTransfer (x : X) :
    gain₁ v₁ d₁ x (halfTransfer v₁ v₂ d₁ d₂ x) = (S v₁ v₂ x - d₁ - d₂) / 2 := by
  unfold gain₁ halfTransfer S; ring

theorem gain₂_halfTransfer (x : X) :
    gain₂ v₂ d₂ x (halfTransfer v₁ v₂ d₁ d₂ x) = (S v₁ v₂ x - d₁ - d₂) / 2 := by
  unfold gain₂ halfTransfer S; ring

theorem nashProduct_halfTransfer (x : X) :
    nashProduct v₁ v₂ d₁ d₂ x (halfTransfer v₁ v₂ d₁ d₂ x) = (S v₁ v₂ x - d₁ - d₂) ^ 2 / 4 := by
  unfold nashProduct
  rw [gain₁_halfTransfer, gain₂_halfTransfer]; ring

theorem feasible_halfTransfer {x : X} (hx : d₁ + d₂ < S v₁ v₂ x) :
    Feasible v₁ v₂ d₁ d₂ x (halfTransfer v₁ v₂ d₁ d₂ x) := by
  unfold Feasible
  rw [gain₁_halfTransfer, gain₂_halfTransfer]
  constructor <;> linarith

theorem exists_feasible_iff (x : X) :
    (∃ t, Feasible v₁ v₂ d₁ d₂ x t) ↔ d₁ + d₂ < S v₁ v₂ x := by
  constructor
  · rintro ⟨t, h1, h2⟩
    have := gain_add v₁ v₂ d₁ d₂ x t
    linarith
  · intro hx
    exact ⟨_, feasible_halfTransfer v₁ v₂ d₁ d₂ hx⟩

theorem gainPos_of_isNash {x : X} {t : ℝ} (h : IsNash v₁ v₂ d₁ d₂ x t) :
    d₁ + d₂ < S v₁ v₂ x :=
  (exists_feasible_iff v₁ v₂ d₁ d₂ x).1 ⟨t, h.1⟩

/-- Target (1): efficiency. -/
theorem efficiency {x : X} {t : ℝ} (h : IsNash v₁ v₂ d₁ d₂ x t) :
    ∀ y, d₁ + d₂ < S v₁ v₂ y → S v₁ v₂ y ≤ S v₁ v₂ x := by
  intro y hy
  have hx := gainPos_of_isNash v₁ v₂ d₁ d₂ h
  have h1 := h.2 y _ (feasible_halfTransfer v₁ v₂ d₁ d₂ hy)
  rw [nashProduct_halfTransfer] at h1
  have h2 := nashProduct_le v₁ v₂ d₁ d₂ x t
  nlinarith

/-- Target (2): at a Nash solution each party gains exactly half of the total gain,
and the transfer is the equal-split transfer. -/
theorem equal_split {x : X} {t : ℝ} (h : IsNash v₁ v₂ d₁ d₂ x t) :
    gain₁ v₁ d₁ x t = (S v₁ v₂ x - d₁ - d₂) / 2 ∧
      gain₂ v₂ d₂ x t = (S v₁ v₂ x - d₁ - d₂) / 2 ∧
      t = halfTransfer v₁ v₂ d₁ d₂ x := by
  have hx := gainPos_of_isNash v₁ v₂ d₁ d₂ h
  have h1 := h.2 x _ (feasible_halfTransfer v₁ v₂ d₁ d₂ hx)
  rw [nashProduct_halfTransfer] at h1
  have hs := gain_add v₁ v₂ d₁ d₂ x t
  have hsq : (gain₁ v₁ d₁ x t - gain₂ v₂ d₂ x t) ^ 2 = 0 := by
    have : (gain₁ v₁ d₁ x t - gain₂ v₂ d₂ x t) ^ 2
        = (S v₁ v₂ x - d₁ - d₂) ^ 2 - 4 * nashProduct v₁ v₂ d₁ d₂ x t := by
      rw [← hs]; unfold nashProduct; ring
    rw [this]
    nlinarith [sq_nonneg (gain₁ v₁ d₁ x t - gain₂ v₂ d₂ x t)]
  have heq : gain₁ v₁ d₁ x t = gain₂ v₂ d₂ x t := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
    linarith
  refine ⟨by linarith, by linarith, ?_⟩
  have e1 : gain₁ v₁ d₁ x t = gain₁ v₁ d₁ x (halfTransfer v₁ v₂ d₁ d₂ x) := by
    rw [gain₁_halfTransfer]; linarith
  unfold gain₁ at e1
  linarith

/-- Characterization of Nash solutions: the condition on the action does not involve the
transfer; the transfer is then the equal-split transfer. -/
theorem isNash_iff (x : X) (t : ℝ) :
    IsNash v₁ v₂ d₁ d₂ x t ↔
      (d₁ + d₂ < S v₁ v₂ x ∧ ∀ y, d₁ + d₂ < S v₁ v₂ y → S v₁ v₂ y ≤ S v₁ v₂ x) ∧
        t = halfTransfer v₁ v₂ d₁ d₂ x := by
  constructor
  · intro h
    exact ⟨⟨gainPos_of_isNash v₁ v₂ d₁ d₂ h, efficiency v₁ v₂ d₁ d₂ h⟩,
      (equal_split v₁ v₂ d₁ d₂ h).2.2⟩
  · rintro ⟨⟨hx, hmax⟩, rfl⟩
    refine ⟨feasible_halfTransfer v₁ v₂ d₁ d₂ hx, ?_⟩
    intro y s hys
    have hy := (exists_feasible_iff v₁ v₂ d₁ d₂ y).1 ⟨s, hys⟩
    have h1 := nashProduct_le v₁ v₂ d₁ d₂ y s
    have h2 := hmax y hy
    rw [nashProduct_halfTransfer]
    have : (S v₁ v₂ y - d₁ - d₂) ^ 2 ≤ (S v₁ v₂ x - d₁ - d₂) ^ 2 := by
      apply pow_le_pow_left₀ <;> linarith
    linarith

theorem isNash_iff_global (x : X) (t : ℝ) :
    IsNash v₁ v₂ d₁ d₂ x t ↔
      (d₁ + d₂ < S v₁ v₂ x ∧ ∀ y, S v₁ v₂ y ≤ S v₁ v₂ x) ∧ t = halfTransfer v₁ v₂ d₁ d₂ x := by
  rw [isNash_iff]
  constructor
  · rintro ⟨⟨hx, hmax⟩, ht⟩
    refine ⟨⟨hx, fun y => ?_⟩, ht⟩
    by_cases hy : d₁ + d₂ < S v₁ v₂ y
    · exact hmax y hy
    · linarith
  · rintro ⟨⟨hx, hmax⟩, ht⟩
    exact ⟨⟨hx, fun y _ => hmax y⟩, ht⟩

/-- Target (3): changing the assignment of rights changes only the transfer. -/
theorem rights_invariance (d₁' d₂' : ℝ) {x : X} {t : ℝ} (h : IsNash v₁ v₂ d₁ d₂ x t)
    (h' : d₁' + d₂' < S v₁ v₂ x) :
    (∀ y, (∃ s, IsNash v₁ v₂ d₁ d₂ y s) ↔ (∃ s, IsNash v₁ v₂ d₁' d₂' y s)) ∧
      IsNash v₁ v₂ d₁' d₂' x (halfTransfer v₁ v₂ d₁' d₂' x) ∧
      halfTransfer v₁ v₂ d₁' d₂' x - t = ((d₁' - d₁) - (d₂' - d₂)) / 2 := by
  have hg := ((isNash_iff_global v₁ v₂ d₁ d₂ x t).1 h)
  obtain ⟨⟨hx, hmax⟩, ht⟩ := hg
  have key : ∀ y, (∃ s, IsNash v₁ v₂ d₁ d₂ y s) ↔ ∀ z, S v₁ v₂ z ≤ S v₁ v₂ y := by
    intro y
    constructor
    · rintro ⟨s, hs⟩
      exact ((isNash_iff_global v₁ v₂ d₁ d₂ y s).1 hs).1.2
    · intro hy
      refine ⟨halfTransfer v₁ v₂ d₁ d₂ y, (isNash_iff_global v₁ v₂ d₁ d₂ y _).2
        ⟨⟨?_, hy⟩, rfl⟩⟩
      have := hy x; linarith
  have key' : ∀ y, (∃ s, IsNash v₁ v₂ d₁' d₂' y s) ↔ ∀ z, S v₁ v₂ z ≤ S v₁ v₂ y := by
    intro y
    constructor
    · rintro ⟨s, hs⟩
      exact ((isNash_iff_global v₁ v₂ d₁' d₂' y s).1 hs).1.2
    · intro hy
      refine ⟨halfTransfer v₁ v₂ d₁' d₂' y, (isNash_iff_global v₁ v₂ d₁' d₂' y _).2
        ⟨⟨?_, hy⟩, rfl⟩⟩
      have := hy x; linarith
  refine ⟨fun y => (key y).trans (key' y).symm,
    (isNash_iff_global v₁ v₂ d₁' d₂' x _).2 ⟨⟨h', hmax⟩, rfl⟩, ?_⟩
  rw [ht]; unfold halfTransfer; ring

/-- Existence for a finite nonempty action set. -/
theorem exists_isNash [Finite X] [Nonempty X] :
    (∃ x t, IsNash v₁ v₂ d₁ d₂ x t) ↔ ∃ x, d₁ + d₂ < S v₁ v₂ x := by
  constructor
  · rintro ⟨x, t, h⟩
    exact ⟨x, gainPos_of_isNash v₁ v₂ d₁ d₂ h⟩
  · rintro ⟨x₀, hx₀⟩
    have := Fintype.ofFinite X
    obtain ⟨x, -, hx⟩ := Finset.exists_max_image Finset.univ (S v₁ v₂) Finset.univ_nonempty
    refine ⟨x, halfTransfer v₁ v₂ d₁ d₂ x, (isNash_iff_global v₁ v₂ d₁ d₂ x _).2
      ⟨⟨?_, fun y => hx y (Finset.mem_univ y)⟩, rfl⟩⟩
    have := hx x₀ (Finset.mem_univ x₀); linarith

end CoaseNashTUA
