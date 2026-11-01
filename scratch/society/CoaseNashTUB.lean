import Mathlib

/-!
# Coase theorem via Nash bargaining with transferable utility

Two parties choose an action `x : X` and a transfer `t : ℝ` from party 2 to party 1.
Party 1 receives `v₁ x + t`, party 2 receives `v₂ x - t`; the joint surplus is
`S x = v₁ x + v₂ x`. Disagreement payoffs `d₁, d₂` encode the initial assignment of rights.
Admissible outcomes are those giving both parties strictly positive gains over disagreement.
The Nash product is `(v₁ x + t - d₁) * (v₂ x - t - d₂)`, maximised over admissible outcomes.

PROVED (the action set `X` is an arbitrary type; finiteness is used only for existence):
* `nash_le` : on every outcome, Nash product `≤ (S x - d₁ - d₂)^2 / 4`.
* `efficiency` (target 1): if `(x*, t*)` maximises the Nash product over admissible outcomes,
  then `S y ≤ S x*` for every `y` with `S y > d₁ + d₂`.
* `equal_split` (target 2): at a maximiser, both gains equal `(S x* - d₁ - d₂) / 2`.
* `transfer_eq` : at a maximiser, `t* = ((v₂ x* - d₂) - (v₁ x* - d₁)) / 2`.
* `isNashMax_iff` : `(x, t)` is a maximiser iff `S x > d₁ + d₂`, `x` maximises `S` among
  actions with `S y > d₁ + d₂`, and `t` is the half-split transfer.
* `action_indep_split` (target 2, action part): the set of maximising actions depends on
  `(v₁, v₂, d₁, d₂)` only through `v₁ + v₂` and `d₁ + d₂`; in particular it does not depend
  on how the gain is divided between the parties.
* `isNashMax_iff_of_global` : when `max S > d₁ + d₂`, maximising actions are exactly the
  global maximisers of `S`.
* `rights_same_actions` (target 3): if `(x*, t*)` is a maximiser under rights `(d₁, d₂)` and
  `S x* > d₁' + d₂'`, then the maximising actions under `(d₁', d₂')` are exactly those under
  `(d₁, d₂)`.
* `rights_move_transfer` (target 3, transfer part): under the same hypotheses
  `(x*, t* + ((d₁' - d₁) - (d₂' - d₂)) / 2)` is a maximiser under `(d₁', d₂')`, and every
  maximiser `(y, s)` under `(d₁', d₂')` has `S y = S x*`.
* `exists_isNashMax` : for finite `X`, a maximiser exists iff some action has `S y > d₁ + d₂`.

INTERPRETED (docstring only): with zero transaction costs, bargaining reaches the efficient
action whoever holds the rights; the assignment of rights only changes the transfer.
-/

namespace CoaseNashTUB

variable {X : Type*}

/-- Joint surplus. -/
def S (v₁ v₂ : X → ℝ) (x : X) : ℝ := v₁ x + v₂ x

/-- Gain of party 1 over disagreement. -/
def gain₁ (v₁ : X → ℝ) (d₁ : ℝ) (x : X) (t : ℝ) : ℝ := v₁ x + t - d₁

/-- Gain of party 2 over disagreement. -/
def gain₂ (v₂ : X → ℝ) (d₂ : ℝ) (x : X) (t : ℝ) : ℝ := v₂ x - t - d₂

/-- Admissible outcomes: both gains strictly positive. -/
def Admissible (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ) (x : X) (t : ℝ) : Prop :=
  0 < gain₁ v₁ d₁ x t ∧ 0 < gain₂ v₂ d₂ x t

/-- Nash product. -/
def nash (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ) (x : X) (t : ℝ) : ℝ :=
  gain₁ v₁ d₁ x t * gain₂ v₂ d₂ x t

/-- `(x, t)` maximises the Nash product over admissible outcomes. -/
def IsNashMax (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ) (x : X) (t : ℝ) : Prop :=
  Admissible v₁ v₂ d₁ d₂ x t ∧
    ∀ y s, Admissible v₁ v₂ d₁ d₂ y s → nash v₁ v₂ d₁ d₂ y s ≤ nash v₁ v₂ d₁ d₂ x t

/-- Transfer splitting the gain equally. -/
noncomputable def halfTransfer (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ) (x : X) : ℝ :=
  ((v₂ x - d₂) - (v₁ x - d₁)) / 2

variable (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ)

theorem gain_sum (x : X) (t : ℝ) :
    gain₁ v₁ d₁ x t + gain₂ v₂ d₂ x t = S v₁ v₂ x - d₁ - d₂ := by
  unfold gain₁ gain₂ S; ring

theorem nash_le (x : X) (t : ℝ) :
    nash v₁ v₂ d₁ d₂ x t ≤ (S v₁ v₂ x - d₁ - d₂) ^ 2 / 4 := by
  rw [← gain_sum v₁ v₂ d₁ d₂ x t]
  unfold nash
  nlinarith [sq_nonneg (gain₁ v₁ d₁ x t - gain₂ v₂ d₂ x t)]

theorem gain₁_half (x : X) :
    gain₁ v₁ d₁ x (halfTransfer v₁ v₂ d₁ d₂ x) = (S v₁ v₂ x - d₁ - d₂) / 2 := by
  unfold gain₁ halfTransfer S; ring

theorem gain₂_half (x : X) :
    gain₂ v₂ d₂ x (halfTransfer v₁ v₂ d₁ d₂ x) = (S v₁ v₂ x - d₁ - d₂) / 2 := by
  unfold gain₂ halfTransfer S; ring

theorem nash_half (x : X) :
    nash v₁ v₂ d₁ d₂ x (halfTransfer v₁ v₂ d₁ d₂ x) = (S v₁ v₂ x - d₁ - d₂) ^ 2 / 4 := by
  unfold nash; rw [gain₁_half, gain₂_half]; ring

theorem admissible_half {x : X} (hx : d₁ + d₂ < S v₁ v₂ x) :
    Admissible v₁ v₂ d₁ d₂ x (halfTransfer v₁ v₂ d₁ d₂ x) := by
  unfold Admissible; rw [gain₁_half, gain₂_half]; constructor <;> linarith

theorem admissible_pos {x : X} {t : ℝ} (h : Admissible v₁ v₂ d₁ d₂ x t) :
    d₁ + d₂ < S v₁ v₂ x := by
  have := gain_sum v₁ v₂ d₁ d₂ x t
  linarith [h.1, h.2]

/-- Target (1): efficiency. -/
theorem efficiency {x : X} {t : ℝ} (h : IsNashMax v₁ v₂ d₁ d₂ x t) :
    ∀ y, d₁ + d₂ < S v₁ v₂ y → S v₁ v₂ y ≤ S v₁ v₂ x := by
  intro y hy
  have hx := admissible_pos v₁ v₂ d₁ d₂ h.1
  have h1 := h.2 y _ (admissible_half v₁ v₂ d₁ d₂ hy)
  rw [nash_half] at h1
  have h2 := nash_le v₁ v₂ d₁ d₂ x t
  by_contra hc
  have hc' : S v₁ v₂ x < S v₁ v₂ y := lt_of_not_ge hc
  nlinarith

/-- Target (2): equal split of the gain at a maximiser. -/
theorem equal_split {x : X} {t : ℝ} (h : IsNashMax v₁ v₂ d₁ d₂ x t) :
    gain₁ v₁ d₁ x t = (S v₁ v₂ x - d₁ - d₂) / 2 ∧
      gain₂ v₂ d₂ x t = (S v₁ v₂ x - d₁ - d₂) / 2 := by
  have hx := admissible_pos v₁ v₂ d₁ d₂ h.1
  have h1 := h.2 x _ (admissible_half v₁ v₂ d₁ d₂ hx)
  rw [nash_half, ← gain_sum v₁ v₂ d₁ d₂ x t] at h1
  unfold nash at h1
  have hsq : (gain₁ v₁ d₁ x t - gain₂ v₂ d₂ x t) ^ 2 = 0 := by
    nlinarith [sq_nonneg (gain₁ v₁ d₁ x t - gain₂ v₂ d₂ x t)]
  have heq : gain₁ v₁ d₁ x t = gain₂ v₂ d₂ x t := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    linarith
  have hs := gain_sum v₁ v₂ d₁ d₂ x t
  constructor <;> linarith

theorem transfer_eq {x : X} {t : ℝ} (h : IsNashMax v₁ v₂ d₁ d₂ x t) :
    t = halfTransfer v₁ v₂ d₁ d₂ x := by
  have h1 := (equal_split v₁ v₂ d₁ d₂ h).1
  have h2 := gain₁_half v₁ v₂ d₁ d₂ x
  unfold gain₁ at h1 h2
  linarith

/-- Full characterisation of Nash bargaining maximisers. -/
theorem isNashMax_iff (x : X) (t : ℝ) :
    IsNashMax v₁ v₂ d₁ d₂ x t ↔
      d₁ + d₂ < S v₁ v₂ x ∧ (∀ y, d₁ + d₂ < S v₁ v₂ y → S v₁ v₂ y ≤ S v₁ v₂ x) ∧
        t = halfTransfer v₁ v₂ d₁ d₂ x := by
  constructor
  · intro h
    exact ⟨admissible_pos v₁ v₂ d₁ d₂ h.1, efficiency v₁ v₂ d₁ d₂ h,
      transfer_eq v₁ v₂ d₁ d₂ h⟩
  · rintro ⟨hx, hmax, rfl⟩
    refine ⟨admissible_half v₁ v₂ d₁ d₂ hx, fun y s hys => ?_⟩
    have hy := admissible_pos v₁ v₂ d₁ d₂ hys
    have hle := hmax y hy
    rw [nash_half]
    have h1 := nash_le v₁ v₂ d₁ d₂ y s
    have h2 : (S v₁ v₂ y - d₁ - d₂) ^ 2 ≤ (S v₁ v₂ x - d₁ - d₂) ^ 2 := by
      apply pow_le_pow_left₀ <;> linarith
    linarith

/-- Target (2), action part: maximising actions depend only on `v₁ + v₂` and `d₁ + d₂`. -/
theorem action_indep_split (v₁' v₂' : X → ℝ) (d₁' d₂' : ℝ)
    (hS : ∀ x, v₁' x + v₂' x = v₁ x + v₂ x) (hd : d₁' + d₂' = d₁ + d₂) (x : X) :
    (∃ t, IsNashMax v₁ v₂ d₁ d₂ x t) ↔ (∃ t, IsNashMax v₁' v₂' d₁' d₂' x t) := by
  have hS' : ∀ y, S v₁' v₂' y = S v₁ v₂ y := fun y => hS y
  simp only [isNashMax_iff, hS', hd]
  constructor <;> rintro ⟨t, h1, h2, -⟩ <;> exact ⟨_, h1, h2, rfl⟩

/-- When the efficient surplus exceeds `d₁ + d₂`, maximisers are global maximisers of `S`
with the half-split transfer. -/
theorem isNashMax_iff_of_global {x₀ : X} (hx₀ : d₁ + d₂ < S v₁ v₂ x₀)
    (hmax₀ : ∀ y, S v₁ v₂ y ≤ S v₁ v₂ x₀) (x : X) (t : ℝ) :
    IsNashMax v₁ v₂ d₁ d₂ x t ↔
      (∀ y, S v₁ v₂ y ≤ S v₁ v₂ x) ∧ t = halfTransfer v₁ v₂ d₁ d₂ x := by
  rw [isNashMax_iff]
  constructor
  · rintro ⟨hx, hm, ht⟩
    refine ⟨fun y => le_trans (hmax₀ y) (hm x₀ hx₀), ht⟩
  · rintro ⟨hm, ht⟩
    exact ⟨lt_of_lt_of_le hx₀ (hm x₀), fun y _ => hm y, ht⟩

theorem global_of_isNashMax {x : X} {t : ℝ} (h : IsNashMax v₁ v₂ d₁ d₂ x t) :
    ∀ y, S v₁ v₂ y ≤ S v₁ v₂ x := by
  intro y
  by_cases hy : d₁ + d₂ < S v₁ v₂ y
  · exact efficiency v₁ v₂ d₁ d₂ h y hy
  · have hy' : S v₁ v₂ y ≤ d₁ + d₂ := le_of_not_gt hy
    linarith [admissible_pos v₁ v₂ d₁ d₂ h.1]

/-- Target (3): changing the assignment of rights does not change the maximising actions,
provided the efficient action still yields positive total gain. -/
theorem rights_same_actions (d₁' d₂' : ℝ) {x : X} {t : ℝ} (h : IsNashMax v₁ v₂ d₁ d₂ x t)
    (h' : d₁' + d₂' < S v₁ v₂ x) (y : X) :
    (∃ s, IsNashMax v₁ v₂ d₁ d₂ y s) ↔ (∃ s, IsNashMax v₁ v₂ d₁' d₂' y s) := by
  have hg := global_of_isNashMax v₁ v₂ d₁ d₂ h
  have hx := admissible_pos v₁ v₂ d₁ d₂ h.1
  simp only [isNashMax_iff_of_global v₁ v₂ d₁ d₂ hx hg,
    isNashMax_iff_of_global v₁ v₂ d₁' d₂' h' hg, exists_eq_right]

/-- Target (3), transfer part: only the transfer moves, by `((d₁' - d₁) - (d₂' - d₂)) / 2`. -/
theorem rights_move_transfer (d₁' d₂' : ℝ) {x : X} {t : ℝ} (h : IsNashMax v₁ v₂ d₁ d₂ x t)
    (h' : d₁' + d₂' < S v₁ v₂ x) :
    IsNashMax v₁ v₂ d₁' d₂' x (t + ((d₁' - d₁) - (d₂' - d₂)) / 2) ∧
      ∀ y s, IsNashMax v₁ v₂ d₁' d₂' y s →
        S v₁ v₂ y = S v₁ v₂ x ∧ s = halfTransfer v₁ v₂ d₁' d₂' y := by
  have hg := global_of_isNashMax v₁ v₂ d₁ d₂ h
  have ht := transfer_eq v₁ v₂ d₁ d₂ h
  refine ⟨?_, fun y s hys => ?_⟩
  · rw [isNashMax_iff_of_global v₁ v₂ d₁' d₂' h' hg]
    refine ⟨hg, ?_⟩
    rw [ht]; unfold halfTransfer; ring
  · rw [isNashMax_iff_of_global v₁ v₂ d₁' d₂' h' hg] at hys
    exact ⟨le_antisymm (hg y) (hys.1 x), hys.2⟩

/-- Existence for a finite action set. -/
theorem exists_isNashMax [Finite X] :
    (∃ x t, IsNashMax v₁ v₂ d₁ d₂ x t) ↔ ∃ y, d₁ + d₂ < S v₁ v₂ y := by
  constructor
  · rintro ⟨x, t, h⟩
    exact ⟨x, admissible_pos v₁ v₂ d₁ d₂ h.1⟩
  · rintro ⟨y, hy⟩
    have : Nonempty X := ⟨y⟩
    obtain ⟨x₀, hx₀⟩ := Finite.exists_max (S v₁ v₂)
    have hpos : d₁ + d₂ < S v₁ v₂ x₀ := lt_of_lt_of_le hy (hx₀ y)
    exact ⟨x₀, halfTransfer v₁ v₂ d₁ d₂ x₀,
      (isNashMax_iff_of_global v₁ v₂ d₁ d₂ hpos hx₀ x₀ _).mpr ⟨hx₀, rfl⟩⟩

end CoaseNashTUB
