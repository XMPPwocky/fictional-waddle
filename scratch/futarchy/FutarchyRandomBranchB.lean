import Mathlib

/-!
# Futarchy with a randomized branch: the N/A rule removes confounding bias

Model (finite joint law, explicit finite sums over `U ∈ Fin 2` and `R ∈ Fin 2`).
`A` ranges over an arbitrary type `α`; all statements are pointwise in a fixed action `a`.

* `pU π u` is the confounder prior: `P(U=0) = 1-π`, `P(U=1) = π`.
* `joint ε π ρ c r u a = P(R=r, U=u, A=a)`:
  `ε · pU π u · ρ a` if `r = 1` (random branch, `A ⊥ U`), and
  `(1-ε) · pU π u · c a u` if `r = 0` (chooser branch, `A` depends on `U`).
* `m u a = E[Y | U=u, A=a]`, assumed not to depend on the branch `R`
  (the outcome is caused by `U` and `A` only).
* `V π m a = Σ_u pU π u · m u a`, the causal value of `do(A=a)`.
* `priceNA = E[Y | A=a, R=1]` and `priceAll = E[Y | A=a]`, and
  `postU1 = P(U=1 | A=a)`, all written as ratios of finite sums of `joint`.
* `chosenBias` is the bias of the fully chosen market (`ε = 0`):
  `(πc(a|1)/((1-π)c(a|0)+πc(a|1)) - π)(m(1,a)-m(0,a))`.

PROVED (hypotheses: `0 < π < 1`, `0 < ρ a`, `0 ≤ c a u`, and `0 < ε ≤ 1` where needed):
* `joint_total`: the joint law has total mass 1 when `ρ` and each `c · u` are distributions
  on a finite `α` (sanity check of the model).
* `priceNA_eq_V`: (1) `E[Y | A=a, R=1] = V(a)` exactly (only `ε ≠ 0`, `ρ a ≠ 0` needed).
* `postU1_eq`: `P(U=1 | A=a)` equals the stated closed formula.
* `bias_eq`: (2) `E[Y | A=a] - V(a) = (P(U=1 | A=a) - π)(m(1,a) - m(0,a))`.
* `bias_closed`: `E[Y|A=a] - V(a) = (1-ε)π(1-π)(c(a|1)-c(a|0))(m(1,a)-m(0,a)) / D(ε)`
  with `D(ε) = ερ(a) + (1-ε)((1-π)c(a|0) + πc(a|1)) > 0`.
* `bias_eq_zero_iff`: the bias vanishes iff `ε = 1 ∨ c(a|1) = c(a|0) ∨ m(1,a) = m(0,a)`
  (iff-form of (3)).
* `bias_ne_zero`: (3) if `c(a|1) ≠ c(a|0)`, `m(1,a) ≠ m(0,a)`, `ε < 1`, the bias is nonzero.
* `bias_tendsto_chosen`, `bias_tendsto_chosen_right`: (3) as `ε → 0` (two-sided, hence also
  from the right) the bias tends to `chosenBias`; `chosenBias_ne_zero` shows that limit is
  nonzero under the same hypotheses.
* `bias_tendsto_zero_at_one`, `bias_tendsto_zero_at_one_left`: (3) as `ε → 1` the bias
  tends to `0`; `bias_at_one`: at `ε = 1` it is exactly `0`.

INTERPRETED:
* "Market price" = conditional expectation under the joint law; the N/A rule = conditioning
  on `R = 1`. Market microstructure, fees, and trader beliefs are not modelled.
* `E[Y | U, A, R] = m(U, A)`: being in the random branch does not change the outcome
  given `(U, A)`. This is the assumption under which (1) holds.
* Limits in `ε` are taken of the real-number expression `priceAll ε … - V …`, which is
  defined for all real `ε`; its value at `ε = 0` is the fully chosen market's bias.
-/

namespace FutarchyRandomBranchB

open Finset Filter Topology

variable {α : Type*}

/-- Confounder prior: `P(U=0) = 1-π`, `P(U=1) = π`. -/
def pU (π : ℝ) : Fin 2 → ℝ := ![1 - π, π]

/-- Joint mass `P(R=r, U=u, A=a)`; `r = 1` is the random branch. -/
def joint (ε π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (r u : Fin 2) (a : α) : ℝ :=
  if r = 1 then ε * pU π u * ρ a else (1 - ε) * pU π u * c a u

/-- Causal value `V(a) = (1-π) m(0,a) + π m(1,a)`. -/
def V (π : ℝ) (m : Fin 2 → α → ℝ) (a : α) : ℝ := ∑ u, pU π u * m u a

/-- `E[Y | A=a, R=1]`: the price under the N/A rule. -/
noncomputable def priceNA (ε π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ)
    (a : α) : ℝ :=
  (∑ u, joint ε π ρ c 1 u a * m u a) / ∑ u, joint ε π ρ c 1 u a

/-- `E[Y | A=a]`: the price without the N/A rule. -/
noncomputable def priceAll (ε π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ)
    (a : α) : ℝ :=
  (∑ r, ∑ u, joint ε π ρ c r u a * m u a) / ∑ r, ∑ u, joint ε π ρ c r u a

/-- `P(U=1 | A=a)`. -/
noncomputable def postU1 (ε π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (a : α) : ℝ :=
  (∑ r, joint ε π ρ c r 1 a) / ∑ r, ∑ u, joint ε π ρ c r u a

/-- Denominator `D(ε) = P(A=a)`. -/
def D (ε π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (a : α) : ℝ :=
  ε * ρ a + (1 - ε) * ((1 - π) * c a 0 + π * c a 1)

/-- Bias of the fully chosen market (`ε = 0`). -/
noncomputable def chosenBias (π : ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ) (a : α) : ℝ :=
  (π * c a 1 / ((1 - π) * c a 0 + π * c a 1) - π) * (m 1 a - m 0 a)

theorem joint_total [Fintype α] (ε π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ)
    (hρ : ∑ a, ρ a = 1) (hc : ∀ u, ∑ a, c a u = 1) :
    ∑ r, ∑ u, ∑ a, joint ε π ρ c r u a = 1 := by
  simp only [Fin.sum_univ_two, joint, pU]
  simp only [Fin.isValue, zero_ne_one, ite_false, ite_true, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, ← Finset.mul_sum, hρ, hc]
  ring

theorem sum_joint_eq_D (ε π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (a : α) :
    ∑ r, ∑ u, joint ε π ρ c r u a = D ε π ρ c a := by
  simp [Fin.sum_univ_two, joint, pU, D]
  ring

theorem D_pos {ε π : ℝ} {ρ : α → ℝ} {c : α → Fin 2 → ℝ} {a : α}
    (hπ0 : 0 < π) (hπ1 : π < 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ a)
    (hc : ∀ u, 0 ≤ c a u) : 0 < D ε π ρ c a := by
  have h0 := hc 0
  have h1 := hc 1
  unfold D
  have : 0 ≤ (1 - ε) * ((1 - π) * c a 0 + π * c a 1) := by
    apply mul_nonneg (by linarith)
    have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - π) h0
    have := mul_nonneg hπ0.le h1
    linarith
  have := mul_pos hε0 hρ
  linarith

/-- (1) Under the N/A rule the price is the causal value. -/
theorem priceNA_eq_V (ε π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ) (a : α)
    (hε : ε ≠ 0) (hρ : ρ a ≠ 0) :
    priceNA ε π ρ c m a = V π m a := by
  simp only [priceNA, V, joint, pU, Fin.sum_univ_two, ite_true, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

theorem postU1_eq (ε π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (a : α) :
    postU1 ε π ρ c a =
      (ε * ρ a * π + (1 - ε) * c a 1 * π) /
        (ε * ρ a + (1 - ε) * ((1 - π) * c a 0 + π * c a 1)) := by
  rw [postU1, sum_joint_eq_D]
  simp [Fin.sum_univ_two, joint, pU, D]
  ring

/-- (2) The un-N/A'd price is biased by `(P(U=1|A=a) - π)(m(1,a) - m(0,a))`. -/
theorem bias_eq {ε π : ℝ} {ρ : α → ℝ} {c : α → Fin 2 → ℝ} (m : Fin 2 → α → ℝ) {a : α}
    (hπ0 : 0 < π) (hπ1 : π < 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ a)
    (hc : ∀ u, 0 ≤ c a u) :
    priceAll ε π ρ c m a - V π m a = (postU1 ε π ρ c a - π) * (m 1 a - m 0 a) := by
  have hD := (D_pos hπ0 hπ1 hε0 hε1 hρ hc).ne'
  unfold priceAll postU1
  rw [sum_joint_eq_D]
  simp only [D] at hD
  simp [Fin.sum_univ_two, joint, pU, V, D]
  field_simp
  ring

theorem bias_closed {ε π : ℝ} {ρ : α → ℝ} {c : α → Fin 2 → ℝ} (m : Fin 2 → α → ℝ) {a : α}
    (hπ0 : 0 < π) (hπ1 : π < 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ a)
    (hc : ∀ u, 0 ≤ c a u) :
    priceAll ε π ρ c m a - V π m a =
      (1 - ε) * π * (1 - π) * (c a 1 - c a 0) * (m 1 a - m 0 a) / D ε π ρ c a := by
  have hD := (D_pos hπ0 hπ1 hε0 hε1 hρ hc).ne'
  unfold priceAll
  rw [sum_joint_eq_D]
  simp only [D] at hD ⊢
  simp [Fin.sum_univ_two, joint, pU, V]
  field_simp
  ring

/-- (3), iff form: the bias vanishes exactly when `ε = 1`, or the chooser ignores `U` at `a`,
or `U` does not affect the outcome at `a`. -/
theorem bias_eq_zero_iff {ε π : ℝ} {ρ : α → ℝ} {c : α → Fin 2 → ℝ} (m : Fin 2 → α → ℝ)
    {a : α} (hπ0 : 0 < π) (hπ1 : π < 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ a)
    (hc : ∀ u, 0 ≤ c a u) :
    priceAll ε π ρ c m a - V π m a = 0 ↔ ε = 1 ∨ c a 1 = c a 0 ∨ m 1 a = m 0 a := by
  have hD := (D_pos hπ0 hπ1 hε0 hε1 hρ hc).ne'
  rw [bias_closed m hπ0 hπ1 hε0 hε1 hρ hc, div_eq_zero_iff]
  simp only [hD, or_false, mul_eq_zero, sub_eq_zero, hπ0.ne', hπ1.ne', or_false]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h.symm)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- (3) With a confounded chooser and a confounder that matters, every `ε < 1` leaves bias. -/
theorem bias_ne_zero {ε π : ℝ} {ρ : α → ℝ} {c : α → Fin 2 → ℝ} (m : Fin 2 → α → ℝ)
    {a : α} (hπ0 : 0 < π) (hπ1 : π < 1) (hε0 : 0 < ε) (hε1 : ε < 1) (hρ : 0 < ρ a)
    (hc : ∀ u, 0 ≤ c a u) (hcU : c a 1 ≠ c a 0) (hm : m 1 a ≠ m 0 a) :
    priceAll ε π ρ c m a - V π m a ≠ 0 := by
  rw [Ne, bias_eq_zero_iff m hπ0 hπ1 hε0 hε1.le hρ hc]
  rintro (h | h | h)
  · exact hε1.ne h
  · exact hcU h
  · exact hm h

theorem D0_pos {π : ℝ} {c : α → Fin 2 → ℝ} {a : α} (hπ0 : 0 < π) (hπ1 : π < 1)
    (hc : ∀ u, 0 ≤ c a u) (hcU : c a 1 ≠ c a 0) : 0 < (1 - π) * c a 0 + π * c a 1 := by
  have h0 := hc 0
  have h1 := hc 1
  rcases (lt_or_gt_of_ne hcU) with h | h
  · have := mul_pos (by linarith : (0:ℝ) < 1 - π) (lt_of_le_of_lt h1 h)
    have := mul_nonneg hπ0.le h1
    linarith
  · have := mul_pos hπ0 (lt_of_le_of_lt h0 h)
    have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - π) h0
    linarith

theorem chosenBias_ne_zero {π : ℝ} {c : α → Fin 2 → ℝ} (m : Fin 2 → α → ℝ) {a : α}
    (hπ0 : 0 < π) (hπ1 : π < 1) (hc : ∀ u, 0 ≤ c a u) (hcU : c a 1 ≠ c a 0)
    (hm : m 1 a ≠ m 0 a) : chosenBias π c m a ≠ 0 := by
  have hD0 := (D0_pos hπ0 hπ1 hc hcU).ne'
  have key : chosenBias π c m a =
      π * (1 - π) * (c a 1 - c a 0) * (m 1 a - m 0 a) / ((1 - π) * c a 0 + π * c a 1) := by
    unfold chosenBias
    field_simp
    ring
  rw [key]
  refine div_ne_zero ?_ hD0
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero hπ0.ne' ?_) (sub_ne_zero.mpr hcU))
    (sub_ne_zero.mpr hm)
  linarith

/-- The bias as an explicit function of `ε` (valid for every real `ε`). -/
theorem bias_fun_eq (π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ) (a : α) :
    (fun ε => priceAll ε π ρ c m a - V π m a) = fun ε =>
      (ε * ((1 - π) * ρ a * m 0 a + π * ρ a * m 1 a) +
          (1 - ε) * ((1 - π) * c a 0 * m 0 a + π * c a 1 * m 1 a)) / D ε π ρ c a -
        ((1 - π) * m 0 a + π * m 1 a) := by
  funext ε
  unfold priceAll
  rw [sum_joint_eq_D]
  simp [Fin.sum_univ_two, joint, pU, V]
  congr 1
  ring

theorem bias_continuousAt (π : ℝ) (ρ : α → ℝ) (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ)
    (a : α) (ε₀ : ℝ) (h : D ε₀ π ρ c a ≠ 0) :
    ContinuousAt (fun ε => priceAll ε π ρ c m a - V π m a) ε₀ := by
  rw [bias_fun_eq]
  refine ContinuousAt.sub (ContinuousAt.div ?_ ?_ h) continuousAt_const
  · fun_prop
  · unfold D
    fun_prop

/-- (3) As `ε → 0` the bias tends to the fully chosen market's bias. -/
theorem bias_tendsto_chosen {π : ℝ} {ρ : α → ℝ} {c : α → Fin 2 → ℝ} (m : Fin 2 → α → ℝ)
    {a : α} (hπ0 : 0 < π) (hπ1 : π < 1) (hc : ∀ u, 0 ≤ c a u) (hcU : c a 1 ≠ c a 0) :
    Tendsto (fun ε => priceAll ε π ρ c m a - V π m a) (𝓝 0) (𝓝 (chosenBias π c m a)) := by
  have hD0 := (D0_pos hπ0 hπ1 hc hcU).ne'
  have hD : D 0 π ρ c a ≠ 0 := by simpa [D] using hD0
  have hval : priceAll 0 π ρ c m a - V π m a = chosenBias π c m a := by
    have := congrFun (bias_fun_eq π ρ c m a) 0
    rw [this]
    simp only [D, chosenBias, zero_mul, sub_zero, one_mul, zero_add]
    field_simp
    ring
  rw [← hval]
  exact (bias_continuousAt π ρ c m a 0 hD).tendsto

theorem bias_tendsto_chosen_right {π : ℝ} {ρ : α → ℝ} {c : α → Fin 2 → ℝ}
    (m : Fin 2 → α → ℝ) {a : α} (hπ0 : 0 < π) (hπ1 : π < 1) (hc : ∀ u, 0 ≤ c a u)
    (hcU : c a 1 ≠ c a 0) :
    Tendsto (fun ε => priceAll ε π ρ c m a - V π m a) (𝓝[>] 0) (𝓝 (chosenBias π c m a)) :=
  (bias_tendsto_chosen m hπ0 hπ1 hc hcU).mono_left nhdsWithin_le_nhds

theorem bias_at_one (π : ℝ) {ρ : α → ℝ} (c : α → Fin 2 → ℝ) (m : Fin 2 → α → ℝ) {a : α}
    (hρ : ρ a ≠ 0) : priceAll 1 π ρ c m a - V π m a = 0 := by
  have := congrFun (bias_fun_eq π ρ c m a) 1
  rw [this]
  simp only [D, sub_self, zero_mul, add_zero, one_mul]
  field_simp
  ring

/-- (3) As `ε → 1` the bias tends to `0`. -/
theorem bias_tendsto_zero_at_one (π : ℝ) {ρ : α → ℝ} (c : α → Fin 2 → ℝ)
    (m : Fin 2 → α → ℝ) {a : α} (hρ : ρ a ≠ 0) :
    Tendsto (fun ε => priceAll ε π ρ c m a - V π m a) (𝓝 1) (𝓝 0) := by
  have hD : D 1 π ρ c a ≠ 0 := by simpa [D] using hρ
  rw [← bias_at_one π c m hρ]
  exact (bias_continuousAt π ρ c m a 1 hD).tendsto

theorem bias_tendsto_zero_at_one_left (π : ℝ) {ρ : α → ℝ} (c : α → Fin 2 → ℝ)
    (m : Fin 2 → α → ℝ) {a : α} (hρ : ρ a ≠ 0) :
    Tendsto (fun ε => priceAll ε π ρ c m a - V π m a) (𝓝[<] 1) (𝓝 0) :=
  (bias_tendsto_zero_at_one π c m hρ).mono_left nhdsWithin_le_nhds

end FutarchyRandomBranchB
