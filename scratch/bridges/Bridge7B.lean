import Mathlib

/-!
# Leaky seal: calibrated trust in a sealed hit

Two worlds, indexed by `θ : Bool`, with prior weight `π` on `θ = true`. A trial draws a lead `l`, an outcome `o`
(both in a finite type `α`) and a leak bit `b`, which is `true` with probability `ε`.

* Steering world (`θ = true`): the lead determines the outcome, `l = o`, and the outcome has law `q`.
* Null world (`θ = false`): the lead is sealed independently, `l ~ p`, `o ~ q`.

`W θ l o b` is the joint weight. The reported hit is `x l o b = 1` when `l = o` or the leak fires (the record is
rewritten to match), else `0`. `θR θ` is the world as a real number. A forecaster with trust `w` reports
`π + w (x - π)` (the prior, moved toward the hit by `w`), and `MSE w` is the mean squared error of that report
against `θR θ` under `W`. With `h0 := Σ p q`, `h := h0 + ε (1 - h0)`, `D := (1-π)(π + h - 2πh)` and
`w_ε := π(1-h)/(π + h - 2πh)`:

PROVED (hypotheses: `p, q ≥ 0`, `Σ p = Σ q = 1`, `h0 < 1`, `ε ∈ [0,1]`, `π ∈ (0,1)`):
* `D_pos`, `mse_excess`: `D > 0` and `MSE w - MSE w_ε = (w - w_ε)^2 D` for every `w`, so `w_ε` is the unique
  MSE-optimal (calibrated) trust.
* `null_mass`, `null_hit`, `null_hit_rate`, `leak_excess`: the null world has total weight `1 - π`,
  `Σ_{l,o,b} W(false,l,o,b) x = (1-π) h`, the null-world conditional hit rate is `h`, and
  `h - h0 = ε (1 - h0) ≤ ε`.
* `even_prior`: at `π = 1/2`, `w_ε = (1-ε)(1-h0)` and `MSE w_ε = h(2-h)/4`.
* `full_leak`, `no_leak`: `w_1 = 0`, and `w_0 = π(1-h0)/(π + h0 - 2πh0) > 0`.
* `wε_strictAntiOn`: `ε ↦ w_ε` is strictly antitone on `[0,1]`.
* `leaky_seal`: (i)-(v) bundled.
* `mse_closed`: `MSE w = π(1-π) - 2wπ(1-π)(1-h) + w^2 D`.

INTERPRETED:
* The target names `W`, `x`, `θR`, `MSE` without definitions; they are fixed here as above (steering world as in
  `SealedEnvelope.steering_hit_eq`, null world as in `SealedEnvelope.null_hit_eq`, leak bit independent of
  everything with weight `ε`, a leak forcing a hit, report `π + w (x - π)`).
* "(ii) made precise" is read as: the null-world weighted hit sum is `(1-π) h`, the null-world mass is `1 - π`,
  their ratio is `h`, and `h - h0 = ε(1-h0) ≤ ε`.
-/

namespace Bridge7B
open Finset

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def h0 (p q : α → ℝ) : ℝ := ∑ a, p a * q a

def h (p q : α → ℝ) (ε : ℝ) : ℝ := h0 p q + ε * (1 - h0 p q)

def D (p q : α → ℝ) (ε π : ℝ) : ℝ := (1 - π) * (π + h p q ε - 2 * π * h p q ε)

def wε (p q : α → ℝ) (ε π : ℝ) : ℝ := π * (1 - h p q ε) / (π + h p q ε - 2 * π * h p q ε)

def leak (ε : ℝ) (b : Bool) : ℝ := if b then ε else 1 - ε

def W (p q : α → ℝ) (ε π : ℝ) (θ : Bool) (l o : α) (b : Bool) : ℝ :=
  if θ then π * (if l = o then q o else 0) * leak ε b
  else (1 - π) * (p l * q o) * leak ε b

def x (l o : α) (b : Bool) : ℝ := if l = o ∨ b = true then 1 else 0

def θR (θ : Bool) : ℝ := if θ then 1 else 0

def MSE (p q : α → ℝ) (ε π w : ℝ) : ℝ :=
  ∑ θ : Bool, ∑ l, ∑ o, ∑ b : Bool,
    W p q ε π θ l o b * (θR θ - (π + w * (x l o b - π))) ^ 2

lemma null_affine (p q : α → ℝ) (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (ε π c0 c1 : ℝ) :
    ∑ l, ∑ o, ∑ b : Bool, W p q ε π false l o b * (c0 + x l o b * c1) =
      (1 - π) * (c0 + h p q ε * c1) := by
  have hb : ∀ l o : α, ∑ b : Bool, W p q ε π false l o b * (c0 + x l o b * c1) =
      (1 - π) * (c0 + c1 * ε) * (p l * q o) +
        (1 - π) * (1 - ε) * c1 * (if l = o then p l * q o else 0) := by
    intro l o
    by_cases hlo : l = o
    · subst hlo; simp [W, leak, x]; ring
    · simp [W, leak, x, hlo]; ring
  simp only [hb, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [hq1, mul_one, hp1]
  unfold h h0
  ring

theorem null_mass (p q : α → ℝ) (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (ε π : ℝ) :
    ∑ l, ∑ o, ∑ b : Bool, W p q ε π false l o b = 1 - π := by
  have := null_affine p q hp1 hq1 ε π 1 0
  simp only [mul_zero, add_zero, mul_one] at this
  exact this

theorem null_hit (p q : α → ℝ) (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (ε π : ℝ) :
    ∑ l, ∑ o, ∑ b : Bool, W p q ε π false l o b * x l o b = (1 - π) * h p q ε := by
  have := null_affine p q hp1 hq1 ε π 0 1
  simp only [zero_add, mul_one] at this
  exact this

lemma true_affine (p q : α → ℝ) (hq1 : ∑ a, q a = 1) (ε π : ℝ) (G : ℝ → ℝ) :
    ∑ l, ∑ o, ∑ b : Bool, W p q ε π true l o b * G (x l o b) = π * G 1 := by
  have hb : ∀ l o : α, ∑ b : Bool, W p q ε π true l o b * G (x l o b) =
      if l = o then π * G 1 * q o else 0 := by
    intro l o
    by_cases hlo : l = o
    · subst hlo; simp [W, leak, x]; ring
    · simp [W, leak, hlo]
  simp only [hb, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum, hq1, mul_one]

theorem mse_closed (p q : α → ℝ) (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (ε π w : ℝ) :
    MSE p q ε π w = π * (1 - π) - 2 * w * (π * (1 - π) * (1 - h p q ε)) + w ^ 2 * D p q ε π := by
  unfold MSE
  rw [Fintype.sum_bool]
  have ht := true_affine p q hq1 ε π (fun t => (θR true - (π + w * (t - π))) ^ 2)
  have hf : ∀ l o b, W p q ε π false l o b * (θR false - (π + w * (x l o b - π))) ^ 2 =
      W p q ε π false l o b * ((π - w * π) ^ 2 +
        x l o b * ((π + w * (1 - π)) ^ 2 - (π - w * π) ^ 2)) := by
    intro l o b
    simp only [θR, Bool.false_eq_true, ite_false]
    unfold x
    split_ifs <;> ring
  simp only [hf]
  rw [null_affine p q hp1 hq1, ht]
  unfold D θR
  simp only [ite_true]
  ring

omit [DecidableEq α] in
lemma h0_nonneg (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) : 0 ≤ h0 p q :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (hp a) (hq a))

omit [DecidableEq α] in
lemma h_bounds (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (hh0 : h0 p q < 1)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : 0 ≤ h p q ε ∧ h p q ε ≤ 1 := by
  have := h0_nonneg p q hp hq
  unfold h
  constructor <;> nlinarith

omit [DecidableEq α] in
lemma S_pos (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (hh0 : h0 p q < 1)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) :
    0 < π + h p q ε - 2 * π * h p q ε := by
  obtain ⟨hl, hu⟩ := h_bounds p q hp hq hh0 ε hε0 hε1
  rcases hu.lt_or_eq with hlt | heq
  · nlinarith [mul_pos hπ0 (sub_pos.mpr hlt), mul_nonneg (sub_pos.mpr hπ1).le hl]
  · rw [heq]; linarith

omit [DecidableEq α] in
theorem D_pos (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (hh0 : h0 p q < 1)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) :
    0 < D p q ε π :=
  mul_pos (sub_pos.mpr hπ1) (S_pos p q hp hq hh0 ε hε0 hε1 π hπ0 hπ1)

theorem mse_excess (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (hh0 : h0 p q < 1)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) :
    0 < D p q ε π ∧
      ∀ w, MSE p q ε π w - MSE p q ε π (wε p q ε π) = (w - wε p q ε π) ^ 2 * D p q ε π := by
  refine ⟨D_pos p q hp hq hh0 ε hε0 hε1 π hπ0 hπ1, fun w => ?_⟩
  have hS := (S_pos p q hp hq hh0 ε hε0 hε1 π hπ0 hπ1).ne'
  have key : D p q ε π * wε p q ε π = π * (1 - π) * (1 - h p q ε) := by
    unfold D wε
    rw [mul_comm, div_mul_eq_mul_div, div_eq_iff hS]
    ring
  rw [mse_closed p q hp1 hq1, mse_closed p q hp1 hq1]
  linear_combination 2 * (w - wε p q ε π) * key

theorem null_hit_rate (p q : α → ℝ) (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (ε π : ℝ)
    (hπ1 : π < 1) :
    (∑ l, ∑ o, ∑ b : Bool, W p q ε π false l o b * x l o b) /
      (∑ l, ∑ o, ∑ b : Bool, W p q ε π false l o b) = h p q ε := by
  rw [null_hit p q hp1 hq1, null_mass p q hp1 hq1]
  have : (1 - π) ≠ 0 := (sub_pos.mpr hπ1).ne'
  field_simp

omit [DecidableEq α] in
theorem leak_excess (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (ε : ℝ) (hε0 : 0 ≤ ε) :
    h p q ε - h0 p q = ε * (1 - h0 p q) ∧ ε * (1 - h0 p q) ≤ ε := by
  have := h0_nonneg p q hp hq
  refine ⟨by unfold h; ring, by nlinarith⟩

theorem even_prior (p q : α → ℝ) (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (ε : ℝ) :
    wε p q ε (1 / 2) = (1 - ε) * (1 - h0 p q) ∧
      MSE p q ε (1 / 2) (wε p q ε (1 / 2)) = h p q ε * (2 - h p q ε) / 4 := by
  have hw : wε p q ε (1 / 2) = 1 - h p q ε := by
    unfold wε
    rw [show (1 / 2 : ℝ) + h p q ε - 2 * (1 / 2) * h p q ε = 1 / 2 by ring]
    field_simp
  refine ⟨by rw [hw]; unfold h; ring, ?_⟩
  rw [mse_closed p q hp1 hq1, hw]
  unfold D
  ring

omit [DecidableEq α] in
theorem full_leak (p q : α → ℝ) (π : ℝ) : wε p q 1 π = 0 := by
  unfold wε h
  simp

omit [DecidableEq α] in
theorem no_leak (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (hh0 : h0 p q < 1)
    (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) :
    wε p q 0 π = π * (1 - h0 p q) / (π + h0 p q - 2 * π * h0 p q) ∧
      0 < π * (1 - h0 p q) / (π + h0 p q - 2 * π * h0 p q) := by
  have hS := S_pos p q hp hq hh0 0 le_rfl zero_le_one π hπ0 hπ1
  have h00 : h p q 0 = h0 p q := by unfold h; ring
  rw [h00] at hS
  refine ⟨by unfold wε; rw [h00], ?_⟩
  exact div_pos (mul_pos hπ0 (sub_pos.mpr hh0)) hS

omit [DecidableEq α] in
theorem wε_strictAntiOn (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (hh0 : h0 p q < 1)
    (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) :
    StrictAntiOn (fun ε => wε p q ε π) (Set.Icc 0 1) := by
  intro e1 he1 e2 he2 hlt
  have hS1 := S_pos p q hp hq hh0 e1 he1.1 he1.2 π hπ0 hπ1
  have hS2 := S_pos p q hp hq hh0 e2 he2.1 he2.2 π hπ0 hπ1
  have hhlt : h p q e1 < h p q e2 := by
    unfold h; nlinarith [sub_pos.mpr hh0]
  show wε p q e2 π < wε p q e1 π
  unfold wε
  rw [div_lt_div_iff₀ hS2 hS1]
  nlinarith [mul_pos (mul_pos hπ0 (sub_pos.mpr hπ1)) (sub_pos.mpr hhlt)]

theorem leaky_seal (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (hh0 : h0 p q < 1)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) :
    (0 < D p q ε π ∧
      ∀ w, MSE p q ε π w - MSE p q ε π (wε p q ε π) = (w - wε p q ε π) ^ 2 * D p q ε π) ∧
    (∑ l, ∑ o, ∑ b : Bool, W p q ε π false l o b * x l o b = (1 - π) * h p q ε ∧
      (∑ l, ∑ o, ∑ b : Bool, W p q ε π false l o b * x l o b) /
        (∑ l, ∑ o, ∑ b : Bool, W p q ε π false l o b) = h p q ε ∧
      h p q ε - h0 p q = ε * (1 - h0 p q) ∧ ε * (1 - h0 p q) ≤ ε) ∧
    (wε p q ε (1 / 2) = (1 - ε) * (1 - h0 p q) ∧
      MSE p q ε (1 / 2) (wε p q ε (1 / 2)) = h p q ε * (2 - h p q ε) / 4) ∧
    (wε p q 1 π = 0 ∧ wε p q 0 π = π * (1 - h0 p q) / (π + h0 p q - 2 * π * h0 p q) ∧
      0 < π * (1 - h0 p q) / (π + h0 p q - 2 * π * h0 p q)) ∧
    StrictAntiOn (fun e => wε p q e π) (Set.Icc 0 1) :=
  ⟨mse_excess p q hp hq hp1 hq1 hh0 ε hε0 hε1 π hπ0 hπ1,
    ⟨null_hit p q hp1 hq1 ε π, null_hit_rate p q hp1 hq1 ε π hπ1, leak_excess p q hp hq ε hε0⟩,
    even_prior p q hp1 hq1 ε,
    ⟨full_leak p q π, no_leak p q hp hq hh0 π hπ0 hπ1⟩,
    wε_strictAntiOn p q hp hq hh0 π hπ0 hπ1⟩

end

end Bridge7B
