import Mathlib

/-!
# Leaky seal: calibrated trust in a sealed hit

Setting. `α` is a finite type, `p q : α → ℝ` are probability vectors (lead law and idea law), `h0 := Σ p q < 1`,
`ε ∈ [0,1]` is the post-seal rewrite probability, and `π ∈ (0,1)` is the prior on the steering world.
On `Ω := Bool × α × α × Bool` (world `θ`, lead `l`, idea `o`, leak `b`) the weight is
`W(θ,l,o,b) := (if θ then π * (if l = o then q o else 0) else (1 - π) * p l * q o) * (if b then ε else 1 - ε)`.
The record is `r := if b then o else l`, the observation `x := [r = o]`, the target `θR := [θ]`, and
`MSE w := Σ_Ω W * (w * x + (1 - w) * π - θR)^2`. Put `h := h0 + ε(1 - h0)`,
`D := (1 - π)(π + h - 2πh)` and `w_ε := π(1 - h)/(π + h - 2πh)`.

PROVED:
* `part_i`: `D > 0`, and `MSE w - MSE w_ε = (w - w_ε)^2 * D` for every `w`.
* `part_ii`: `Σ_{l,o,b} W(false,l,o,b) * x(false,l,o,b) = (1 - π) * h`, `Σ_{l,o,b} W(false,l,o,b) = 1 - π`,
  hence the null-world conditional hit rate is `h`; and `h - h0 = ε(1 - h0) ≤ ε`.
* `part_iii`: at `π = 1/2`, `w_ε = (1 - ε)(1 - h0)` and `MSE w_ε = h(2 - h)/4`.
* `part_iv`: `w_1 = 0`, and `w_0 = π(1 - h0)/(π + h0 - 2π h0) > 0`.
* `part_v`: `ε ↦ w_ε` is strictly antitone on `[0,1]`.
* `main`: the conjunction of (i)-(v).
* Auxiliary: `sum_W_F` (the law of `(θ, x)` under `W`), `mse_eq` (closed form of `MSE`), `sum_W` (`W` has mass 1).

INTERPRETED:
* `θ = false` is the null world of `SealedEnvelope.null_hit_eq` (lead and idea independent), `θ = true` the steering
  world of `SealedEnvelope.steering_hit_eq` (lead equals idea); `b` is an independent post-seal rewrite that replaces
  the record by the idea.
* `w_ε` is the weight a calibrated affine forecaster `w * x + (1 - w) * π` puts on a reported hit; `w_1 = 0` is the
  hindsight endpoint and `w_0` the fully sealed endpoint.
-/

namespace Bridge7A
open Finset

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Joint weight on `Ω = Bool × α × α × Bool` (world, lead, idea, leak). -/
def W (p q : α → ℝ) (π ε : ℝ) (z : Bool × α × α × Bool) : ℝ :=
  (if z.1 then π * (if z.2.1 = z.2.2.1 then q z.2.2.1 else 0) else (1 - π) * p z.2.1 * q z.2.2.1) *
    (if z.2.2.2 then ε else 1 - ε)

/-- The reported record: the idea if the seal leaked, otherwise the sealed lead. -/
def r (z : Bool × α × α × Bool) : α := if z.2.2.2 then z.2.2.1 else z.2.1

/-- The observation: the record hits the idea. -/
def x (z : Bool × α × α × Bool) : ℝ := if r z = z.2.2.1 then 1 else 0

/-- The target: indicator of the steering world. -/
def θR (z : Bool × α × α × Bool) : ℝ := if z.1 then 1 else 0

def MSE (p q : α → ℝ) (π ε w : ℝ) : ℝ :=
  ∑ z : Bool × α × α × Bool, W p q π ε z * (w * x z + (1 - w) * π - θR z) ^ 2

def h0 (p q : α → ℝ) : ℝ := ∑ a, p a * q a

def h (p q : α → ℝ) (ε : ℝ) : ℝ := h0 p q + ε * (1 - h0 p q)

def D (p q : α → ℝ) (π ε : ℝ) : ℝ := (1 - π) * (π + h p q ε - 2 * π * h p q ε)

def wε (p q : α → ℝ) (π ε : ℝ) : ℝ := π * (1 - h p q ε) / (π + h p q ε - 2 * π * h p q ε)

lemma sum_true (p q : α → ℝ) (hq1 : ∑ a, q a = 1) (π ε : ℝ) (g : ℝ → ℝ) :
    ∑ y : α × α × Bool, W p q π ε (true, y) * g (x (true, y)) = π * g 1 := by
  have hpt : ∀ y : α × α × Bool, W p q π ε (true, y) * g (x (true, y)) =
      W p q π ε (true, y) * g 1 := by
    rintro ⟨l, o, b⟩
    by_cases hlo : l = o
    · subst hlo; simp [x, r]
    · simp [W, hlo]
  simp_rw [hpt]
  have hb : ∀ l o : α, ∑ b : Bool, W p q π ε (true, l, o, b) * g 1 =
      π * g 1 * (if l = o then q o else 0) := by
    intro l o
    by_cases hlo : l = o
    · simp [W, hlo]; ring
    · simp [W, hlo]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, hb]
  simp [← Finset.mul_sum, hq1]

lemma sum_false (p q : α → ℝ) (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (π ε : ℝ) (g : ℝ → ℝ) :
    ∑ y : α × α × Bool, W p q π ε (false, y) * g (x (false, y)) =
      (1 - π) * (h p q ε * g 1 + (1 - h p q ε) * g 0) := by
  have hb : ∀ l o : α, ∑ b : Bool, W p q π ε (false, l, o, b) * g (x (false, l, o, b)) =
      (1 - π) * (ε * g 1 + (1 - ε) * g 0) * (p l * q o) +
        (1 - π) * (1 - ε) * (g 1 - g 0) * (if l = o then p l * q o else 0) := by
    intro l o
    by_cases hlo : l = o
    · subst hlo; simp [W, x, r]; ring
    · simp [W, x, r, hlo]; ring
  have hpq : ∑ l, ∑ o, p l * q o = 1 := by
    rw [← Finset.sum_mul_sum, hp1, hq1, one_mul]
  have hdiag : ∑ l, ∑ o, (if l = o then p l * q o else 0) = h0 p q := by
    simp [h0]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, hb]
  rw [show ∑ l, ∑ o, ((1 - π) * (ε * g 1 + (1 - ε) * g 0) * (p l * q o) +
        (1 - π) * (1 - ε) * (g 1 - g 0) * (if l = o then p l * q o else 0)) =
      (1 - π) * (ε * g 1 + (1 - ε) * g 0) * (∑ l, ∑ o, p l * q o) +
        (1 - π) * (1 - ε) * (g 1 - g 0) * (∑ l, ∑ o, (if l = o then p l * q o else 0)) by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]]
  rw [hpq, hdiag]
  unfold h; ring

/-- The law of `(θ, x)` under `W`. -/
theorem sum_W_F (p q : α → ℝ) (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (π ε : ℝ)
    (F : Bool → ℝ → ℝ) :
    ∑ z : Bool × α × α × Bool, W p q π ε z * F z.1 (x z) =
      π * F true 1 + (1 - π) * (h p q ε * F false 1 + (1 - h p q ε) * F false 0) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [sum_true p q hq1 π ε (F true), sum_false p q hp1 hq1 π ε (F false)]

theorem sum_W (p q : α → ℝ) (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (π ε : ℝ) :
    ∑ z : Bool × α × α × Bool, W p q π ε z = 1 := by
  have := sum_W_F p q hp1 hq1 π ε (fun _ _ => 1)
  simp only [mul_one] at this
  rw [this]; ring

theorem mse_eq (p q : α → ℝ) (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (π ε w : ℝ) :
    MSE p q π ε w = π * (w + (1 - w) * π - 1) ^ 2 +
      (1 - π) * (h p q ε * (w + (1 - w) * π) ^ 2 + (1 - h p q ε) * ((1 - w) * π) ^ 2) := by
  calc MSE p q π ε w
      = ∑ z : Bool × α × α × Bool, W p q π ε z *
          (fun (θ : Bool) (t : ℝ) => (w * t + (1 - w) * π - if θ then 1 else 0) ^ 2) z.1 (x z) := rfl
    _ = _ := sum_W_F p q hp1 hq1 π ε
          (fun (θ : Bool) (t : ℝ) => (w * t + (1 - w) * π - if θ then 1 else 0) ^ 2)
    _ = _ := by simp

omit [DecidableEq α] in
lemma h0_nonneg (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) : 0 ≤ h0 p q :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (hp a) (hq a))

omit [DecidableEq α] in
lemma h_mem (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (hh0 : h0 p q < 1) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : 0 ≤ h p q ε ∧ h p q ε ≤ 1 := by
  have := h0_nonneg p q hp hq
  unfold h
  constructor <;> nlinarith

lemma denom_pos (π t : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < π + t - 2 * π * t := by
  rcases lt_or_eq_of_le ht1 with ht | ht
  · nlinarith [mul_pos hπ0 (sub_pos.mpr ht), mul_nonneg (sub_pos.mpr hπ1).le ht0]
  · subst ht; linarith

/-- (i) `D > 0` and the miscalibration cost is exactly quadratic with curvature `D`. -/
theorem part_i (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (hh0 : h0 p q < 1) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) :
    0 < D p q π ε ∧
      ∀ w, MSE p q π ε w - MSE p q π ε (wε p q π ε) = (w - wε p q π ε) ^ 2 * D p q π ε := by
  obtain ⟨ht0, ht1⟩ := h_mem p q hp hq hh0 ε hε0 hε1
  have hd := denom_pos π (h p q ε) hπ0 hπ1 ht0 ht1
  refine ⟨mul_pos (sub_pos.mpr hπ1) hd, fun w => ?_⟩
  rw [mse_eq p q hp1 hq1, mse_eq p q hp1 hq1]
  have hw : wε p q π ε * (π + h p q ε - 2 * π * h p q ε) = π * (1 - h p q ε) := by
    unfold wε; exact div_mul_cancel₀ _ hd.ne'
  unfold D
  linear_combination (2 * (1 - π) * (w - wε p q π ε)) * hw

/-- (ii) The null-world reported hit mass is `(1 - π) h`, the null-world mass is `1 - π`, so the conditional hit rate
is `h`; the leak inflates it by `ε(1 - h0) ≤ ε`. -/
theorem part_ii (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (ε : ℝ) (hε0 : 0 ≤ ε) (π : ℝ) (hπ1 : π < 1) :
    (∑ l, ∑ o, ∑ b, W p q π ε (false, l, o, b) * x (false, l, o, b) = (1 - π) * h p q ε) ∧
      (∑ l, ∑ o, ∑ b, W p q π ε (false, l, o, b) = 1 - π) ∧
      (∑ l, ∑ o, ∑ b, W p q π ε (false, l, o, b) * x (false, l, o, b)) /
          (∑ l, ∑ o, ∑ b, W p q π ε (false, l, o, b)) = h p q ε ∧
      h p q ε - h0 p q = ε * (1 - h0 p q) ∧ ε * (1 - h0 p q) ≤ ε := by
  have e1 : ∑ l, ∑ o, ∑ b, W p q π ε (false, l, o, b) * x (false, l, o, b) = (1 - π) * h p q ε := by
    have := sum_false p q hp1 hq1 π ε id
    simp only [Fintype.sum_prod_type, id] at this
    rw [this]; ring
  have e2 : ∑ l, ∑ o, ∑ b, W p q π ε (false, l, o, b) = 1 - π := by
    have := sum_false p q hp1 hq1 π ε (fun _ => 1)
    simp only [Fintype.sum_prod_type, mul_one] at this
    rw [this]; ring
  have hh := h0_nonneg p q hp hq
  refine ⟨e1, e2, ?_, by unfold h; ring, by nlinarith⟩
  rw [e1, e2]
  have : (1 - π) ≠ 0 := (sub_pos.mpr hπ1).ne'
  field_simp

/-- (iii) At an even prior the calibrated trust factorizes as `(1 - ε)(1 - h0)`, with residual `h(2 - h)/4`. -/
theorem part_iii (p q : α → ℝ) (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (ε : ℝ) :
    wε p q (1 / 2) ε = (1 - ε) * (1 - h0 p q) ∧
      MSE p q (1 / 2) ε (wε p q (1 / 2) ε) = h p q ε * (2 - h p q ε) / 4 := by
  have hw : wε p q (1 / 2) ε = 1 - h p q ε := by
    unfold wε
    have : (1 / 2 : ℝ) + h p q ε - 2 * (1 / 2) * h p q ε = 1 / 2 := by ring
    rw [this]; ring
  refine ⟨by rw [hw]; unfold h; ring, ?_⟩
  rw [mse_eq p q hp1 hq1, hw]
  ring

omit [DecidableEq α] in
/-- (iv) Endpoints: full leak gives zero trust; a perfect seal gives positive trust. -/
theorem part_iv (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (hh0 : h0 p q < 1)
    (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) :
    wε p q π 1 = 0 ∧
      wε p q π 0 = π * (1 - h0 p q) / (π + h0 p q - 2 * π * h0 p q) ∧
      0 < π * (1 - h0 p q) / (π + h0 p q - 2 * π * h0 p q) := by
  have hh := h0_nonneg p q hp hq
  refine ⟨by simp [wε, h], by simp [wε, h], ?_⟩
  exact div_pos (mul_pos hπ0 (sub_pos.mpr hh0)) (denom_pos π _ hπ0 hπ1 hh hh0.le)

omit [DecidableEq α] in
/-- (v) Trust in a sealed hit strictly decreases with the leak probability. -/
theorem part_v (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (hh0 : h0 p q < 1)
    (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) :
    StrictAntiOn (fun ε => wε p q π ε) (Set.Icc 0 1) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := h_mem p q hp hq hh0 a ha.1 ha.2
  obtain ⟨hb0, hb1⟩ := h_mem p q hp hq hh0 b hb.1 hb.2
  have hda := denom_pos π _ hπ0 hπ1 ha0 ha1
  have hdb := denom_pos π _ hπ0 hπ1 hb0 hb1
  have hlt : h p q a < h p q b := by
    unfold h; nlinarith [sub_pos.mpr hh0]
  simp only [wε]
  rw [div_lt_div_iff₀ hdb hda]
  nlinarith [mul_pos (mul_pos hπ0 (sub_pos.mpr hπ1)) (sub_pos.mpr hlt)]

theorem main (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (hh0 : h0 p q < 1) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) :
    (0 < D p q π ε ∧
      ∀ w, MSE p q π ε w - MSE p q π ε (wε p q π ε) = (w - wε p q π ε) ^ 2 * D p q π ε) ∧
    ((∑ l, ∑ o, ∑ b, W p q π ε (false, l, o, b) * x (false, l, o, b) = (1 - π) * h p q ε) ∧
      (∑ l, ∑ o, ∑ b, W p q π ε (false, l, o, b) = 1 - π) ∧
      (∑ l, ∑ o, ∑ b, W p q π ε (false, l, o, b) * x (false, l, o, b)) /
          (∑ l, ∑ o, ∑ b, W p q π ε (false, l, o, b)) = h p q ε ∧
      h p q ε - h0 p q = ε * (1 - h0 p q) ∧ ε * (1 - h0 p q) ≤ ε) ∧
    (wε p q (1 / 2) ε = (1 - ε) * (1 - h0 p q) ∧
      MSE p q (1 / 2) ε (wε p q (1 / 2) ε) = h p q ε * (2 - h p q ε) / 4) ∧
    (wε p q π 1 = 0 ∧
      wε p q π 0 = π * (1 - h0 p q) / (π + h0 p q - 2 * π * h0 p q) ∧
      0 < π * (1 - h0 p q) / (π + h0 p q - 2 * π * h0 p q)) ∧
    StrictAntiOn (fun ε => wε p q π ε) (Set.Icc 0 1) :=
  ⟨part_i p q hp hq hp1 hq1 hh0 ε hε0 hε1 π hπ0 hπ1, part_ii p q hp hq hp1 hq1 ε hε0 π hπ1,
    part_iii p q hp1 hq1 ε, part_iv p q hp hq hh0 π hπ0 hπ1, part_v p q hp hq hh0 π hπ0 hπ1⟩

end

end Bridge7A
