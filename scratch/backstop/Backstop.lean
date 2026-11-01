import Mathlib

/-!
# Evolution as a backstop for learning (after Gwern, "Evolution as Backstop for Reinforcement Learning")

Two nested loops. The inner loop is fast and optimizes a proxy reward. The outer loop is slow and selects on a
ground-truth fitness it cannot be argued with (death, bankruptcy, losing the match).

PROVED:
* `optimal_shift_invariant`, `optimal_scale_invariant`: adding a constant to every reward, or multiplying all rewards
  by a positive number, leaves the set of optimal actions unchanged. `bias_changes_optimum`: an action-dependent bias
  can move the optimum, which is what reward hacking exploits.
* `goodhart_bound`, `goodhart_tight`: if the proxy is within `ε` of the true reward everywhere, the proxy-optimal action
  loses at most `2ε` of true reward, and `2ε` can be lost.
* `backstop_step`: one generation in which inner learning raises everyone's hack trait by `η` and then the outer loop
  selects on true fitness `a - c·h`, changes the mean hack by exactly `η - c·Var(h)/w̄` (the Price equation).
  `backstop_iff`: the mean hack falls if and only if `η·w̄ < c·Var(h)`; selection must outpace hacking.
  `no_variation_no_backstop`: with no variation in the trait, the outer loop corrects nothing and the hack rises by
  `η` every generation.
* `outer_wins`: if a non-hacking type has strictly higher true fitness, its frequency ratio over the hacker grows like
  `(w₁/w₂)^k` and tends to infinity: the ground truth eventually wins.
* `outcome_entropy_le`: an outcome with `n` possible values carries at most `log n` nats, so a generation that only
  reports survival or death teaches the outer loop at most `log 2` per individual. That is why it is slow.
INTERPRETED (not formalized): the identification of the loops with evolution and brains, markets and firms, or
population training and agents.
-/

namespace Backstop
open Finset Real Filter

variable {A : Type*}

def IsOptimal (r : A → ℝ) (a : A) : Prop := ∀ b, r b ≤ r a

theorem optimal_shift_invariant (r : A → ℝ) (k : ℝ) (a : A) : IsOptimal (fun x => r x + k) a ↔ IsOptimal r a := by
  simp [IsOptimal]

theorem optimal_scale_invariant (r : A → ℝ) (k : ℝ) (hk : 0 < k) (a : A) :
    IsOptimal (fun x => k * r x) a ↔ IsOptimal r a := by
  simp only [IsOptimal]
  exact forall_congr' (fun b => mul_le_mul_iff_of_pos_left hk)

theorem bias_changes_optimum :
    IsOptimal (fun b : Bool => if b then (1 : ℝ) else 0) true ∧
    ¬ IsOptimal (fun b : Bool => (if b then (1 : ℝ) else 0) + (if b then 0 else 2)) true := by
  refine ⟨fun b => by cases b <;> norm_num, fun h => ?_⟩
  have := h false; norm_num at this

theorem goodhart_bound (r p : A → ℝ) (ε : ℝ) (hclose : ∀ x, |p x - r x| ≤ ε) (a b : A)
    (hpa : IsOptimal p a) : r b - r a ≤ 2 * ε := by
  have h1 := hclose a; have h2 := hclose b; have h3 := hpa b
  rw [abs_le] at h1 h2; linarith

theorem goodhart_tight (ε : ℝ) (hε : 0 ≤ ε) :
    let r : Bool → ℝ := fun b => if b then 2 * ε else 0
    let p : Bool → ℝ := fun b => if b then ε else ε
    (∀ x, |p x - r x| ≤ ε) ∧ IsOptimal p false ∧ r true - r false = 2 * ε := by
  intro r p
  refine ⟨fun x => ?_, fun b => ?_, ?_⟩
  · cases x <;> simp [r, p, abs_of_nonneg hε] <;> rw [show ε - 2 * ε = -ε by ring, abs_neg, abs_of_nonneg hε]
  · cases b <;> simp [p]
  · simp [r]

/-! One generation: inner learning, then outer selection. -/

variable {ι : Type*} [Fintype ι]

noncomputable def mean (q h : ι → ℝ) : ℝ := ∑ i, q i * h i
noncomputable def var (q h : ι → ℝ) : ℝ := ∑ i, q i * (h i - mean q h) ^ 2

theorem backstop_step (q h : ι → ℝ) (a c η : ℝ) (hq : ∑ i, q i = 1)
    (hw : (∑ i, q i * (a - c * (h i + η))) ≠ 0) :
    (∑ i, q i * (a - c * (h i + η)) * (h i + η)) / (∑ i, q i * (a - c * (h i + η))) - mean q h
      = η - c * var q h / (∑ i, q i * (a - c * (h i + η))) := by
  set m := mean q h
  have hm : ∑ i, q i * h i = m := rfl
  have hW : ∑ i, q i * (a - c * (h i + η)) = a - c * (m + η) := by
    have : ∀ i, q i * (a - c * (h i + η)) = a * q i - c * (q i * h i) - c * η * q i := fun i => by ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hq, hm]; ring
  have hV : var q h = ∑ i, q i * h i ^ 2 - m ^ 2 := by
    unfold var
    have : ∑ i, q i * (h i - m) ^ 2 = ∑ i, q i * h i ^ 2 - 2 * m * ∑ i, q i * h i + m ^ 2 * ∑ i, q i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this, hm, hq]; ring
  have hN : ∑ i, q i * (a - c * (h i + η)) * (h i + η)
      = a * (m + η) - c * (∑ i, q i * h i ^ 2 + 2 * η * m + η ^ 2) := by
    have : ∀ i, q i * (a - c * (h i + η)) * (h i + η)
        = a * (q i * h i) + a * η * q i - c * (q i * h i ^ 2) - 2 * c * η * (q i * h i) - c * η ^ 2 * q i := by
      intro i; ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hm, hq]
    ring
  rw [hW] at hw ⊢
  rw [hN, hV]
  generalize hWd : a - c * (m + η) = W at hw ⊢
  have ha : a = W + c * (m + η) := by linarith
  subst ha
  field_simp
  ring

theorem backstop_iff (q h : ι → ℝ) (a c η : ℝ) (hq : ∑ i, q i = 1)
    (hw : 0 < ∑ i, q i * (a - c * (h i + η))) :
    (∑ i, q i * (a - c * (h i + η)) * (h i + η)) / (∑ i, q i * (a - c * (h i + η))) < mean q h
      ↔ η * (∑ i, q i * (a - c * (h i + η))) < c * var q h := by
  have hs := backstop_step q h a c η hq hw.ne'
  rw [← sub_neg, hs, sub_neg, lt_div_iff₀ hw]

theorem no_variation_no_backstop (q h : ι → ℝ) (a c η : ℝ) (hq : ∑ i, q i = 1)
    (hw : (∑ i, q i * (a - c * (h i + η))) ≠ 0) (hv : var q h = 0) :
    (∑ i, q i * (a - c * (h i + η)) * (h i + η)) / (∑ i, q i * (a - c * (h i + η))) = mean q h + η := by
  have := backstop_step q h a c η hq hw
  rw [hv, mul_zero, zero_div, sub_zero] at this; linarith

/-! The ground truth wins in the long run. -/

theorem outer_wins (q₁ q₂ w₁ w₂ : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hw₂ : 0 < w₂) (hlt : w₂ < w₁) :
    Tendsto (fun k : ℕ => (q₁ * w₁ ^ k) / (q₂ * w₂ ^ k)) atTop atTop := by
  have hr : 1 < w₁ / w₂ := (one_lt_div hw₂).mpr hlt
  have hpow : Tendsto (fun k : ℕ => (w₁ / w₂) ^ k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hr
  have : (fun k : ℕ => (q₁ * w₁ ^ k) / (q₂ * w₂ ^ k)) = fun k => (q₁ / q₂) * (w₁ / w₂) ^ k := by
    funext k; rw [div_pow]; field_simp
  rw [this]; exact hpow.const_mul_atTop (div_pos hq₁ hq₂)

/-! The outer loop's information budget. -/

theorem outcome_entropy_le {Y : Type*} [Fintype Y] [Nonempty Y] (p : Y → ℝ) (hp : ∀ y, 0 < p y)
    (h1 : ∑ y, p y = 1) : -(∑ y, p y * log (p y)) ≤ log (Fintype.card Y) := by
  set n : ℝ := (Fintype.card Y : ℝ) with hn_def
  have hn : 0 < n := by rw [hn_def]; exact_mod_cast Fintype.card_pos
  have key : ∑ y, p y * log (1 / (n * p y)) ≤ 0 := by
    have : ∀ y, p y * log (1 / (n * p y)) ≤ p y * (1 / (n * p y) - 1) := fun y =>
      mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (by have := hp y; positivity)) (hp y).le
    calc ∑ y, p y * log (1 / (n * p y)) ≤ ∑ y, p y * (1 / (n * p y) - 1) := Finset.sum_le_sum (fun y _ => this y)
      _ = ∑ y, (1 / n - p y) := Finset.sum_congr rfl (fun y _ => by have := (hp y).ne'; field_simp)
      _ = 0 := by
        rw [Finset.sum_sub_distrib, h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def]
        field_simp; ring
  have expand : ∀ y, p y * log (1 / (n * p y)) = -(p y * log n) - p y * log (p y) := fun y => by
    rw [one_div, log_inv, log_mul hn.ne' (hp y).ne']; ring
  simp only [expand, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul, h1, one_mul] at key
  linarith

end Backstop
