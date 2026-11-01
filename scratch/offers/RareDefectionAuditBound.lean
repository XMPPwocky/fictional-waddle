import Mathlib

/-!
# Rare defection evades sampling audits

PROVED:
* `weight_total` : the product Bernoulli(q) weights on `Fin k → Bool` sum to 1.
* `prob_caught_eq` : in the finite product space `Fin k → Bool` with product Bernoulli(q)
  weights, the probability of the event "some coordinate is a defection (`true`)" equals
  `pCaught q k = 1 - (1 - q)^k` (computed via the complement event "all comply").
* `pCaught_le` : for `q ∈ [0,1]`, `pCaught q k ≤ k * q` (Bernoulli's inequality).
* `pCaught_lt_of` : for `q ∈ [0,1]`, if `k * q < p` then `pCaught q k < p`.
* `exists_q_evades` : for every `k` and every `p ∈ (0,1]` there is `q ∈ (0,1)` with
  `pCaught q k < p`.
* `pCaught_ge` : for `q ∈ [0,1]`, `1 - exp (-(k * q)) ≤ pCaught q k`, so on the order of
  `1/q` samples do suffice to catch defection with constant probability.
* `argmax_eq_comply` : for the two-action policy with `π defect = q`, `π comply = 1 - q`,
  `q < 1/2`, every argmax action equals `comply` (and `comply` is an argmax).
* `argmax_monitor_detects_zero` : for any temperature-0 decoder (a map returning an argmax
  action), a monitor that flags only when the decoded action is `defect` has detection
  probability 0, even though the policy defects with probability `q` (which may be positive).

INTERPRETED (not formalized):
* "Temperature-0" is modelled as an arbitrary decoder whose output is an argmax of the
  policy; no softmax temperature limit is formalized.
* The product measure is formalized as the explicit finite product weight on `Fin k → Bool`,
  not via `MeasureTheory.Measure.pi`.
-/

namespace RareDefectionAuditBound

open Finset

/-- Probability that at least one of `k` independent Bernoulli(q) samples is a defection. -/
noncomputable def pCaught (q : ℝ) (k : ℕ) : ℝ := 1 - (1 - q) ^ k

/-- Product Bernoulli(q) weight of an outcome `f : Fin k → Bool` (`true` = defection). -/
def weight (q : ℝ) {k : ℕ} (f : Fin k → Bool) : ℝ :=
  ∏ i, if f i then q else 1 - q

theorem weight_total (q : ℝ) (k : ℕ) : ∑ f : Fin k → Bool, weight q f = 1 := by
  unfold weight
  rw [← Fintype.prod_sum (fun (_ : Fin k) (b : Bool) => if b then q else 1 - q)]
  simp

theorem prob_caught_eq (q : ℝ) (k : ℕ) :
    ∑ f ∈ univ.filter (fun f : Fin k → Bool => ∃ i, f i = true), weight q f = pCaught q k := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Fin k → Bool))
    (fun f => ∃ i, f i = true) (weight q)
  rw [weight_total] at hsplit
  have hnot : univ.filter (fun f : Fin k → Bool => ¬ ∃ i, f i = true) = {fun _ => false} := by
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_singleton, not_exists, Bool.not_eq_true]
    constructor
    · intro h; funext i; exact h i
    · intro h i; rw [h]
  rw [hnot, sum_singleton] at hsplit
  have hw : weight q (fun _ : Fin k => false) = (1 - q) ^ k := by
    simp [weight]
  rw [hw] at hsplit
  unfold pCaught
  linarith

theorem pCaught_le (q : ℝ) (k : ℕ) (_hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    pCaught q k ≤ k * q := by
  have h := one_add_mul_le_pow (a := -q) (by linarith) k
  unfold pCaught
  have : (1 + -q) = 1 - q := by ring
  rw [this] at h
  linarith

theorem pCaught_lt_of (q p : ℝ) (k : ℕ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h : k * q < p) :
    pCaught q k < p :=
  lt_of_le_of_lt (pCaught_le q k hq0 hq1) h

theorem exists_q_evades (k : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ pCaught q k < p := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  refine ⟨p / (2 * (k + 1)), by positivity, ?_, ?_⟩
  · rw [div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  · have hq0 : 0 ≤ p / (2 * (k + 1)) := by positivity
    have hq1 : p / (2 * (k + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    apply pCaught_lt_of _ _ _ hq0 hq1
    have : (k : ℝ) * (p / (2 * (k + 1))) = p * (k / (2 * (k + 1))) := by
      field_simp
    rw [this]
    have hfrac : (k : ℝ) / (2 * (k + 1)) < 1 := by
      rw [div_lt_one (by positivity)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    nlinarith

theorem pCaught_ge (q : ℝ) (k : ℕ) (_hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    1 - Real.exp (-(k * q)) ≤ pCaught q k := by
  unfold pCaught
  have h1 : 1 - q ≤ Real.exp (-q) := by
    have := Real.add_one_le_exp (-q)
    linarith
  have h2 : (1 - q) ^ k ≤ Real.exp (-q) ^ k :=
    pow_le_pow_left₀ (by linarith) h1 k
  have h3 : Real.exp (-q) ^ k = Real.exp (-(k * q)) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  linarith

/-- The two actions of the policy. -/
inductive Action
  | defect
  | comply
  deriving DecidableEq

/-- Two-action policy with defect probability `q`. -/
def policy (q : ℝ) : Action → ℝ
  | .defect => q
  | .comply => 1 - q

/-- `a` is an argmax action of the distribution `π`. -/
def IsArgmax (π : Action → ℝ) (a : Action) : Prop := ∀ b, π b ≤ π a

theorem argmax_eq_comply (q : ℝ) (hq : q < 1 / 2) :
    IsArgmax (policy q) .comply ∧ ∀ a, IsArgmax (policy q) a → a = .comply := by
  refine ⟨?_, ?_⟩
  · intro b
    cases b
    · simp only [policy]; linarith
    · exact le_rfl
  · intro a ha
    cases a with
    | comply => rfl
    | defect =>
      exfalso
      have := ha .comply
      simp [policy] at this
      linarith

/-- Detection probability of a monitor that sees only the decoded action and flags `defect`. -/
def argmaxDetection (dec : (Action → ℝ) → Action) (π : Action → ℝ) : ℝ :=
  if dec π = .defect then 1 else 0

theorem argmax_monitor_detects_zero (q : ℝ) (hq : q < 1 / 2)
    (dec : (Action → ℝ) → Action) (hdec : ∀ π, IsArgmax π (dec π)) :
    dec (policy q) = .comply ∧ argmaxDetection dec (policy q) = 0 := by
  have h := (argmax_eq_comply q hq).2 _ (hdec (policy q))
  refine ⟨h, ?_⟩
  simp [argmaxDetection, h]

end RareDefectionAuditBound
