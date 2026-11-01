import Mathlib

/-!
# Postselection ledger: `log (1 / s) = I_Q(S;A) + KL(Q_S ‖ p) + KL(Q_A ‖ q)`

Setting: finite types `α`, `β`; weights `p : α → ℝ≥0`, `q : β → ℝ≥0` with `∑ p = ∑ q = 1`;
the product law `P (a, b) = p a * q b`; an event `C : Finset (α × β)` with
`s = ∑_{x ∈ C} P x > 0`; the postselected law `Q = P(· | C)`, i.e. `Q x = P x / s` on `C`
and `0` off `C`; its marginals `Q_S a = ∑ b, Q (a, b)` and `Q_A b = ∑ a, Q (a, b)`.
`KL(f ‖ g) = ∑ x, f x * log (f x / g x)` (natural log; `0 * log 0 = 0`), and
`I_Q(S;A) = KL(Q ‖ Q_S ⊗ Q_A)`.

PROVED
* `ledger` (i): `I_Q + KL(Q_S ‖ p) + KL(Q_A ‖ q) = log (1 / s)`, for `s > 0`.
  (`ledger` does not use `∑ p = ∑ q = 1`; the remaining statements do.)
* `kl_QS_nonneg`, `kl_QA_nonneg`, `mutualInfo_nonneg`: the three terms are `≥ 0`.
* `mutualInfo_le_log` : `I_Q ≤ log (1 / s)`.
* `ledger_eq_iff` (iii): `I_Q = log (1 / s) ↔ Q_S = p ∧ Q_A = q`.
* `gibbs`, `gibbs_eq_iff`: `∑ f - ∑ g ≤ KL(f ‖ g)` for nonnegative `f`, `g` with
  `g x = 0 → f x = 0`, with equality iff `f = g`.
* `Q_cond` : `Q x` is the conditional probability `Pmeas[{x} | C]` of the product measure
  `Pmeas = ∑ x, P x • dirac x`; `Pmeas_finset` : `Pmeas C = s`.
* `expected_cost` (ii): for runs `X k : Ω → α × β` that are measurable, have law `Pmeas`,
  and are mutually independent (`iIndepFun`), restarting until a run lands in `C`, with every
  performed run costing `τ`, the expected total cost equals `τ / s`, which equals
  `τ * exp (I_Q + KL(Q_S ‖ p) + KL(Q_A ‖ q))`, which is `≥ τ * exp I_Q`.
* `expected_cost_eq_iff` (iii, cost form): for `0 < τ < ⊤`,
  `τ * exp I_Q = τ / s ↔ Q_S = p ∧ Q_A = q`.
* `colliderA` : uniform `p = q` on `Fin k` (`k > 0`), `C` = diagonal: `∑ p = 1`, `s = 1 / k`,
  `Q_S = p`, `Q_A = q`, `I_Q = log k = log (1 / s)`.
* `xorB` : fair independent bits on `Bool`, `C = {x | xor x.1 x.2 = false}` (which equals
  `{x | x.1 = x.2}`, `xorC_eq_diag`): `∑ p = 1`, `s = 1 / 2`, `Q_S = p`, `Q_A = q`,
  `I_Q = log 2 = log (1 / s)`.

INTERPRETED
* `RestartBound.lintegral_totalCost_eq` lives in `scratch/coloring/RestartBound.lean`, which is
  not an importable module; its definitions (`allFail`, `numRuns`, `totalCost`) and the
  lemmas used here are reproduced verbatim in the section `Bridge2A.RestartBound` below.
* The real-valued `KL` uses `Real.log 0 = 0`. Off absolute continuity this would not be the
  usual (infinite) KL; every KL used here is between absolutely continuous laws
  (`QS_eq_zero_of`, `QA_eq_zero_of`, `Q_eq_zero_of_prod`), so it is the usual KL.
* "Q := P(·|C)" is the explicit formula `Q`; `Q_cond` identifies it with
  `ProbabilityTheory.cond` of the product measure.
* "Equality holds" in (iii) is read as `I_Q = log (1 / s)`, equivalently
  `τ / s = τ * exp I_Q` for `0 < τ < ⊤`.
* PostselectionColliderA and XorColliderB are instantiated in this file's framework (uniform
  weights, diagonal / xor event) rather than imported, since those files are also scratch files.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Bridge2A

/-! ## Restart cost (reproduced from `scratch/coloring/RestartBound.lean`) -/

namespace RestartBound

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The event that runs `0, …, k-1` all fail, i.e. run `k` is performed. -/
def allFail (A : ℕ → Set Ω) (k : ℕ) : Set Ω := ⋂ i ∈ range k, (A i)ᶜ

/-- Number of runs performed. -/
noncomputable def numRuns (A : ℕ → Set Ω) (ω : Ω) : ℝ≥0∞ :=
  ∑' k, (allFail A k).indicator (fun _ => (1 : ℝ≥0∞)) ω

/-- Total cost: run `k` contributes `cost k ω` when it is performed. -/
noncomputable def totalCost (A : ℕ → Set Ω) (cost : ℕ → Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ∑' k, (allFail A k).indicator (cost k) ω

lemma measurableSet_allFail {A : ℕ → Set Ω} (hA : ∀ i, MeasurableSet (A i)) (k : ℕ) :
    MeasurableSet (allFail A k) :=
  Finset.measurableSet_biInter _ (fun i _ => (hA i).compl)

theorem measure_allFail {μ : Measure Ω} {A : ℕ → Set Ω} {s : ℝ≥0∞}
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ) (hs : ∀ i, μ (A i) = s) (k : ℕ) :
    μ (allFail A k) = (1 - s) ^ k := by
  have := hind.isProbabilityMeasure
  have h := (iIndepSet_iff A μ).1 hind (range k) (f := fun i => (A i)ᶜ)
    (fun i _ => (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)).compl)
  rw [allFail, h]
  simp [prob_compl_eq_one_sub (hA _), hs]

theorem lintegral_numRuns {μ : Measure Ω} {A : ℕ → Set Ω} {s : ℝ≥0∞}
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ) (hs : ∀ i, μ (A i) = s)
    (hs1 : s ≤ 1) :
    ∫⁻ ω, numRuns A ω ∂μ = s⁻¹ := by
  unfold numRuns
  rw [lintegral_tsum (fun k =>
    (measurable_const.indicator (measurableSet_allFail hA k)).aemeasurable)]
  simp_rw [lintegral_indicator_const (measurableSet_allFail hA _), one_mul,
    measure_allFail hA hind hs]
  rw [ENNReal.tsum_geometric, ENNReal.sub_sub_cancel ENNReal.one_ne_top hs1]

lemma measurable_numRuns {A : ℕ → Set Ω} (hA : ∀ i, MeasurableSet (A i)) :
    Measurable (numRuns A) :=
  Measurable.tsum (fun k => measurable_const.indicator (measurableSet_allFail hA k))

theorem lintegral_totalCost_eq {μ : Measure Ω} {A : ℕ → Set Ω} {s τ : ℝ≥0∞}
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ) (hs : ∀ i, μ (A i) = s)
    (hs1 : s ≤ 1) :
    ∫⁻ ω, totalCost A (fun _ _ => τ) ω ∂μ = τ / s := by
  have hpt : ∀ ω, totalCost A (fun _ _ => τ) ω = τ * numRuns A ω := by
    intro ω
    unfold totalCost numRuns
    rw [← ENNReal.tsum_mul_left]
    congr 1
    ext k
    by_cases hk : ω ∈ allFail A k
    · simp [Set.indicator_of_mem hk]
    · simp [Set.indicator_of_notMem hk]
  simp_rw [hpt]
  rw [lintegral_const_mul _ (measurable_numRuns hA), lintegral_numRuns hA hind hs hs1,
    div_eq_mul_inv]

end RestartBound

/-! ## Discrete KL divergence and Gibbs' inequality -/

/-- Discrete KL divergence with natural log (`Real.log 0 = 0`, so `0 * log 0 = 0`). -/
noncomputable def kl {γ : Type*} [Fintype γ] (f g : γ → ℝ) : ℝ :=
  ∑ x, f x * Real.log (f x / g x)

lemma gibbs_term {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0) :
    a - b ≤ a * Real.log (a / b) ∧ (a * Real.log (a / b) = a - b → a = b) := by
  rcases ha.eq_or_lt with h | h
  · rw [← h]
    constructor
    · rw [zero_mul]; linarith
    · intro h'; rw [zero_mul] at h'; linarith
  · have hb0 : b ≠ 0 := fun h0 => h.ne' (hab h0)
    have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hba : a * (b / a) = b := by field_simp
    have key : a * Real.log (a / b) - (a - b) = a * (b / a - 1 - Real.log (b / a)) := by
      rw [Real.log_div h.ne' hb0, Real.log_div hb0 h.ne']
      linear_combination -hba
    constructor
    · have h1 := Real.log_le_sub_one_of_pos (div_pos hb' h)
      have h2 : 0 ≤ a * (b / a - 1 - Real.log (b / a)) := mul_nonneg h.le (by linarith)
      linarith
    · intro heq
      by_contra hne
      have hne' : b / a ≠ 1 := fun h1 => hne ((div_eq_one_iff_eq h.ne').1 h1).symm
      have h1 := Real.log_lt_sub_one_of_pos (div_pos hb' h) hne'
      have h2 : 0 < a * (b / a - 1 - Real.log (b / a)) := mul_pos h (by linarith)
      linarith

theorem gibbs {γ : Type*} [Fintype γ] (f g : γ → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfg : ∀ x, g x = 0 → f x = 0) :
    ∑ x, f x - ∑ x, g x ≤ kl f g := by
  rw [← sum_sub_distrib]
  exact sum_le_sum (fun x _ => (gibbs_term (hf x) (hg x) (hfg x)).1)

lemma kl_self {γ : Type*} [Fintype γ] (f : γ → ℝ) : kl f f = 0 := by
  unfold kl
  refine sum_eq_zero (fun x _ => ?_)
  rcases eq_or_ne (f x) 0 with h | h
  · simp [h]
  · simp [div_self h]

theorem gibbs_eq_iff {γ : Type*} [Fintype γ] (f g : γ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 ≤ g x) (hfg : ∀ x, g x = 0 → f x = 0) :
    kl f g = ∑ x, f x - ∑ x, g x ↔ f = g := by
  constructor
  · intro h
    have h0 : ∑ x, (f x * Real.log (f x / g x) - (f x - g x)) = 0 := by
      unfold kl at h
      rw [sum_sub_distrib, h, sum_sub_distrib, sub_self]
    rw [sum_eq_zero_iff_of_nonneg
      (fun x _ => sub_nonneg.2 (gibbs_term (hf x) (hg x) (hfg x)).1)] at h0
    funext x
    exact (gibbs_term (hf x) (hg x) (hfg x)).2 (by linarith [h0 x (mem_univ x)])
  · rintro rfl
    rw [sub_self, kl_self]

lemma kl_nonneg_of_sum_eq {γ : Type*} [Fintype γ] (f g : γ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 ≤ g x) (hfg : ∀ x, g x = 0 → f x = 0) (hsum : ∑ x, f x = ∑ x, g x) :
    0 ≤ kl f g := by
  have := gibbs f g hf hg hfg
  linarith

lemma kl_eq_zero_iff_of_sum_eq {γ : Type*} [Fintype γ] (f g : γ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 ≤ g x) (hfg : ∀ x, g x = 0 → f x = 0) (hsum : ∑ x, f x = ∑ x, g x) :
    kl f g = 0 ↔ f = g := by
  rw [← gibbs_eq_iff f g hf hg hfg, hsum, sub_self]

/-! ## The postselected law -/

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Product law `P (a, b) = p a * q b`. -/
noncomputable def P (p : α → ℝ≥0) (q : β → ℝ≥0) (x : α × β) : ℝ := p x.1 * q x.2

/-- Success probability `s = ∑_{x ∈ C} P x`. -/
noncomputable def succProb (p : α → ℝ≥0) (q : β → ℝ≥0) (C : Finset (α × β)) : ℝ :=
  ∑ x ∈ C, P p q x

/-- Postselected law `Q = P(· | C)`. -/
noncomputable def Q (p : α → ℝ≥0) (q : β → ℝ≥0) (C : Finset (α × β)) (x : α × β) : ℝ :=
  if x ∈ C then P p q x / succProb p q C else 0

/-- First marginal of `Q`. -/
noncomputable def QS (p : α → ℝ≥0) (q : β → ℝ≥0) (C : Finset (α × β)) (a : α) : ℝ :=
  ∑ b, Q p q C (a, b)

/-- Second marginal of `Q`. -/
noncomputable def QA (p : α → ℝ≥0) (q : β → ℝ≥0) (C : Finset (α × β)) (b : β) : ℝ :=
  ∑ a, Q p q C (a, b)

/-- Mutual information `I_Q(S;A) = KL(Q ‖ Q_S ⊗ Q_A)`. -/
noncomputable def mutualInfo (p : α → ℝ≥0) (q : β → ℝ≥0) (C : Finset (α × β)) : ℝ :=
  kl (Q p q C) (fun x => QS p q C x.1 * QA p q C x.2)

variable (p : α → ℝ≥0) (q : β → ℝ≥0) (C : Finset (α × β))

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
lemma P_nonneg (x : α × β) : 0 ≤ P p q x := by unfold P; positivity

omit [Fintype α] [Fintype β] in
lemma Q_nonneg (hs : 0 < succProb p q C) (x : α × β) : 0 ≤ Q p q C x := by
  unfold Q
  split_ifs
  · exact div_nonneg (P_nonneg p q x) hs.le
  · exact le_rfl

lemma sum_Q (hs : 0 < succProb p q C) : ∑ x, Q p q C x = 1 := by
  unfold Q
  rw [sum_ite_mem, univ_inter, ← sum_div]
  exact div_self hs.ne'

lemma sum_QS (hs : 0 < succProb p q C) : ∑ a, QS p q C a = 1 := by
  rw [← sum_Q p q C hs, Fintype.sum_prod_type]
  rfl

lemma sum_QA (hs : 0 < succProb p q C) : ∑ b, QA p q C b = 1 := by
  rw [← sum_Q p q C hs, Fintype.sum_prod_type_right]
  rfl

omit [Fintype α] in
lemma QS_nonneg (hs : 0 < succProb p q C) (a : α) : 0 ≤ QS p q C a :=
  sum_nonneg (fun b _ => Q_nonneg p q C hs (a, b))

omit [Fintype β] in
lemma QA_nonneg (hs : 0 < succProb p q C) (b : β) : 0 ≤ QA p q C b :=
  sum_nonneg (fun a _ => Q_nonneg p q C hs (a, b))

omit [Fintype α] in
lemma Q_le_QS (hs : 0 < succProb p q C) (x : α × β) : Q p q C x ≤ QS p q C x.1 :=
  single_le_sum (f := fun b => Q p q C (x.1, b)) (fun _ _ => Q_nonneg p q C hs _) (mem_univ x.2)

omit [Fintype β] in
lemma Q_le_QA (hs : 0 < succProb p q C) (x : α × β) : Q p q C x ≤ QA p q C x.2 :=
  single_le_sum (f := fun a => Q p q C (a, x.2)) (fun _ _ => Q_nonneg p q C hs _) (mem_univ x.1)

omit [Fintype α] in
lemma QS_eq_zero_of (a : α) (h : (p a : ℝ) = 0) : QS p q C a = 0 :=
  sum_eq_zero (fun b _ => by simp [Q, P, h])

omit [Fintype β] in
lemma QA_eq_zero_of (b : β) (h : (q b : ℝ) = 0) : QA p q C b = 0 :=
  sum_eq_zero (fun a _ => by simp [Q, P, h])

lemma Q_eq_zero_of_prod (hs : 0 < succProb p q C) (x : α × β)
    (h : QS p q C x.1 * QA p q C x.2 = 0) : Q p q C x = 0 := by
  rcases mul_eq_zero.1 h with h1 | h1
  · exact le_antisymm (h1 ▸ Q_le_QS p q C hs x) (Q_nonneg p q C hs x)
  · exact le_antisymm (h1 ▸ Q_le_QA p q C hs x) (Q_nonneg p q C hs x)

lemma sum_QS_mul (L : α → ℝ) : ∑ a, QS p q C a * L a = ∑ x, Q p q C x * L x.1 := by
  simp only [QS, sum_mul]
  rw [Fintype.sum_prod_type]

lemma sum_QA_mul (L : β → ℝ) : ∑ b, QA p q C b * L b = ∑ x, Q p q C x * L x.2 := by
  simp only [QA, sum_mul]
  rw [Fintype.sum_prod_type_right]

/-- (i) The postselection ledger. -/
theorem ledger (hs : 0 < succProb p q C) :
    mutualInfo p q C + kl (QS p q C) (fun a => (p a : ℝ)) + kl (QA p q C) (fun b => (q b : ℝ))
      = Real.log (1 / succProb p q C) := by
  have h2 := sum_QS_mul p q C (fun a => Real.log (QS p q C a / p a))
  have h3 := sum_QA_mul p q C (fun b => Real.log (QA p q C b / q b))
  simp only [mutualInfo, kl] at h2 h3 ⊢
  rw [h2, h3, ← sum_add_distrib, ← sum_add_distrib,
    show Real.log (1 / succProb p q C) = ∑ x, Q p q C x * Real.log (1 / succProb p q C) by
      rw [← sum_mul, sum_Q p q C hs, one_mul]]
  refine sum_congr rfl (fun x _ => ?_)
  rcases (Q_nonneg p q C hs x).eq_or_lt with h | h
  · rw [← h]; ring
  · have hxC : x ∈ C := by
      by_contra hc
      simp [Q, hc] at h
    have hQx : Q p q C x = P p q x / succProb p q C := by simp [Q, hxC]
    have hp0 : (p x.1 : ℝ) ≠ 0 := fun h0 => by simp [hQx, P, h0] at h
    have hq0 : (q x.2 : ℝ) ≠ 0 := fun h0 => by simp [hQx, P, h0] at h
    have hS0 : QS p q C x.1 ≠ 0 := (lt_of_lt_of_le h (Q_le_QS p q C hs x)).ne'
    have hA0 : QA p q C x.2 ≠ 0 := (lt_of_lt_of_le h (Q_le_QA p q C hs x)).ne'
    rw [← mul_add, ← mul_add]
    congr 1
    rw [Real.log_div h.ne' (mul_ne_zero hS0 hA0), Real.log_mul hS0 hA0, Real.log_div hS0 hp0,
      Real.log_div hA0 hq0, hQx, P, Real.log_div (mul_ne_zero hp0 hq0) hs.ne',
      Real.log_mul hp0 hq0, one_div, Real.log_inv]
    ring

omit [Fintype β] [DecidableEq α] [DecidableEq β] in
lemma sum_p_real (hp : ∑ a, p a = 1) : ∑ a, (p a : ℝ) = 1 := by
  rw [← NNReal.coe_sum, hp, NNReal.coe_one]

omit [Fintype α] [DecidableEq α] [DecidableEq β] in
lemma sum_q_real (hq : ∑ b, q b = 1) : ∑ b, (q b : ℝ) = 1 := by
  rw [← NNReal.coe_sum, hq, NNReal.coe_one]

theorem kl_QS_nonneg (hp : ∑ a, p a = 1) (hs : 0 < succProb p q C) :
    0 ≤ kl (QS p q C) (fun a => (p a : ℝ)) :=
  kl_nonneg_of_sum_eq _ _ (QS_nonneg p q C hs) (fun a => (p a).coe_nonneg) (QS_eq_zero_of p q C)
    (by rw [sum_QS p q C hs]; exact (sum_p_real p hp).symm)

theorem kl_QA_nonneg (hq : ∑ b, q b = 1) (hs : 0 < succProb p q C) :
    0 ≤ kl (QA p q C) (fun b => (q b : ℝ)) :=
  kl_nonneg_of_sum_eq _ _ (QA_nonneg p q C hs) (fun b => (q b).coe_nonneg) (QA_eq_zero_of p q C)
    (by rw [sum_QA p q C hs]; exact (sum_q_real q hq).symm)

theorem mutualInfo_nonneg (hs : 0 < succProb p q C) : 0 ≤ mutualInfo p q C := by
  refine kl_nonneg_of_sum_eq _ _ (Q_nonneg p q C hs)
    (fun x => mul_nonneg (QS_nonneg p q C hs x.1) (QA_nonneg p q C hs x.2))
    (Q_eq_zero_of_prod p q C hs) ?_
  rw [sum_Q p q C hs, Fintype.sum_prod_type]
  simp_rw [← mul_sum]
  rw [← sum_mul, sum_QS p q C hs, sum_QA p q C hs, one_mul]

theorem mutualInfo_le_log (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1) (hs : 0 < succProb p q C) :
    mutualInfo p q C ≤ Real.log (1 / succProb p q C) := by
  have := ledger p q C hs
  have := kl_QS_nonneg p q C hp hs
  have := kl_QA_nonneg p q C hq hs
  linarith

/-- (iii) Equality in `I_Q ≤ log (1 / s)` holds iff both marginals are undistorted. -/
theorem ledger_eq_iff (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1) (hs : 0 < succProb p q C) :
    mutualInfo p q C = Real.log (1 / succProb p q C) ↔
      QS p q C = (fun a => (p a : ℝ)) ∧ QA p q C = (fun b => (q b : ℝ)) := by
  have hL := ledger p q C hs
  have k1 := kl_QS_nonneg p q C hp hs
  have k2 := kl_QA_nonneg p q C hq hs
  have e1 := kl_eq_zero_iff_of_sum_eq (QS p q C) (fun a => (p a : ℝ)) (QS_nonneg p q C hs)
    (fun a => (p a).coe_nonneg)
    (QS_eq_zero_of p q C) (by rw [sum_QS p q C hs]; exact (sum_p_real p hp).symm)
  have e2 := kl_eq_zero_iff_of_sum_eq (QA p q C) (fun b => (q b : ℝ)) (QA_nonneg p q C hs)
    (fun b => (q b).coe_nonneg)
    (QA_eq_zero_of p q C) (by rw [sum_QA p q C hs]; exact (sum_q_real q hq).symm)
  constructor
  · intro h
    exact ⟨e1.1 (by linarith), e2.1 (by linarith)⟩
  · rintro ⟨h1, h2⟩
    have z1 := e1.2 h1
    have z2 := e2.2 h2
    linarith

/-! ## The product measure and conditioning -/

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β]

/-- The product law as a measure on `α × β`. -/
noncomputable def Pmeas : Measure (α × β) :=
  ∑ x : α × β, ((p x.1 * q x.2 : ℝ≥0) : ℝ≥0∞) • Measure.dirac x

lemma Pmeas_finset (D : Finset (α × β)) :
    Pmeas p q (D : Set (α × β)) = ENNReal.ofReal (succProb p q D) := by
  have h1 : succProb p q D = ((∑ x ∈ D, p x.1 * q x.2 : ℝ≥0) : ℝ) := by
    simp [succProb, P]
  rw [h1, ENNReal.ofReal_coe_nnreal, ENNReal.ofNNReal_finsetSum]
  simp [Pmeas, Measure.finsetSum_apply, Measure.dirac_apply, Set.indicator_apply]

theorem Q_cond (hs : 0 < succProb p q C) (x : α × β) :
    ENNReal.ofReal (Q p q C x) = (Pmeas p q)[{x} | (C : Set (α × β))] := by
  rw [cond_apply C.measurableSet, Pmeas_finset]
  by_cases hx : x ∈ C
  · have hi : (C : Set (α × β)) ∩ {x} = ((({x} : Finset (α × β))) : Set (α × β)) := by
      ext y; simp only [Set.mem_inter_iff, Finset.mem_coe, Set.mem_singleton_iff,
        Finset.coe_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨hx, rfl⟩
    rw [hi, Pmeas_finset]
    have h1 : succProb p q {x} = P p q x := sum_singleton _ _
    simp only [Q, hx, ite_true, h1]
    rw [ENNReal.ofReal_div_of_pos hs, div_eq_mul_inv, mul_comm]
  · have hi : (C : Set (α × β)) ∩ {x} = ∅ := by
      ext y; simp only [Set.mem_inter_iff, Finset.mem_coe, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro hy rfl; exact hx hy
    rw [hi, measure_empty, mul_zero]
    simp [Q, hx]

/-! ## (ii) Expected restart cost -/

/-- (ii) Restarting i.i.d. runs with law `P` until one lands in `C`, each run costing `τ`:
the expected total cost is `τ / s = τ * exp (I_Q + KL(Q_S ‖ p) + KL(Q_A ‖ q)) ≥ τ * exp I_Q`. -/
theorem expected_cost (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1) (hs : 0 < succProb p q C)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (X : ℕ → Ω → α × β)
    (hXm : ∀ k, Measurable (X k)) (hlaw : ∀ k, μ.map (X k) = Pmeas p q)
    (hind : iIndepFun X μ) (τ : ℝ≥0∞) :
    ∫⁻ ω, RestartBound.totalCost (fun k => X k ⁻¹' (C : Set (α × β))) (fun _ _ => τ) ω ∂μ
        = τ / ENNReal.ofReal (succProb p q C) ∧
      τ / ENNReal.ofReal (succProb p q C)
        = τ * ENNReal.ofReal (Real.exp (mutualInfo p q C
            + kl (QS p q C) (fun a => (p a : ℝ)) + kl (QA p q C) (fun b => (q b : ℝ)))) ∧
      τ * ENNReal.ofReal (Real.exp (mutualInfo p q C)) ≤ τ / ENNReal.ofReal (succProb p q C) := by
  have hA : ∀ k, MeasurableSet (X k ⁻¹' (C : Set (α × β))) :=
    fun k => hXm k C.measurableSet
  have hsA : ∀ k, μ (X k ⁻¹' (C : Set (α × β))) = ENNReal.ofReal (succProb p q C) := by
    intro k
    rw [← Measure.map_apply (hXm k) C.measurableSet, hlaw k, Pmeas_finset]
  have hindA : iIndepSet (fun k => X k ⁻¹' (C : Set (α × β))) μ := by
    rw [iIndepSet_iff]
    intro S f hf
    refine hind.meas_biInter (fun i hi => ?_)
    have hle : MeasurableSpace.generateFrom {X i ⁻¹' (C : Set (α × β))}
        ≤ MeasurableSpace.comap (X i) inferInstance := by
      refine MeasurableSpace.generateFrom_le (fun t ht => ?_)
      rw [Set.mem_singleton_iff] at ht
      subst ht
      exact ⟨_, C.measurableSet, rfl⟩
    exact hle _ (hf i hi)
  have hs1 : ENNReal.ofReal (succProb p q C) ≤ 1 := by
    have := hindA.isProbabilityMeasure
    rw [← hsA 0]
    exact prob_le_one
  have heq : τ / ENNReal.ofReal (succProb p q C)
      = τ * ENNReal.ofReal (Real.exp (mutualInfo p q C
          + kl (QS p q C) (fun a => (p a : ℝ)) + kl (QA p q C) (fun b => (q b : ℝ)))) := by
    rw [ledger p q C hs, Real.exp_log (by positivity), one_div, ENNReal.ofReal_inv_of_pos hs,
      div_eq_mul_inv]
  refine ⟨RestartBound.lintegral_totalCost_eq hA hindA hsA hs1, heq, ?_⟩
  rw [heq]
  have k1 := kl_QS_nonneg p q C hp hs
  have k2 := kl_QA_nonneg p q C hq hs
  gcongr
  linarith

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β] in
/-- (iii), cost form: for `0 < τ < ⊤`, `τ * exp I_Q = τ / s` iff `Q_S = p` and `Q_A = q`. -/
theorem expected_cost_eq_iff (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1)
    (hs : 0 < succProb p q C) {τ : ℝ≥0∞} (hτ0 : τ ≠ 0) (hτ : τ ≠ ⊤) :
    τ * ENNReal.ofReal (Real.exp (mutualInfo p q C)) = τ / ENNReal.ofReal (succProb p q C) ↔
      QS p q C = (fun a => (p a : ℝ)) ∧ QA p q C = (fun b => (q b : ℝ)) := by
  rw [← ledger_eq_iff p q C hp hq hs]
  have h1 : τ / ENNReal.ofReal (succProb p q C)
      = τ * ENNReal.ofReal (Real.exp (Real.log (1 / succProb p q C))) := by
    rw [Real.exp_log (by positivity), one_div, ENNReal.ofReal_inv_of_pos hs, div_eq_mul_inv]
  rw [h1, ENNReal.mul_right_inj hτ0 hτ,
    ENNReal.ofReal_eq_ofReal_iff (Real.exp_pos _).le (Real.exp_pos _).le, Real.exp_eq_exp]

/-! ## Examples -/

/-- Uniform weights on `Fin k`. -/
noncomputable def unifFin (k : ℕ) : Fin k → ℝ≥0 := fun _ => (k : ℝ≥0)⁻¹

/-- The diagonal event `S = A` on `Fin k × Fin k`. -/
def diagC (k : ℕ) : Finset (Fin k × Fin k) := univ.filter (fun x => x.1 = x.2)

lemma unifFin_sum {k : ℕ} (hk : 0 < k) : ∑ a, unifFin k a = 1 := by
  have : (k : ℝ≥0) ≠ 0 := by exact_mod_cast hk.ne'
  simp [unifFin, this]

lemma diagC_card (k : ℕ) : (diagC k).card = k := by
  have : diagC k = (univ : Finset (Fin k)).diag := by
    ext ω; simp [diagC, Finset.mem_diag]
  rw [this, Finset.diag_card]; simp

lemma colliderA_succProb {k : ℕ} (hk : 0 < k) :
    succProb (unifFin k) (unifFin k) (diagC k) = 1 / k := by
  have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold succProb P unifFin
  rw [sum_const, diagC_card]
  simp only [NNReal.coe_inv, NNReal.coe_natCast, nsmul_eq_mul]
  field_simp

lemma colliderA_QS {k : ℕ} (hk : 0 < k) :
    QS (unifFin k) (unifFin k) (diagC k) = fun a => (unifFin k a : ℝ) := by
  have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  funext a
  unfold QS Q
  rw [colliderA_succProb hk]
  simp only [diagC, mem_filter, mem_univ, true_and, P, unifFin, NNReal.coe_inv,
    NNReal.coe_natCast]
  rw [sum_ite_eq]
  simp only [mem_univ, ite_true]
  field_simp

lemma colliderA_QA {k : ℕ} (hk : 0 < k) :
    QA (unifFin k) (unifFin k) (diagC k) = fun b => (unifFin k b : ℝ) := by
  have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  funext b
  unfold QA Q
  rw [colliderA_succProb hk]
  simp only [diagC, mem_filter, mem_univ, true_and, P, unifFin, NNReal.coe_inv,
    NNReal.coe_natCast]
  rw [sum_ite_eq']
  simp only [mem_univ, ite_true]
  field_simp

/-- PostselectionColliderA instance: uniform on `Fin k`, `C` = diagonal; the bound is attained
with `s = 1 / k` and `I_Q = log k`. -/
theorem colliderA {k : ℕ} (hk : 0 < k) :
    ∑ a, unifFin k a = 1 ∧
    succProb (unifFin k) (unifFin k) (diagC k) = 1 / k ∧
    QS (unifFin k) (unifFin k) (diagC k) = (fun a => (unifFin k a : ℝ)) ∧
    QA (unifFin k) (unifFin k) (diagC k) = (fun b => (unifFin k b : ℝ)) ∧
    mutualInfo (unifFin k) (unifFin k) (diagC k) = Real.log k ∧
    mutualInfo (unifFin k) (unifFin k) (diagC k)
      = Real.log (1 / succProb (unifFin k) (unifFin k) (diagC k)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : 0 < succProb (unifFin k) (unifFin k) (diagC k) := by
    rw [colliderA_succProb hk]; positivity
  have heq := (ledger_eq_iff _ _ _ (unifFin_sum hk) (unifFin_sum hk) hs).2
    ⟨colliderA_QS hk, colliderA_QA hk⟩
  refine ⟨unifFin_sum hk, colliderA_succProb hk, colliderA_QS hk, colliderA_QA hk, ?_, heq⟩
  rw [heq, colliderA_succProb hk, one_div_one_div]

/-- Fair bit. -/
noncomputable def fairBit : Bool → ℝ≥0 := fun _ => (2 : ℝ≥0)⁻¹

/-- The event `Z = X xor Y = false`. -/
def xorC : Finset (Bool × Bool) := univ.filter (fun x => xor x.1 x.2 = false)

lemma xorC_eq_diag : xorC = univ.filter (fun x : Bool × Bool => x.1 = x.2) := by decide

lemma xorC_eq_pair : xorC = {(false, false), (true, true)} := by decide

lemma fairBit_sum : ∑ a, fairBit a = 1 := by
  simp [fairBit]

lemma xorB_succProb : succProb fairBit fairBit xorC = 1 / 2 := by
  rw [xorC_eq_pair]
  simp [succProb, P, fairBit]

lemma xorB_QS : QS fairBit fairBit xorC = fun a => (fairBit a : ℝ) := by
  funext a
  unfold QS Q
  rw [xorB_succProb, xorC_eq_pair]
  cases a <;> simp [P, fairBit]

lemma xorB_QA : QA fairBit fairBit xorC = fun b => (fairBit b : ℝ) := by
  funext b
  unfold QA Q
  rw [xorB_succProb, xorC_eq_pair]
  cases b <;> simp [P, fairBit]

/-- XorColliderB instance: fair independent bits, `C = {xor = false} = {X = Y}`; the bound is
attained with `s = 1 / 2` and `I_Q = log 2`. -/
theorem xorB :
    ∑ a, fairBit a = 1 ∧
    succProb fairBit fairBit xorC = 1 / 2 ∧
    QS fairBit fairBit xorC = (fun a => (fairBit a : ℝ)) ∧
    QA fairBit fairBit xorC = (fun b => (fairBit b : ℝ)) ∧
    mutualInfo fairBit fairBit xorC = Real.log 2 ∧
    mutualInfo fairBit fairBit xorC = Real.log (1 / succProb fairBit fairBit xorC) := by
  have hs : 0 < succProb fairBit fairBit xorC := by rw [xorB_succProb]; norm_num
  have heq := (ledger_eq_iff _ _ _ fairBit_sum fairBit_sum hs).2 ⟨xorB_QS, xorB_QA⟩
  refine ⟨fairBit_sum, xorB_succProb, xorB_QS, xorB_QA, ?_, heq⟩
  rw [heq, xorB_succProb, one_div_one_div]

end Bridge2A
