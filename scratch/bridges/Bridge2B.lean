import Mathlib

/-!
# Postselection ledger: `log (1/s) = I_Q(S;A) + KL(Q_S ‖ p) + KL(Q_A ‖ q)`

Setting. `α`, `β` finite types, `p : α → ℝ≥0`, `q : β → ℝ≥0`, prior `P (a, b) = p a * q b`,
a postselection event `C : Finset (α × β)` of prior mass `s = ∑_{x ∈ C} P x`, and the
postselected law `Q = P(· | C)` with marginals `Q_S`, `Q_A`. KL divergence is the finite sum
`kl μ ν = ∑ i, μ i * log (μ i / ν i)` with natural log; since `Real.log 0 = 0` this has
`0 * log 0 = 0`. The mutual information is `I_Q(S;A) = kl Q (Q_S ⊗ Q_A)`.

PROVED
* `ledger` (i): if `s > 0` then `I_Q(S;A) + KL(Q_S ‖ p) + KL(Q_A ‖ q) = log (1 / s)`.
  The normalisations `∑ p = ∑ q = 1` are not needed for this identity.
* `ledger_of_prob` (i) with the normalisation hypotheses of the target.
* `postS_ac`, `postA_ac`, `post_ac` : absolute continuity `Q_S ≪ p`, `Q_A ≪ q`,
  `Q ≪ Q_S ⊗ Q_A`, so each finite-sum KL above is the genuine (finite) KL divergence.
* `kl_nonneg`, `kl_eq_zero_iff` : Gibbs' inequality and its equality case for finite
  probability vectors with `μ ≪ ν`.
* `mutualInfo_nonneg`, `mutualInfo_le_log_inv_mass`, `exp_mutualInfo_le_inv_mass` :
  `0 ≤ I_Q ≤ log (1/s)`, i.e. `exp I_Q ≤ 1/s`.
* `log_inv_mass_eq_mutualInfo_iff` (iii): `log (1/s) = I_Q ↔ Q_S = p ∧ Q_A = q`.
* `expected_cost` (ii): for runs `R i : Ω → α × β` that are i.i.d. (`iIndepFun`) with law
  `P` (`μ (R i ⁻¹' {x}) = P x`), each costing `τ`, restarted until the run lands in `C`,
  the expected total cost is `τ / s = τ * exp (I_Q + KL(Q_S‖p) + KL(Q_A‖q)) ≥ τ * exp I_Q`.
  This uses `RestartBound.lintegral_totalCost_eq`, copied verbatim below.
* `expected_cost_eq_iff` (iii, cost form): for `0 < τ < ⊤`, `τ / s = τ * exp I_Q` iff
  `Q_S = p ∧ Q_A = q`.
* `graph_*` : general equality case: `p`, `q` uniform on `n`-element types and `C` the graph
  of a bijection `σ : α ≃ β`. Then `s = 1/n`, `Q_S = p`, `Q_A = q`, `I_Q = log n`,
  `log (1/s) = I_Q`.
* `colliderA_*` : `PostselectionColliderA` (uniform on `Fin k`, `k ≥ 1`, `C` = diagonal
  `{S = A}`): `s = 1/k`, `I_Q = log k`, equality holds, cost `τ / s = τ * exp I_Q = kτ`.
* `xorZero_eq_eq`, `xor_*` : `XorColliderB` (`X`, `Y` fair independent bits,
  `C = xorZero = {X xor Y = false}`): `C = {X = Y}`, `s = 1/2`, `I_Q = log 2`, equality holds,
  cost `τ / s = τ * exp I_Q = 2τ`.
* `mass_le_one` : `s ≤ 1` under the normalisations (needed by the restart lemma).

INTERPRETED
* `C ⊆ α × β` is a `Finset`; `Q x = P x / s` on `C` and `0` off `C`.
* "i.i.d. runs with law `P`" is `iIndepFun R μ` together with `μ (R i ⁻¹' {x}) = P x` for
  every `i`, `x`; "restart until the run lands in `C`" is `RestartBound.totalCost` with
  success events `A i = R i ⁻¹' C` and constant cost `τ`.
* The `RestartBound` definitions and lemmas (`allFail`, `numRuns`, `totalCost`,
  `measurableSet_allFail`, `measure_allFail`, `lintegral_numRuns`, `measurable_numRuns`,
  `lintegral_totalCost_eq`) are copied verbatim from `scratch/coloring/RestartBound.lean`
  into `Bridge2B.RestartBound`, since scratch files are not importable modules.
* The two colliders are re-expressed in this file's `(p, q, C)` format; their source files are
  not imported. In the cost form of the equality case, `τ ≠ 0` and `τ ≠ ⊤` are needed: at
  `τ = 0` both sides vanish for every `C`.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Bridge2B

/-! ## Copied verbatim from `scratch/coloring/RestartBound.lean` -/

namespace RestartBound

open ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The event that runs `0, …, k-1` all fail, i.e. run `k` is performed. -/
def allFail (A : ℕ → Set Ω) (k : ℕ) : Set Ω := ⋂ i ∈ range k, (A i)ᶜ

/-- Number of runs performed: the number of `k` such that runs `0, …, k-1` all failed. -/
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
  rw [ENNReal.tsum_geometric, ENNReal.sub_sub_cancel one_ne_top hs1]

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
  rw [lintegral_const_mul _ (measurable_numRuns hA), lintegral_numRuns hA hind hs hs1, div_eq_mul_inv]

end RestartBound

/-! ## Finite KL divergence and Gibbs' inequality -/

section KL

variable {ι : Type*} [Fintype ι]

/-- KL divergence of finite vectors, natural log, with `0 * log 0 = 0` (`Real.log 0 = 0`). -/
noncomputable def kl (μ ν : ι → ℝ) : ℝ := ∑ i, μ i * Real.log (μ i / ν i)

lemma kl_term_ge {m n : ℝ} (hm : 0 ≤ m) (hn0 : 0 ≤ n) (hac : 0 < m → 0 < n) :
    m - n ≤ m * Real.log (m / n) := by
  rcases hm.eq_or_lt with h | h
  · subst h
    simpa using hn0
  · have hn := hac h
    have h1 := Real.one_sub_inv_le_log_of_pos (div_pos h hn)
    rw [inv_div] at h1
    calc m - n = m * (1 - n / m) := by field_simp
      _ ≤ m * Real.log (m / n) := mul_le_mul_of_nonneg_left h1 h.le

lemma kl_term_gt {m n : ℝ} (hm : 0 < m) (hn : 0 < n) (hne : m ≠ n) :
    m - n < m * Real.log (m / n) := by
  have ht : n / m ≠ 1 := by
    intro h; exact hne ((div_eq_one_iff_eq hm.ne').1 h).symm
  have h1 := Real.log_lt_sub_one_of_pos (div_pos hn hm) ht
  have h2 : Real.log (m / n) = - Real.log (n / m) := by
    rw [← Real.log_inv, inv_div]
  rw [h2]
  have h3 : m * (n / m - 1) = n - m := by field_simp
  nlinarith

/-- Gibbs' inequality for finite vectors with `μ ≪ ν`. -/
theorem kl_nonneg {μ ν : ι → ℝ} (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 ≤ ν i)
    (hμ1 : ∑ i, μ i = 1) (hν1 : ∑ i, ν i = 1) (hac : ∀ i, 0 < μ i → 0 < ν i) :
    0 ≤ kl μ ν := by
  have : ∑ i, (μ i - ν i) ≤ kl μ ν :=
    Finset.sum_le_sum fun i _ => kl_term_ge (hμ i) (hν i) (hac i)
  rw [Finset.sum_sub_distrib, hμ1, hν1, sub_self] at this
  exact this

lemma kl_self (μ : ι → ℝ) : kl μ μ = 0 := by
  unfold kl
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : μ i = 0
  · simp [h]
  · simp [div_self h]

/-- Equality case of Gibbs' inequality. -/
theorem kl_eq_zero_iff {μ ν : ι → ℝ} (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 ≤ ν i)
    (hμ1 : ∑ i, μ i = 1) (hν1 : ∑ i, ν i = 1) (hac : ∀ i, 0 < μ i → 0 < ν i) :
    kl μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h0
    have hd : ∀ i ∈ (univ : Finset ι), 0 ≤ μ i * Real.log (μ i / ν i) - (μ i - ν i) :=
      fun i _ => sub_nonneg.2 (kl_term_ge (hμ i) (hν i) (hac i))
    have hsum : ∑ i, (μ i * Real.log (μ i / ν i) - (μ i - ν i)) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hμ1, hν1]
      unfold kl at h0
      rw [h0]; ring
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hd).1 hsum
    funext i
    have hi := hz i (mem_univ i)
    rcases (hμ i).eq_or_lt with h | h
    · rw [← h] at hi ⊢
      simp at hi
      exact hi.symm
    · by_contra hne
      have := kl_term_gt h (hac i h) hne
      linarith
  · rintro rfl; exact kl_self μ

end KL

/-! ## Prior, postselected law, marginals -/

section Ledger

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Prior `P (a, b) = p a * q b`. -/
noncomputable def prior (p : α → ℝ≥0) (q : β → ℝ≥0) (x : α × β) : ℝ :=
  (p x.1 : ℝ) * (q x.2 : ℝ)

/-- Prior mass `s = P(C)` of the postselection event. -/
noncomputable def mass (p : α → ℝ≥0) (q : β → ℝ≥0) (C : Finset (α × β)) : ℝ :=
  ∑ x ∈ C, prior p q x

/-- Postselected law `Q = P(· | C)`. -/
noncomputable def post (p : α → ℝ≥0) (q : β → ℝ≥0) (C : Finset (α × β)) (x : α × β) : ℝ :=
  if x ∈ C then prior p q x / mass p q C else 0

/-- First marginal `Q_S` of the postselected law. -/
noncomputable def postS (p : α → ℝ≥0) (q : β → ℝ≥0) (C : Finset (α × β)) (a : α) : ℝ :=
  ∑ b, post p q C (a, b)

/-- Second marginal `Q_A` of the postselected law. -/
noncomputable def postA (p : α → ℝ≥0) (q : β → ℝ≥0) (C : Finset (α × β)) (b : β) : ℝ :=
  ∑ a, post p q C (a, b)

/-- Mutual information `I_Q(S;A) = KL(Q ‖ Q_S ⊗ Q_A)`. -/
noncomputable def mutualInfo (p : α → ℝ≥0) (q : β → ℝ≥0) (C : Finset (α × β)) : ℝ :=
  kl (post p q C) (fun x => postS p q C x.1 * postA p q C x.2)

variable {p : α → ℝ≥0} {q : β → ℝ≥0} {C : Finset (α × β)}

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
lemma prior_nonneg (x : α × β) : 0 ≤ prior p q x :=
  mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
lemma mass_nonneg : 0 ≤ mass p q C :=
  Finset.sum_nonneg fun x _ => prior_nonneg x

omit [Fintype α] [Fintype β] in
lemma post_nonneg (x : α × β) : 0 ≤ post p q C x := by
  unfold post
  split_ifs
  · exact div_nonneg (prior_nonneg x) mass_nonneg
  · exact le_rfl

omit [Fintype α] in
lemma postS_nonneg (a : α) : 0 ≤ postS p q C a :=
  Finset.sum_nonneg fun _ _ => post_nonneg _

omit [Fintype β] in
lemma postA_nonneg (b : β) : 0 ≤ postA p q C b :=
  Finset.sum_nonneg fun _ _ => post_nonneg _

lemma sum_post (hs : 0 < mass p q C) : ∑ x, post p q C x = 1 := by
  unfold post
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div]
  exact div_self hs.ne'

lemma sum_postS (hs : 0 < mass p q C) : ∑ a, postS p q C a = 1 := by
  rw [← sum_post hs, Fintype.sum_prod_type]; rfl

lemma sum_postA (hs : 0 < mass p q C) : ∑ b, postA p q C b = 1 := by
  rw [← sum_post hs, Fintype.sum_prod_type_right]; rfl

omit [Fintype α] in
lemma post_le_postS (x : α × β) : post p q C x ≤ postS p q C x.1 :=
  Finset.single_le_sum (f := fun b => post p q C (x.1, b)) (fun _ _ => post_nonneg _)
    (mem_univ x.2)

omit [Fintype β] in
lemma post_le_postA (x : α × β) : post p q C x ≤ postA p q C x.2 :=
  Finset.single_le_sum (f := fun a => post p q C (a, x.2)) (fun _ _ => post_nonneg _)
    (mem_univ x.1)

omit [Fintype α] [Fintype β] in
lemma post_pos_iff (hs : 0 < mass p q C) (x : α × β) :
    0 < post p q C x ↔ x ∈ C ∧ 0 < prior p q x := by
  unfold post
  split_ifs with hx
  · simp only [hx, true_and]
    exact ⟨fun h => (div_pos_iff_of_pos_right hs).1 h, fun h => div_pos h hs⟩
  · simp [hx]

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
lemma prior_pos_iff (x : α × β) : 0 < prior p q x ↔ 0 < p x.1 ∧ 0 < q x.2 := by
  unfold prior
  constructor
  · intro h
    have h1 : (p x.1 : ℝ) ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact lt_irrefl _ h
    have h2 : (q x.2 : ℝ) ≠ 0 := fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl _ h
    exact ⟨NNReal.coe_pos.1 (lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm h1)),
      NNReal.coe_pos.1 (lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm h2))⟩
  · rintro ⟨h1, h2⟩
    exact mul_pos (by exact_mod_cast h1) (by exact_mod_cast h2)

omit [Fintype α] in
/-- `Q_S ≪ p`. -/
lemma postS_ac (hs : 0 < mass p q C) (a : α) : 0 < postS p q C a → 0 < (p a : ℝ) := by
  intro h
  obtain ⟨b, -, hb⟩ := Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℝ))
    (g := fun b => post p q C (a, b)) (by simpa [postS] using h)
  have := ((post_pos_iff hs (a, b)).1 hb).2
  exact_mod_cast ((prior_pos_iff (a, b)).1 this).1

omit [Fintype β] in
/-- `Q_A ≪ q`. -/
lemma postA_ac (hs : 0 < mass p q C) (b : β) : 0 < postA p q C b → 0 < (q b : ℝ) := by
  intro h
  obtain ⟨a, -, ha⟩ := Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℝ))
    (g := fun a => post p q C (a, b)) (by simpa [postA] using h)
  have := ((post_pos_iff hs (a, b)).1 ha).2
  exact_mod_cast ((prior_pos_iff (a, b)).1 this).2

/-- `Q ≪ Q_S ⊗ Q_A`. -/
lemma post_ac (x : α × β) :
    0 < post p q C x → 0 < postS p q C x.1 * postA p q C x.2 := fun h =>
  mul_pos (lt_of_lt_of_le h (post_le_postS x)) (lt_of_lt_of_le h (post_le_postA x))

/-- (i) The postselection ledger. -/
theorem ledger (hs : 0 < mass p q C) :
    mutualInfo p q C + kl (postS p q C) (fun a => (p a : ℝ))
      + kl (postA p q C) (fun b => (q b : ℝ)) = Real.log (1 / mass p q C) := by
  have hS : kl (postS p q C) (fun a => (p a : ℝ))
      = ∑ x : α × β, post p q C x * Real.log (postS p q C x.1 / p x.1) := by
    unfold kl
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    dsimp only
    rw [← Finset.sum_mul]; rfl
  have hA : kl (postA p q C) (fun b => (q b : ℝ))
      = ∑ x : α × β, post p q C x * Real.log (postA p q C x.2 / q x.2) := by
    unfold kl
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    dsimp only
    rw [← Finset.sum_mul]; rfl
  have key : ∀ x : α × β,
      post p q C x * Real.log (post p q C x / (postS p q C x.1 * postA p q C x.2))
        + post p q C x * Real.log (postS p q C x.1 / p x.1)
        + post p q C x * Real.log (postA p q C x.2 / q x.2)
        = post p q C x * Real.log (1 / mass p q C) := by
    intro x
    rcases (post_nonneg (C := C) x).eq_or_lt with h0 | hpos
    · rw [← h0]; ring
    · have hS0 : 0 < postS p q C x.1 := lt_of_lt_of_le hpos (post_le_postS x)
      have hA0 : 0 < postA p q C x.2 := lt_of_lt_of_le hpos (post_le_postA x)
      obtain ⟨hxC, hpr⟩ := (post_pos_iff hs x).1 hpos
      obtain ⟨hp0, hq0⟩ := (prior_pos_iff x).1 hpr
      have hp0' : (0 : ℝ) < p x.1 := by exact_mod_cast hp0
      have hq0' : (0 : ℝ) < q x.2 := by exact_mod_cast hq0
      have hQ : post p q C x = (p x.1 : ℝ) * q x.2 / mass p q C := by
        simp [post, hxC, prior]
      have hlogQ : Real.log (post p q C x)
          = Real.log (p x.1) + Real.log (q x.2) - Real.log (mass p q C) := by
        rw [hQ, Real.log_div (mul_pos hp0' hq0').ne' hs.ne',
          Real.log_mul hp0'.ne' hq0'.ne']
      rw [Real.log_div hpos.ne' (mul_pos hS0 hA0).ne', Real.log_mul hS0.ne' hA0.ne',
        Real.log_div hS0.ne' hp0'.ne', Real.log_div hA0.ne' hq0'.ne',
        Real.log_div one_ne_zero hs.ne', Real.log_one, hlogQ]
      ring
  rw [mutualInfo, kl, hS, hA, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun x _ => key x), ← Finset.sum_mul, sum_post hs, one_mul]

/-- (i) with the normalisation hypotheses `∑ p = ∑ q = 1` of the target. -/
theorem ledger_of_prob (_hp : ∑ a, p a = 1) (_hq : ∑ b, q b = 1) (hs : 0 < mass p q C) :
    mutualInfo p q C + kl (postS p q C) (fun a => (p a : ℝ))
      + kl (postA p q C) (fun b => (q b : ℝ)) = Real.log (1 / mass p q C) :=
  ledger hs

lemma sum_coe_eq_one {γ : Type*} [Fintype γ] {r : γ → ℝ≥0} (h : ∑ c, r c = 1) :
    ∑ c, (r c : ℝ) = 1 := by
  rw [← NNReal.coe_sum, h, NNReal.coe_one]

lemma klS_nonneg (hp : ∑ a, p a = 1) (hs : 0 < mass p q C) :
    0 ≤ kl (postS p q C) (fun a => (p a : ℝ)) :=
  kl_nonneg postS_nonneg (fun _ => NNReal.coe_nonneg _) (sum_postS hs) (sum_coe_eq_one hp)
    (postS_ac hs)

lemma klA_nonneg (hq : ∑ b, q b = 1) (hs : 0 < mass p q C) :
    0 ≤ kl (postA p q C) (fun b => (q b : ℝ)) :=
  kl_nonneg postA_nonneg (fun _ => NNReal.coe_nonneg _) (sum_postA hs) (sum_coe_eq_one hq)
    (postA_ac hs)

lemma sum_prod_marg (hs : 0 < mass p q C) :
    ∑ x : α × β, postS p q C x.1 * postA p q C x.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_postS hs, sum_postA hs, one_mul]

theorem mutualInfo_nonneg (hs : 0 < mass p q C) : 0 ≤ mutualInfo p q C :=
  kl_nonneg post_nonneg (fun _ => mul_nonneg (postS_nonneg _) (postA_nonneg _)) (sum_post hs)
    (sum_prod_marg hs) post_ac

theorem mutualInfo_le_log_inv_mass (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1)
    (hs : 0 < mass p q C) : mutualInfo p q C ≤ Real.log (1 / mass p q C) := by
  rw [← ledger hs]
  linarith [klS_nonneg hp hs (q := q) (C := C), klA_nonneg hq hs (p := p) (C := C)]

theorem exp_mutualInfo_le_inv_mass (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1)
    (hs : 0 < mass p q C) : Real.exp (mutualInfo p q C) ≤ 1 / mass p q C := by
  rw [← Real.exp_log (one_div_pos.2 hs)]
  exact Real.exp_le_exp.2 (mutualInfo_le_log_inv_mass hp hq hs)

/-- (iii) Equality `log (1/s) = I_Q` holds iff both postselected marginals equal the priors. -/
theorem log_inv_mass_eq_mutualInfo_iff (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1)
    (hs : 0 < mass p q C) :
    Real.log (1 / mass p q C) = mutualInfo p q C ↔
      postS p q C = (fun a => (p a : ℝ)) ∧ postA p q C = (fun b => (q b : ℝ)) := by
  have h1 := klS_nonneg hp hs (q := q) (C := C)
  have h2 := klA_nonneg hq hs (p := p) (C := C)
  rw [← ledger hs,
    ← kl_eq_zero_iff postS_nonneg (fun _ => NNReal.coe_nonneg _) (sum_postS hs)
      (sum_coe_eq_one hp) (postS_ac hs),
    ← kl_eq_zero_iff postA_nonneg (fun _ => NNReal.coe_nonneg _) (sum_postA hs)
      (sum_coe_eq_one hq) (postA_ac hs)]
  constructor
  · intro h
    have h0 : kl (postS p q C) (fun a => (p a : ℝ)) + kl (postA p q C) (fun b => (q b : ℝ))
        = 0 := by linarith
    exact (add_eq_zero_iff_of_nonneg h1 h2).1 h0
  · rintro ⟨e1, e2⟩
    rw [e1, e2]; ring

end Ledger

/-! ## Restart cost -/

section Cost

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β]
  {p : α → ℝ≥0} {q : β → ℝ≥0} {C : Finset (α × β)} {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β] [DecidableEq α] [DecidableEq β] in
lemma mass_le_one (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1) : mass p q C ≤ 1 := by
  calc mass p q C ≤ ∑ x : α × β, prior p q x :=
        Finset.sum_le_sum_of_subset_of_nonneg (subset_univ C) (fun x _ _ => prior_nonneg x)
    _ = (∑ a, (p a : ℝ)) * ∑ b, (q b : ℝ) := by
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]; rfl
    _ = 1 := by rw [sum_coe_eq_one hp, sum_coe_eq_one hq, one_mul]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β] in
lemma inv_mass_eq_exp (hs : 0 < mass p q C) :
    1 / mass p q C = Real.exp (mutualInfo p q C + kl (postS p q C) (fun a => (p a : ℝ))
      + kl (postA p q C) (fun b => (q b : ℝ))) := by
  rw [ledger hs, Real.exp_log (one_div_pos.2 hs)]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β] [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
lemma div_ofReal_eq (hs : 0 < mass p q C) (τ : ℝ≥0∞) :
    τ / ENNReal.ofReal (mass p q C) = τ * ENNReal.ofReal (1 / mass p q C) := by
  rw [div_eq_mul_inv, one_div, ENNReal.ofReal_inv_of_pos hs]

/-- (ii) Expected restart cost: i.i.d. runs with law `P`, each costing `τ`, restarted until
the run lands in `C`, cost `τ / s = τ * exp (I_Q + KL(Q_S‖p) + KL(Q_A‖q)) ≥ τ * exp I_Q`. -/
theorem expected_cost {μ : Measure Ω} (R : ℕ → Ω → α × β) (hR : ∀ i, Measurable (R i))
    (hind : iIndepFun R μ) (hlaw : ∀ i x, μ (R i ⁻¹' {x}) = ENNReal.ofReal (prior p q x))
    (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1) (hs : 0 < mass p q C) (τ : ℝ≥0∞) :
    ∫⁻ ω, RestartBound.totalCost (fun i => R i ⁻¹' (C : Set (α × β))) (fun _ _ => τ) ω ∂μ
        = τ / ENNReal.ofReal (mass p q C) ∧
      τ / ENNReal.ofReal (mass p q C) = τ * ENNReal.ofReal (Real.exp (mutualInfo p q C
        + kl (postS p q C) (fun a => (p a : ℝ)) + kl (postA p q C) (fun b => (q b : ℝ)))) ∧
      τ * ENNReal.ofReal (Real.exp (mutualInfo p q C)) ≤ τ / ENNReal.ofReal (mass p q C) := by
  have hC : MeasurableSet (C : Set (α × β)) := C.finite_toSet.measurableSet
  have hA : ∀ i, MeasurableSet (R i ⁻¹' (C : Set (α × β))) := fun i => hR i hC
  have hindA : iIndepSet (fun i => R i ⁻¹' (C : Set (α × β))) μ := by
    rw [iIndepSet_iff_iIndep]
    refine iIndep_of_iIndep_of_le ((iIndepFun_iff_iIndep _ _ _).1 hind) (fun i => ?_)
    refine MeasurableSpace.generateFrom_le fun t ht => ?_
    rw [Set.mem_singleton_iff] at ht
    exact ⟨_, hC, ht.symm⟩
  have hmass : ∀ i, μ (R i ⁻¹' (C : Set (α × β))) = ENNReal.ofReal (mass p q C) := by
    intro i
    rw [← sum_measure_preimage_singleton C (fun y _ => hR i (measurableSet_singleton y))]
    simp_rw [hlaw i]
    rw [mass, ENNReal.ofReal_sum_of_nonneg (fun x _ => prior_nonneg x)]
  have hs1 : ENNReal.ofReal (mass p q C) ≤ 1 := ENNReal.ofReal_le_one.2 (mass_le_one hp hq)
  refine ⟨RestartBound.lintegral_totalCost_eq hA hindA hmass hs1, ?_, ?_⟩
  · rw [div_ofReal_eq hs, inv_mass_eq_exp hs]
  · rw [div_ofReal_eq hs]
    exact mul_le_mul_of_nonneg_left
      (ENNReal.ofReal_le_ofReal (exp_mutualInfo_le_inv_mass hp hq hs)) zero_le

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β] in
/-- (iii) cost form: for `0 < τ < ⊤`, `τ / s = τ * exp I_Q` iff `Q_S = p` and `Q_A = q`. -/
theorem expected_cost_eq_iff (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1) (hs : 0 < mass p q C)
    {τ : ℝ≥0∞} (hτ0 : τ ≠ 0) (hτ : τ ≠ ⊤) :
    τ / ENNReal.ofReal (mass p q C) = τ * ENNReal.ofReal (Real.exp (mutualInfo p q C)) ↔
      postS p q C = (fun a => (p a : ℝ)) ∧ postA p q C = (fun b => (q b : ℝ)) := by
  rw [div_ofReal_eq hs, ENNReal.mul_right_inj hτ0 hτ,
    ENNReal.ofReal_eq_ofReal_iff (one_div_pos.2 hs).le (Real.exp_pos _).le,
    ← log_inv_mass_eq_mutualInfo_iff hp hq hs]
  constructor
  · intro h; rw [h, Real.log_exp]
  · intro h; rw [← h, Real.exp_log (one_div_pos.2 hs)]

end Cost

/-! ## Equality case: uniform priors, `C` the graph of a bijection -/

section Graph

/-- Uniform weights on a finite type. -/
noncomputable def unif (γ : Type*) [Fintype γ] : γ → ℝ≥0 :=
  fun _ => (Fintype.card γ : ℝ≥0)⁻¹

lemma unif_coe (γ : Type*) [Fintype γ] (c : γ) :
    (unif γ c : ℝ) = (Fintype.card γ : ℝ)⁻¹ := by
  simp [unif]

lemma sum_unif (γ : Type*) [Fintype γ] [Nonempty γ] : ∑ c, unif γ c = 1 := by
  simp [unif, Finset.sum_const, nsmul_eq_mul, Fintype.card_ne_zero]

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The graph `{(a, σ a)}` of a bijection `σ : α ≃ β`. -/
def graph (σ : α ≃ β) : Finset (α × β) := univ.filter fun x => x.2 = σ x.1

variable [Nonempty α] (σ : α ≃ β)

omit [DecidableEq α] [DecidableEq β] [Nonempty α] in
lemma card_eq (e : α ≃ β) : Fintype.card β = Fintype.card α := (Fintype.card_congr e).symm

omit [DecidableEq α] in
theorem graph_mass :
    mass (unif α) (unif β) (graph σ) = 1 / (Fintype.card α : ℝ) := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold mass graph
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [prior, unif_coe, card_eq σ]

omit [DecidableEq α] in
theorem graph_mass_pos : 0 < mass (unif α) (unif β) (graph σ) := by
  rw [graph_mass σ]
  have : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  positivity

theorem graph_post (x : α × β) :
    post (unif α) (unif β) (graph σ) x = if x.2 = σ x.1 then (Fintype.card α : ℝ)⁻¹ else 0 := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold post
  rw [graph_mass σ]
  by_cases hx : x.2 = σ x.1
  · simp [graph, hx, prior, unif_coe, card_eq σ]
  · simp [graph, hx]

theorem graph_postS : postS (unif α) (unif β) (graph σ) = fun a => (unif α a : ℝ) := by
  funext a
  simp [postS, graph_post σ, unif_coe]

theorem graph_postA : postA (unif α) (unif β) (graph σ) = fun b => (unif β b : ℝ) := by
  funext b
  simp only [postA, graph_post σ, unif_coe, card_eq σ]
  simp_rw [← Equiv.symm_apply_eq]
  simp

theorem graph_mutualInfo :
    mutualInfo (unif α) (unif β) (graph σ) = Real.log (Fintype.card α) := by
  have h := ledger (graph_mass_pos σ)
  rw [graph_postS σ, graph_postA σ, kl_self, kl_self, graph_mass σ] at h
  rw [one_div_one_div] at h
  linarith

theorem graph_equality :
    Real.log (1 / mass (unif α) (unif β) (graph σ)) = mutualInfo (unif α) (unif β) (graph σ) := by
  have : Nonempty β := ⟨σ (Classical.arbitrary α)⟩
  exact (log_inv_mass_eq_mutualInfo_iff (sum_unif α) (sum_unif β) (graph_mass_pos σ)).2
    ⟨graph_postS σ, graph_postA σ⟩

end Graph

/-! ## The two colliders -/

section Colliders

/-- `PostselectionColliderA`: the success event `S = A` on `Fin k × Fin k`. -/
def diagonal (k : ℕ) : Finset (Fin k × Fin k) := univ.filter fun x => x.1 = x.2

variable {k : ℕ} [NeZero k]

omit [NeZero k] in
lemma diagonal_eq_graph : diagonal k = graph (Equiv.refl (Fin k)) := by
  ext x; simp [diagonal, graph, eq_comm]

omit [NeZero k] in
lemma colliderA_unif (a : Fin k) : (unif (Fin k) a : ℝ) = 1 / (k : ℝ) := by
  rw [unif_coe, Fintype.card_fin, one_div]

theorem colliderA_mass : mass (unif (Fin k)) (unif (Fin k)) (diagonal k) = 1 / (k : ℝ) := by
  rw [diagonal_eq_graph, graph_mass, Fintype.card_fin]

theorem colliderA_mass_pos : 0 < mass (unif (Fin k)) (unif (Fin k)) (diagonal k) := by
  rw [diagonal_eq_graph]; exact graph_mass_pos _

theorem colliderA_marginals :
    postS (unif (Fin k)) (unif (Fin k)) (diagonal k) = (fun a => (unif (Fin k) a : ℝ)) ∧
      postA (unif (Fin k)) (unif (Fin k)) (diagonal k) = (fun b => (unif (Fin k) b : ℝ)) := by
  rw [diagonal_eq_graph]; exact ⟨graph_postS _, graph_postA _⟩

theorem colliderA_mutualInfo :
    mutualInfo (unif (Fin k)) (unif (Fin k)) (diagonal k) = Real.log k := by
  rw [diagonal_eq_graph, graph_mutualInfo, Fintype.card_fin]

theorem colliderA_equality :
    Real.log (1 / mass (unif (Fin k)) (unif (Fin k)) (diagonal k))
      = mutualInfo (unif (Fin k)) (unif (Fin k)) (diagonal k) := by
  rw [diagonal_eq_graph]; exact graph_equality _

theorem colliderA_cost (τ : ℝ≥0∞) :
    τ / ENNReal.ofReal (mass (unif (Fin k)) (unif (Fin k)) (diagonal k))
        = τ * ENNReal.ofReal (Real.exp (mutualInfo (unif (Fin k)) (unif (Fin k)) (diagonal k))) ∧
      τ / ENNReal.ofReal (mass (unif (Fin k)) (unif (Fin k)) (diagonal k)) = τ * k := by
  have hs := colliderA_mass_pos (k := k)
  have h1 : τ / ENNReal.ofReal (mass (unif (Fin k)) (unif (Fin k)) (diagonal k))
      = τ * ENNReal.ofReal (Real.exp (mutualInfo (unif (Fin k)) (unif (Fin k)) (diagonal k))) := by
    rw [div_ofReal_eq hs, ← colliderA_equality, Real.exp_log (one_div_pos.2 hs)]
  refine ⟨h1, ?_⟩
  rw [h1, colliderA_mutualInfo, Real.exp_log (by exact_mod_cast Nat.pos_of_neZero k),
    ENNReal.ofReal_natCast]

end Colliders

section Xor

/-- `XorColliderB`: the event `Z = X xor Y = false` on `Bool × Bool`. -/
def xorZero : Finset (Bool × Bool) := univ.filter fun x => xor x.1 x.2 = false

lemma xorZero_eq_eq : xorZero = univ.filter fun x : Bool × Bool => x.1 = x.2 := by
  ext ⟨a, b⟩; cases a <;> cases b <;> simp [xorZero]

lemma xorZero_eq_graph : xorZero = graph (Equiv.refl Bool) := by
  ext ⟨a, b⟩; cases a <;> cases b <;> simp [xorZero, graph, Finset.mem_filter] <;> decide

lemma xor_unif (b : Bool) : (unif Bool b : ℝ) = 1 / 2 := by
  rw [unif_coe, Fintype.card_bool]; norm_num

theorem xor_mass : mass (unif Bool) (unif Bool) xorZero = 1 / 2 := by
  rw [xorZero_eq_graph, graph_mass, Fintype.card_bool]; norm_num

theorem xor_mass_pos : 0 < mass (unif Bool) (unif Bool) xorZero := by
  rw [xor_mass]; norm_num

theorem xor_marginals :
    postS (unif Bool) (unif Bool) xorZero = (fun a => (unif Bool a : ℝ)) ∧
      postA (unif Bool) (unif Bool) xorZero = (fun b => (unif Bool b : ℝ)) := by
  rw [xorZero_eq_graph]; exact ⟨graph_postS _, graph_postA _⟩

theorem xor_mutualInfo : mutualInfo (unif Bool) (unif Bool) xorZero = Real.log 2 := by
  rw [xorZero_eq_graph, graph_mutualInfo, Fintype.card_bool]; norm_num

theorem xor_equality :
    Real.log (1 / mass (unif Bool) (unif Bool) xorZero)
      = mutualInfo (unif Bool) (unif Bool) xorZero := by
  rw [xorZero_eq_graph]; exact graph_equality _

theorem xor_cost (τ : ℝ≥0∞) :
    τ / ENNReal.ofReal (mass (unif Bool) (unif Bool) xorZero)
        = τ * ENNReal.ofReal (Real.exp (mutualInfo (unif Bool) (unif Bool) xorZero)) ∧
      τ / ENNReal.ofReal (mass (unif Bool) (unif Bool) xorZero) = τ * 2 := by
  have hs := xor_mass_pos
  have h1 : τ / ENNReal.ofReal (mass (unif Bool) (unif Bool) xorZero)
      = τ * ENNReal.ofReal (Real.exp (mutualInfo (unif Bool) (unif Bool) xorZero)) := by
    rw [div_ofReal_eq hs, ← xor_equality, Real.exp_log (one_div_pos.2 hs)]
  refine ⟨h1, ?_⟩
  rw [h1, xor_mutualInfo, Real.exp_log (by norm_num), ENNReal.ofReal_ofNat]

end Xor

end Bridge2B
