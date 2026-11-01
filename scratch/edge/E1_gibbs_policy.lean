import Mathlib

/-!
# E1. The Gibbs policy (finite Gibbs variational principle)

**Proved here** (finite nonempty action type `A`, edges `e : A → ℝ`, temperature `τ > 0`,
natural logs, probability vectors strictly positive and summing to 1):

* `gibbsPolicy_pos`, `gibbsPolicy_sum` : `g a = exp (e a / τ) / Z` is a strictly positive
  probability vector.
* `free_gibbs` : `F(g) = τ * log Z`, where `F(p) = Σ p a * e a + τ * H(p)`, `H(p) = -Σ p log p`.
* `gibbs_variational` : `F(p) ≤ F(g)` for every strictly positive probability vector `p`.
* `expectedEdge_antitone` / `entropy_monotone` (two-point form): for `0 < τ₁ < τ₂`,
  `Σ g_{τ₂} e ≤ Σ g_{τ₁} e` and `H(g_{τ₁}) ≤ H(g_{τ₂})`.
  (Only the two-point statement is proved; derivative signs are **not** formalised.)
* `entropy_le_log_card` : `H(p) ≤ log |A|`.
* `edge_given_up_le` : `max e - Σ g e ≤ τ * log |A|`.

**Added by the adversarial second agent (proved):**

* `freeObj_gap` : `F(g) - F(p) = τ · KL(p ‖ g)` exactly, with `KL(p ‖ g) = Σ p log (p / g)`.
* `gibbs_unique_maximiser` : if `p` is a strictly positive probability vector with
  `F(g) ≤ F(p)` then `p = g`, so the Gibbs policy is the **unique** maximiser.
* `gibbsPolicy_const` and three `example`s check that the results are not vacuous: `IsProb` has
  inhabitants, the Gibbs policy is not uniform for edges `(0, 1)`, the inequality is strict at a
  concrete `p ≠ g`, and `edge_given_up_le` holds for concrete data.

Statements of the prover's 13 declarations are unchanged. The second agent added only new
declarations and examples, and changed no existing statement.

**Interpretation (not proved, just reading):** `e` is the per-action edge, `τ` the price of
committing (exploration temperature); the Gibbs/softmax policy is a maximiser of
"edge plus τ·entropy", raising temperature trades edge for entropy monotonically, and the edge
forfeited by softening is at most `τ · log |A|`. The Gibbs inequality `gibbs` is copied verbatim from
`scratch/KellyInformation.lean` (K1).
-/

open Finset Real

namespace E1GibbsPolicy

variable {A : Type*} [Fintype A]

/-- Gibbs' inequality (copied from `KellyInformation.gibbs`). -/
theorem gibbs (p b : A → ℝ) (hp : ∀ i, 0 < p i) (hb : ∀ i, 0 < b i)
    (hp1 : ∑ i, p i = 1) (hb1 : ∑ i, b i ≤ 1) :
    ∑ i, p i * log (b i) ≤ ∑ i, p i * log (p i) := by
  have key : ∀ i, p i * log (b i) - p i * log (p i) ≤ b i - p i := by
    intro i
    have h := log_le_sub_one_of_pos (div_pos (hb i) (hp i))
    rw [log_div (hb i).ne' (hp i).ne'] at h
    have h2 : p i * (log (b i) - log (p i)) ≤ p i * (b i / p i - 1) :=
      mul_le_mul_of_nonneg_left h (hp i).le
    have e : p i * (b i / p i - 1) = b i - p i := by
      have hp0 := (hp i).ne'
      field_simp
    linarith [h2, e, show p i * (log (b i) - log (p i)) = p i * log (b i) - p i * log (p i) by ring]
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at this
  linarith

/-- Partition function `Z = Σ exp (e a / τ)`. -/
noncomputable def partition (τ : ℝ) (e : A → ℝ) : ℝ := ∑ a, exp (e a / τ)

/-- The Gibbs (softmax) policy `g a = exp (e a / τ) / Z`. -/
noncomputable def gibbsPolicy (τ : ℝ) (e : A → ℝ) (a : A) : ℝ := exp (e a / τ) / partition τ e

/-- Shannon entropy `H(p) = -Σ p log p` (nats). -/
noncomputable def entropy (p : A → ℝ) : ℝ := -∑ a, p a * log (p a)

/-- Expected edge `Σ p a * e a`. -/
noncomputable def expectedEdge (p e : A → ℝ) : ℝ := ∑ a, p a * e a

/-- Free objective `F(p) = Σ p e + τ H(p)`. -/
noncomputable def freeObj (τ : ℝ) (e p : A → ℝ) : ℝ := expectedEdge p e + τ * entropy p

/-- A strictly positive probability vector. -/
def IsProb (p : A → ℝ) : Prop := (∀ a, 0 < p a) ∧ ∑ a, p a = 1

theorem partition_pos [Nonempty A] (τ : ℝ) (e : A → ℝ) : 0 < partition τ e :=
  Finset.sum_pos (fun _ _ => exp_pos _) univ_nonempty

theorem gibbsPolicy_pos [Nonempty A] (τ : ℝ) (e : A → ℝ) (a : A) : 0 < gibbsPolicy τ e a :=
  div_pos (exp_pos _) (partition_pos τ e)

theorem gibbsPolicy_sum [Nonempty A] (τ : ℝ) (e : A → ℝ) : ∑ a, gibbsPolicy τ e a = 1 := by
  unfold gibbsPolicy
  rw [← Finset.sum_div]
  exact div_self (partition_pos τ e).ne'

theorem gibbsPolicy_isProb [Nonempty A] (τ : ℝ) (e : A → ℝ) : IsProb (gibbsPolicy τ e) :=
  ⟨gibbsPolicy_pos τ e, gibbsPolicy_sum τ e⟩

theorem log_gibbsPolicy [Nonempty A] (τ : ℝ) (e : A → ℝ) (a : A) :
    log (gibbsPolicy τ e a) = e a / τ - log (partition τ e) := by
  unfold gibbsPolicy
  rw [log_div (exp_pos _).ne' (partition_pos τ e).ne', log_exp]

/-- For any probability vector `p`, `Σ p log g = (Σ p e)/τ - log Z`. -/
theorem cross_gibbs [Nonempty A] (τ : ℝ) (e p : A → ℝ) (hp1 : ∑ a, p a = 1) :
    ∑ a, p a * log (gibbsPolicy τ e a) = expectedEdge p e / τ - log (partition τ e) := by
  simp_rw [log_gibbsPolicy, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul, expectedEdge, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- **E1.a** `F(g) = τ log Z`. -/
theorem free_gibbs [Nonempty A] (τ : ℝ) (hτ : 0 < τ) (e : A → ℝ) :
    freeObj τ e (gibbsPolicy τ e) = τ * log (partition τ e) := by
  have h := cross_gibbs τ e (gibbsPolicy τ e) (gibbsPolicy_sum τ e)
  unfold freeObj entropy
  rw [h]
  field_simp
  ring

/-- **E1.b** Gibbs variational principle: the Gibbs policy maximises `F`. -/
theorem gibbs_variational [Nonempty A] (τ : ℝ) (hτ : 0 < τ) (e p : A → ℝ) (hp : IsProb p) :
    freeObj τ e p ≤ freeObj τ e (gibbsPolicy τ e) := by
  rw [free_gibbs τ hτ e]
  have hg := gibbs p (gibbsPolicy τ e) hp.1 (gibbsPolicy_pos τ e) hp.2 (gibbsPolicy_sum τ e).le
  rw [cross_gibbs τ e p hp.2] at hg
  unfold freeObj entropy
  have : expectedEdge p e ≤ τ * (∑ a, p a * log (p a)) + τ * log (partition τ e) := by
    have h2 := mul_le_mul_of_nonneg_left hg hτ.le
    rw [mul_sub, mul_div_cancel₀ _ hτ.ne'] at h2
    linarith
  linarith

/-- Comparison lemma: Gibbs at temperatures `τ₁ < τ₂`, entropy rises. -/
theorem entropy_monotone [Nonempty A] (τ₁ τ₂ : ℝ) (h1 : 0 < τ₁) (h12 : τ₁ < τ₂) (e : A → ℝ) :
    entropy (gibbsPolicy τ₁ e) ≤ entropy (gibbsPolicy τ₂ e) := by
  have hA := gibbs_variational τ₁ h1 e _ (gibbsPolicy_isProb τ₂ e)
  have hB := gibbs_variational τ₂ (h1.trans h12) e _ (gibbsPolicy_isProb τ₁ e)
  unfold freeObj at hA hB
  have : (τ₂ - τ₁) * (entropy (gibbsPolicy τ₁ e) - entropy (gibbsPolicy τ₂ e)) ≤ 0 := by
    nlinarith
  by_contra hc
  rw [not_le] at hc
  have : 0 < (τ₂ - τ₁) * (entropy (gibbsPolicy τ₁ e) - entropy (gibbsPolicy τ₂ e)) :=
    mul_pos (by linarith) (by linarith)
  linarith

/-- Two-point monotonicity: expected edge of the Gibbs policy is non-increasing in `τ`. -/
theorem expectedEdge_antitone [Nonempty A] (τ₁ τ₂ : ℝ) (h1 : 0 < τ₁) (h12 : τ₁ < τ₂)
    (e : A → ℝ) :
    expectedEdge (gibbsPolicy τ₂ e) e ≤ expectedEdge (gibbsPolicy τ₁ e) e := by
  have hA := gibbs_variational τ₁ h1 e _ (gibbsPolicy_isProb τ₂ e)
  have hH := entropy_monotone τ₁ τ₂ h1 h12 e
  unfold freeObj at hA
  have : τ₁ * entropy (gibbsPolicy τ₁ e) ≤ τ₁ * entropy (gibbsPolicy τ₂ e) :=
    mul_le_mul_of_nonneg_left hH h1.le
  linarith

/-- Entropy of a positive probability vector is at most `log |A|`. -/
theorem entropy_le_log_card [Nonempty A] (p : A → ℝ) (hp : IsProb p) :
    entropy p ≤ log (Fintype.card A) := by
  have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hg := gibbs p (fun _ => 1 / (Fintype.card A : ℝ)) hp.1 (fun _ => by positivity) hp.2
    (by simp [Finset.card_univ])
  rw [← Finset.sum_mul, hp.2, one_mul, one_div, log_inv] at hg
  unfold entropy
  linarith

/-- **E1.c** Edge given up: `max e - Σ g e ≤ τ log |A|`. -/
theorem edge_given_up_le [Nonempty A] (τ : ℝ) (hτ : 0 < τ) (e : A → ℝ) :
    univ.sup' univ_nonempty e - expectedEdge (gibbsPolicy τ e) e ≤ τ * log (Fintype.card A) := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := A)) e
  rw [ha]
  have hF := free_gibbs τ hτ e
  have hH := entropy_le_log_card _ (gibbsPolicy_isProb τ e)
  have hZ : exp (e a / τ) ≤ partition τ e :=
    Finset.single_le_sum (f := fun b => exp (e b / τ)) (fun b _ => (exp_pos _).le) (mem_univ a)
  have hlog : e a / τ ≤ log (partition τ e) := by
    rw [← log_exp (e a / τ)]
    exact log_le_log (exp_pos _) hZ
  have hlog' : e a ≤ τ * log (partition τ e) := by
    have := mul_le_mul_of_nonneg_left hlog hτ.le
    rwa [mul_div_cancel₀ _ hτ.ne'] at this
  unfold freeObj at hF
  have : τ * entropy (gibbsPolicy τ e) ≤ τ * log (Fintype.card A) :=
    mul_le_mul_of_nonneg_left hH hτ.le
  linarith


/-- **Exact gap (added by the second agent).** `F(g) - F(p) = τ · KL(p ‖ g)`. -/
theorem freeObj_gap [Nonempty A] (τ : ℝ) (hτ : 0 < τ) (e p : A → ℝ) (hp : IsProb p) :
    freeObj τ e (gibbsPolicy τ e) - freeObj τ e p =
      τ * ∑ a, p a * log (p a / gibbsPolicy τ e a) := by
  have hsplit : ∑ a, p a * log (p a / gibbsPolicy τ e a) =
      ∑ a, p a * log (p a) - ∑ a, p a * log (gibbsPolicy τ e a) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [log_div (hp.1 a).ne' (gibbsPolicy_pos τ e a).ne']
    ring
  rw [hsplit, cross_gibbs τ e p hp.2, free_gibbs τ hτ e]
  unfold freeObj entropy
  rw [mul_sub, mul_sub, mul_div_cancel₀ _ hτ.ne']
  ring

/-- **Uniqueness (added by the second agent).** Any strictly positive probability vector that
does at least as well as the Gibbs policy on `F` *is* the Gibbs policy. -/
theorem gibbs_unique_maximiser [Nonempty A] (τ : ℝ) (hτ : 0 < τ) (e p : A → ℝ) (hp : IsProb p)
    (hopt : freeObj τ e (gibbsPolicy τ e) ≤ freeObj τ e p) :
    p = gibbsPolicy τ e := by
  set g := gibbsPolicy τ e with hg_def
  have hgpos : ∀ a, 0 < g a := gibbsPolicy_pos τ e
  have hgsum : ∑ a, g a = 1 := gibbsPolicy_sum τ e
  -- pointwise slack `d a = g a - p a - p a * log (g a / p a) ≥ 0`
  set d : A → ℝ := fun a => g a - p a - p a * log (g a / p a) with hd_def
  have hdnn : ∀ a, 0 ≤ d a := by
    intro a
    have h := log_le_sub_one_of_pos (div_pos (hgpos a) (hp.1 a))
    have h2 := mul_le_mul_of_nonneg_left h (hp.1 a).le
    have : p a * (g a / p a - 1) = g a - p a := by
      have := (hp.1 a).ne'
      field_simp
    simp only [hd_def]
    linarith
  -- `Σ d = KL(p ‖ g) ≤ 0`
  have hsum_d : ∑ a, d a = ∑ a, p a * log (p a / g a) := by
    simp only [hd_def]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hgsum, hp.2, sub_self, zero_sub,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [log_div (hgpos a).ne' (hp.1 a).ne', log_div (hp.1 a).ne' (hgpos a).ne']
    ring
  have hgap := freeObj_gap τ hτ e p hp
  have hKL : ∑ a, p a * log (p a / g a) ≤ 0 := by
    have : τ * ∑ a, p a * log (p a / g a) ≤ 0 := by rw [← hgap]; linarith
    by_contra hc
    rw [not_le] at hc
    linarith [mul_pos hτ hc]
  have hzero : ∀ a ∈ univ, d a = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hdnn a)).1
      (le_antisymm (hsum_d ▸ hKL) (Finset.sum_nonneg (fun a _ => hdnn a)))
  funext a
  have hda := hzero a (mem_univ a)
  by_contra hne
  have hratio : g a / p a ≠ 1 := by
    intro h1
    apply hne
    have := (hp.1 a).ne'
    field_simp at h1
    linarith
  have hlt := log_lt_sub_one_of_pos (div_pos (hgpos a) (hp.1 a)) hratio
  have h2 := mul_lt_mul_of_pos_left hlt (hp.1 a)
  have : p a * (g a / p a - 1) = g a - p a := by
    have := (hp.1 a).ne'
    field_simp
  simp only [hd_def] at hda
  linarith

/-! ### Concrete examples (non-vacuity) -/

/-- With constant edges the Gibbs policy is uniform, at every temperature. -/
theorem gibbsPolicy_const [Nonempty A] (τ c : ℝ) (a : A) :
    gibbsPolicy τ (fun _ => c) a = 1 / (Fintype.card A : ℝ) := by
  unfold gibbsPolicy partition
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : exp (c / τ) ≠ 0 := (exp_pos _).ne'
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Two actions, edges `0` and `1`, temperature `1`: `g = (1/(1+e), e/(1+e))`, so the Gibbs
policy is genuinely non-uniform and favours the higher edge. -/
example : gibbsPolicy 1 ![(0 : ℝ), 1] 0 < gibbsPolicy 1 ![(0 : ℝ), 1] 1 := by
  unfold gibbsPolicy
  apply div_lt_div_of_pos_right _ (partition_pos _ _)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, div_one]
  exact exp_lt_exp.2 one_pos

/-- The variational principle has content: the point-ish vector `(1/4, 3/4)` is a strictly
positive probability vector, so `gibbs_variational` applies to it. -/
example : IsProb (![1/4, 3/4] : Fin 2 → ℝ) := by
  refine ⟨fun a => ?_, ?_⟩
  · fin_cases a <;> norm_num
  · simp [Fin.sum_univ_two]; norm_num

/-- Strictness has content: with constant edges on two actions the Gibbs policy is `(1/2, 1/2)`,
so by `gibbs_unique_maximiser` the vector `(1/4, 3/4)` scores *strictly* below it. -/
example (τ c : ℝ) (hτ : 0 < τ) :
    freeObj τ (fun _ : Fin 2 => c) ![1/4, 3/4] <
      freeObj τ (fun _ : Fin 2 => c) (gibbsPolicy τ (fun _ => c)) := by
  have hp : IsProb (![1/4, 3/4] : Fin 2 → ℝ) := by
    refine ⟨fun a => ?_, ?_⟩
    · fin_cases a <;> norm_num
    · simp [Fin.sum_univ_two]; norm_num
  refine lt_of_le_of_ne (gibbs_variational τ hτ _ _ hp) (fun h => ?_)
  have := congrFun (gibbs_unique_maximiser τ hτ _ _ hp h.ge) 0
  rw [gibbsPolicy_const] at this
  simp at this

/-- Concrete instance of `edge_given_up_le`: edges `(0, 1)` at temperature `1`, so the edge
given up is at most `log 2` (numerically `1/(1+e) ≈ 0.27 ≤ 0.69`). -/
example : univ.sup' univ_nonempty ![(0 : ℝ), 1] - expectedEdge (gibbsPolicy 1 ![(0 : ℝ), 1])
    ![(0 : ℝ), 1] ≤ 1 * log 2 := by
  have := edge_given_up_le (A := Fin 2) 1 one_pos ![(0 : ℝ), 1]
  simpa using this

end E1GibbsPolicy
