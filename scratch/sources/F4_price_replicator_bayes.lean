import Mathlib

/-!
# F4: Price identity, replicator = Bayes, iterated selection

"You can get information about the math of selection from watching any instance of it anywhere." This file
pins down the finite, exact core that every instance shares.

## Proved (Lean, no axioms beyond Mathlib's standard three)

Setting: types `i : Fin n`, frequencies `q i > 0` with `∑ q = 1`, fitness `w i > 0`, parent trait `z i`, offspring
trait `z' i`. `w̄ = ∑ q_i w_i`, and the replicator step is `q'_i = q_i w_i / w̄`.

* `wbar_pos`: `w̄ > 0` (the hypotheses force `n ≥ 1`).
* **(1)** `price_identity`: `∑ q'_i z'_i − ∑ q_i z_i = Cov_q(w, z)/w̄ + E_q[w (z' − z)]/w̄`.
  `price_selection_only` (`z' = z`: the change is `Cov_q(w, z)/w̄`) and `fisher_fundamental` (`z = w`: mean fitness
  rises by `Var_q(w)/w̄`, written `cov q w w / wbar q w`) are its corollaries.
* **(2)** `replicator_eq_bayes`: the replicator step with fitness `w i = L i o` *is* the Bayes posterior with prior
  `q` and likelihood `L · o` (the two formulas agree by definition, `rfl`). `sel_sum_one`, `sel_pos`: the posterior is
  a probability vector with full support. `sel_scale`: both see fitness/likelihood only up to a nonzero scalar.
  `selection_is_conditioning_on_survival`: every positive fitness, rescaled by `c = 1 + ∑ w`, is a genuine Bernoulli
  likelihood `P(survive | i) = w i / c ∈ (0, 1]`, and the replicator step equals the posterior given `survive`.
* **(3)** `sel_iterate`: `k` steps with fixed fitness give `q_i w_i^k / ∑_j q_j w_j^k`.
* **(3')** `sel_comp`: selecting with `w₁` and then `w₂` equals one step with fitness `w₁ * w₂` (sequential Bayes
  multiplies likelihoods). So replicator steps form a commutative action of the positive fitness functions under
  pointwise product. `sel_iterate` is the constant-`w` case.
* `example_two_types` (non-vacuity): `q = (1/2, 1/2)`, `w = (1, 3)`, `z = (0, 1)` gives `w̄ = 2`, `q' = (1/4, 3/4)`,
  `Cov = 1/2`, `Δz̄ = 1/4`. The last conjunct comes from `price_selection_only` with every hypothesis discharged.

## Interpreted (not proved; reading of the theorems)

* The identity holds for **any replicator** (genes, memes, viruses, prompts, policies in a population, hypotheses in
  a learner): nothing in the proofs refers to what a type *is*. Only the meanings of `w` (offspring per parent) and
  `z` (the measured trait) change. That is the sense in which any instance of selection informs all of them. The
  modelling step, "this system *is* a replicator with these `q, w, z`", is the empirical claim, and nothing here checks it.
* Replicator = Bayes reads "natural selection is inference with fitness as likelihood" (Shalizi 2009; Harper 2009).
  The map is exact for one step and for `k` steps (`sel_iterate` = the posterior after `k` i.i.d. observations
  with likelihood `w`). It does not say *what* is being inferred. Under fixed fitness the "hypothesis" it concentrates on
  is just `argmax w`.
* The transmission term `E_q[w (z' − z)]/w̄` is where mutation, biased transmission, and drift in meaning live.
  Taking `z' = z` sets it to zero by fiat. The theorem does not say when it is small.
* No finite-population sampling noise: `q'` is the expected next frequency, i.e. the infinite-population limit.

## Relation to earlier work

`scratch/SelectionUniversal.lean`, theorem `SelectionUniversal.selection_universal` (A1), proves the converse
direction with no transmission term. *Any* change `p → q` with `q ≪ p` is one selection step with fitness = likelihood
ratio normalised to `E_p w = 1`, and every trait mean moves by `Cov_p(w, z)`. That is `price_selection_only` with
`w̄ = 1`. Together they say: selection steps ⇔ absolutely continuous reweightings, and Price/Bayes is the
bookkeeping for both. The scratch file is not a module of the Lake package, so it is cited rather than imported.
This file is self-contained.

## Changes from `F4_price_replicator_bayes.statements.lean`

Only this module docstring differs. All definitions and theorem statements are textually identical.

Adversarial review: I recompiled both files. I found no false or vacuous statement among
the first prover's ten theorems. `cov` is a true covariance under `∑ q = 1`, and the Price and Fisher forms match the
textbook `w̄ Δz̄ = Cov(w, z) + E[w Δz]`. I added `sel_comp` (going up: arbitrary sequential pressures, not one
repeated `w`) and `example_two_types` to **both** files, with identical statements. No existing statement changed.
`replicator_eq_bayes` is still `rfl`, a definitional identity and not a theorem with content. The content of (2)
lives in `sel_sum_one`, `sel_scale`, `selection_is_conditioning_on_survival` and now `sel_comp`.
-/

open Finset

namespace F4

variable {n : ℕ}

/-- Mean of `z` under weights `q`. -/
def mean (q z : Fin n → ℝ) : ℝ := ∑ i, q i * z i

/-- Covariance of `w` and `z` under weights `q` (a covariance when `∑ q = 1`). -/
def cov (q w z : Fin n → ℝ) : ℝ := mean q (fun i => w i * z i) - mean q w * mean q z

/-- Mean fitness `w̄ = ∑ q_i w_i`. -/
def wbar (q w : Fin n → ℝ) : ℝ := ∑ i, q i * w i

/-- One discrete replicator step `q'_i = q_i w_i / w̄`. -/
noncomputable def sel (q w : Fin n → ℝ) : Fin n → ℝ := fun i => q i * w i / wbar q w

/-- Bayes' rule: prior `π`, likelihood `L i o = P(o | i)`, posterior `P(i | o) = π i L i o / ∑_j π j L j o`. -/
noncomputable def bayes {Obs : Type*} (π : Fin n → ℝ) (L : Fin n → Obs → ℝ) (o : Obs) : Fin n → ℝ :=
  fun i => π i * L i o / ∑ j, π j * L j o

theorem wbar_pos (q w : Fin n → ℝ) (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1) (hw : ∀ i, 0 < w i) :
    0 < wbar q w := by
  have hne : (univ : Finset (Fin n)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, sum_empty] at hq1
    exact zero_ne_one hq1
  exact Finset.sum_pos (fun i _ => mul_pos (hq i) (hw i)) hne

/-- **(1) Price identity.** -/
theorem price_identity (q w z z' : Fin n → ℝ) (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1)
    (hw : ∀ i, 0 < w i) :
    mean (sel q w) z' - mean q z
      = cov q w z / wbar q w + mean q (fun i => w i * (z' i - z i)) / wbar q w := by
  have hW : wbar q w ≠ 0 := (wbar_pos q w hq hq1 hw).ne'
  have h1 : mean (sel q w) z' = (∑ i, q i * (w i * z' i)) / wbar q w := by
    simp only [mean, sel, Finset.sum_div]
    apply sum_congr rfl; intro i _; ring
  have h2 : mean q (fun i => w i * (z' i - z i)) = (∑ i, q i * (w i * z' i)) - ∑ i, q i * (w i * z i) := by
    simp only [mean]; rw [← sum_sub_distrib]
    apply sum_congr rfl; intro i _; ring
  rw [h1, h2]
  simp only [cov, mean]
  have hw' : (∑ i, q i * w i) = wbar q w := rfl
  rw [hw']
  field_simp
  ring

/-- **(1') Pure selection** (`z' = z`): the trait mean moves by `Cov(w, z)/w̄`. -/
theorem price_selection_only (q w z : Fin n → ℝ) (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1)
    (hw : ∀ i, 0 < w i) :
    mean (sel q w) z - mean q z = cov q w z / wbar q w := by
  have h := price_identity q w z z hq hq1 hw
  simp only [sub_self, mul_zero] at h
  rw [h]; simp [mean]

/-- **(1'') Fisher's fundamental theorem (discrete, trait = fitness).** -/
theorem fisher_fundamental (q w : Fin n → ℝ) (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1)
    (hw : ∀ i, 0 < w i) :
    mean (sel q w) w - mean q w = cov q w w / wbar q w := by
  exact price_selection_only q w w hq hq1 hw

/-- **(2a) Replicator = Bayes.** -/
theorem replicator_eq_bayes {Obs : Type*} (q : Fin n → ℝ) (L : Fin n → Obs → ℝ) (o : Obs) :
    sel q (fun i => L i o) = bayes q L o := by
  rfl

/-- **(2b)** Posterior frequencies sum to 1. -/
theorem sel_sum_one (q w : Fin n → ℝ) (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1)
    (hw : ∀ i, 0 < w i) : ∑ i, sel q w i = 1 := by
  have hW : wbar q w ≠ 0 := (wbar_pos q w hq hq1 hw).ne'
  simp only [sel]
  rw [← Finset.sum_div]
  exact div_self hW

/-- **(2b')** Posterior frequencies are positive. -/
theorem sel_pos (q w : Fin n → ℝ) (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1)
    (hw : ∀ i, 0 < w i) (i : Fin n) : 0 < sel q w i := by
  exact div_pos (mul_pos (hq i) (hw i)) (wbar_pos q w hq hq1 hw)

/-- **(2c)** Selection only sees fitness up to scale (as Bayes only sees likelihood up to scale). -/
theorem sel_scale (q w : Fin n → ℝ) (c : ℝ) (hc : c ≠ 0) :
    sel q (fun i => c * w i) = sel q w := by
  funext i
  simp only [sel, wbar]
  have h1 : q i * (c * w i) = c * (q i * w i) := by ring
  have h2 : ∑ j, q j * (c * w j) = c * ∑ j, q j * w j := by
    rw [Finset.mul_sum]; apply sum_congr rfl; intro j _; ring
  rw [h1, h2, mul_div_mul_left _ _ hc]

/-- **(2d) Every selection step is conditioning on survival.** Any positive fitness is, after rescaling, a genuine
Bernoulli likelihood `P(survive | i) ∈ (0, 1]`, and the replicator step is the Bayes posterior given `survive`. -/
theorem selection_is_conditioning_on_survival (q w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    ∃ L : Fin n → Bool → ℝ,
      (∀ i b, 0 ≤ L i b) ∧ (∀ i, L i true + L i false = 1) ∧ (∀ i, 0 < L i true) ∧
      sel q w = bayes q L true := by
  set c : ℝ := 1 + ∑ j, w j with hc_def
  have hsum : ∀ i, w i ≤ ∑ j, w j := fun i =>
    Finset.single_le_sum (f := w) (fun j _ => (hw j).le) (Finset.mem_univ i)
  have hc : 0 < c := by
    have : 0 ≤ ∑ j, w j := Finset.sum_nonneg (fun j _ => (hw j).le)
    linarith
  have hle : ∀ i, w i / c ≤ 1 := fun i => by
    rw [div_le_one hc]; linarith [hsum i]
  refine ⟨fun i b => if b then w i / c else 1 - w i / c, ?_, ?_, ?_, ?_⟩
  · intro i b
    cases b
    · simp only [Bool.false_eq_true, ite_false]; linarith [hle i]
    · simp only [ite_true]; exact (div_pos (hw i) hc).le
  · intro i; simp
  · intro i; simp only [ite_true]; exact div_pos (hw i) hc
  · rw [← replicator_eq_bayes]
    have : (fun i => (fun i b => if b then w i / c else 1 - w i / c : Fin n → Bool → ℝ) i true)
        = fun i => c⁻¹ * w i := by
      funext i; simp [div_eq_inv_mul]
    rw [this, sel_scale q w c⁻¹ (inv_ne_zero hc.ne')]

/-- **(3) Iterated selection, closed form.** -/
theorem sel_iterate (q w : Fin n → ℝ) (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1)
    (hw : ∀ i, 0 < w i) (k : ℕ) :
    (fun p => sel p w)^[k] q = fun i => q i * w i ^ k / ∑ j, q j * w j ^ k := by
  have hne : (univ : Finset (Fin n)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, sum_empty] at hq1
    exact zero_ne_one hq1
  have hZ : ∀ m : ℕ, 0 < ∑ j, q j * w j ^ m := fun m =>
    Finset.sum_pos (fun j _ => mul_pos (hq j) (pow_pos (hw j) m)) hne
  induction k with
  | zero => funext i; simp [hq1]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    funext i
    simp only [sel, wbar]
    have hZk := (hZ k).ne'
    have hZk1 := (hZ (k + 1)).ne'
    have hden : ∑ j, q j * w j ^ k / (∑ l, q l * w l ^ k) * w j
        = (∑ j, q j * w j ^ (k + 1)) / ∑ l, q l * w l ^ k := by
      rw [Finset.sum_div]; apply sum_congr rfl; intro j _; rw [pow_succ]; ring
    rw [hden, pow_succ]
    field_simp

/-- **(3') Selection pressures compose multiplicatively** (sequential Bayes: two observations = one observation with
the product likelihood). Selecting with `w₁` and then with `w₂` is one step with fitness `w₁ * w₂`. `sel_iterate` is
the special case where every factor is `w`. -/
theorem sel_comp (q w₁ w₂ : Fin n → ℝ) (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1)
    (hw₁ : ∀ i, 0 < w₁ i) (hw₂ : ∀ i, 0 < w₂ i) :
    sel (sel q w₁) w₂ = sel q (fun i => w₁ i * w₂ i) := by
  have hne : (univ : Finset (Fin n)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, sum_empty] at hq1
    exact zero_ne_one hq1
  have h1 : 0 < ∑ j, q j * w₁ j := Finset.sum_pos (fun j _ => mul_pos (hq j) (hw₁ j)) hne
  have h12 : 0 < ∑ j, q j * (w₁ j * w₂ j) :=
    Finset.sum_pos (fun j _ => mul_pos (hq j) (mul_pos (hw₁ j) (hw₂ j))) hne
  funext i
  simp only [sel, wbar]
  have hden : ∑ j, q j * w₁ j / (∑ l, q l * w₁ l) * w₂ j
      = (∑ j, q j * (w₁ j * w₂ j)) / ∑ l, q l * w₁ l := by
    rw [Finset.sum_div]; apply sum_congr rfl; intro j _; ring
  rw [hden]
  field_simp [h1.ne', h12.ne']

/-- **Non-vacuity example.** Two types, `q = (1/2, 1/2)`, `w = (1, 3)`, `z = (0, 1)`: `w̄ = 2`, `q' = (1/4, 3/4)`,
`Cov = 1/2`, and the trait mean rises by `1/4 = Cov/w̄`, as `price_selection_only` says. All hypotheses are met. -/
theorem example_two_types :
    wbar ![1/2, 1/2] ![1, 3] = (2 : ℝ) ∧
    sel ![1/2, 1/2] ![1, 3] = (![1/4, 3/4] : Fin 2 → ℝ) ∧
    cov ![1/2, 1/2] ![1, 3] ![0, 1] = (1/2 : ℝ) ∧
    mean (sel ![1/2, 1/2] ![1, 3]) ![0, 1] - mean ![1/2, 1/2] ![0, 1] = (1/4 : ℝ) ∧
    mean (sel ![1/2, 1/2] ![1, 3]) ![0, 1] - mean ![1/2, 1/2] ![0, 1]
      = cov ![1/2, 1/2] ![1, 3] ![0, 1] / wbar ![1/2, 1/2] (![1, 3] : Fin 2 → ℝ) := by
  have hW : wbar ![1/2, 1/2] ![1, 3] = (2 : ℝ) := by
    simp [wbar, Fin.sum_univ_two]; norm_num
  have hS : sel ![1/2, 1/2] ![1, 3] = (![1/4, 3/4] : Fin 2 → ℝ) := by
    funext i; simp only [sel]; rw [hW]; fin_cases i <;> simp <;> norm_num
  have hC : cov ![1/2, 1/2] ![1, 3] ![0, 1] = (1/2 : ℝ) := by
    simp [cov, mean, Fin.sum_univ_two]; norm_num
  have hD : mean (sel ![1/2, 1/2] ![1, 3]) ![0, 1] - mean ![1/2, 1/2] ![0, 1] = (1/4 : ℝ) := by
    rw [hS]; simp [mean, Fin.sum_univ_two]; norm_num
  refine ⟨hW, hS, hC, hD, ?_⟩
  -- The general theorem, with its hypotheses discharged on this instance (so they are satisfiable).
  exact price_selection_only _ _ _ (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num) (by intro i; fin_cases i <;> norm_num)

end F4
