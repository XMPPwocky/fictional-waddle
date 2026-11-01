import Mathlib

/-!
# A12 — Martingale-ness depends on the observer (proofs)

Finite model: seed `s` uniform on `Fin m`, deterministic program `f : Fin m → Bool`
produces the next bit, exactly half the seeds give `true` (`2 * #{s | f s} = m`).
All probabilities are explicit finite sums with weight `1/m` per seed.

## What is proved (formal content)
* `uninformed_fair`: `probBit f b = 1/2` for both values of `b`.
* `informed_certain` / `informed_zero_or_one`: the conditional probability
  `condProb f s₀ b` (ratio of finite sums) equals `if f s₀ = b then 1 else 0`.
* `tower`: `Σ_s (1/m) condProb f s b = probBit f b` (the coarse forecast is the
  average of the fine forecasts).
* `lossUninformed_eq = log 2`, `lossInformed_eq = 0`, `entropyBit_eq = log 2`,
  `mutualInfo_eq = log 2`, and `gain_eq_entropy_eq_mi` bundling them.
* Kelly with even odds: informed growth `log 2`, uninformed-at-fair-bet growth `0`,
  every seed-independent split with both fractions `> 0` has growth `≤ 0`
  (`kelly_uninformed_le_zero`), so the gain over the fair bet is exactly `log 2`.

* `gain_eq_entropy_eq_mi_general` (adversarial addition): for every `f : Fin m → Bool`
  with `0 < m`, `lossUninformed f - lossInformed f = entropyBit f` and
  `mutualInfo f = entropyBit f`. Concrete `example`s: the headline at `m = 2`, non-vacuity of
  the half-true hypothesis for every `m = 2k`, and the general theorem at `m = 3` with one
  true seed (gain `= log 3 - (2/3) log 2`).

## Interpretation (not formalised)
"The bit is a martingale / fair coin" is a statement about an observer's filtration, not
about the bit: the same deterministic `f` is a fair coin for the seed-blind observer and a
known constant for the seed-holder. Only the one-step version is formalised here (no
sequences of bits, no filtrations, no `MeasureTheory`). The `log 2` equalities are specific to
the half-true hypothesis. The general identity gain = H(bit) = I(bit; seed) for an arbitrary
deterministic `f` (any `m ≥ 1`, no half-true hypothesis) IS proved, as
`gain_eq_entropy_eq_mi_general` (added by the adversarial pass; the formal reason is that
`lossInformed f = 0`, i.e. H(bit | seed) = 0).
Caveat: `Real.log 0 = 0` in Mathlib, which is why the Kelly upper bound requires strictly
positive bets (a zero bet on a possible outcome would really give growth `-∞`).
-/

open Finset

namespace A12

variable {m : ℕ}

/-- `P(bit = b)` for the observer who does not know the seed. -/
noncomputable def probBit (f : Fin m → Bool) (b : Bool) : ℝ :=
  ∑ s : Fin m, if f s = b then (1 : ℝ) / m else 0

/-- `P(bit = b | seed = s₀)` as a ratio of explicit finite sums. -/
noncomputable def condProb (f : Fin m → Bool) (s₀ : Fin m) (b : Bool) : ℝ :=
  (∑ s : Fin m, if s = s₀ ∧ f s = b then (1 : ℝ) / m else 0) /
    (∑ s : Fin m, if s = s₀ then (1 : ℝ) / m else 0)

/-- Joint law `P(seed = s, bit = b)`. -/
noncomputable def joint (f : Fin m → Bool) (s : Fin m) (b : Bool) : ℝ :=
  if f s = b then (1 : ℝ) / m else 0

/-- Expected log-loss of the uninformed observer: `E[-log P(bit)]`. -/
noncomputable def lossUninformed (f : Fin m → Bool) : ℝ :=
  ∑ s : Fin m, (1 : ℝ) / m * (-Real.log (probBit f (f s)))

/-- Expected log-loss of the informed observer: `E[-log P(bit | seed)]`. -/
noncomputable def lossInformed (f : Fin m → Bool) : ℝ :=
  ∑ s : Fin m, (1 : ℝ) / m * (-Real.log (condProb f s (f s)))

/-- Shannon entropy of the bit (natural log). -/
noncomputable def entropyBit (f : Fin m → Bool) : ℝ :=
  -∑ b : Bool, probBit f b * Real.log (probBit f b)

/-- Mutual information `I(bit; seed) = Σ p(s,b) log (p(s,b) / (p(s) p(b)))`
(terms with `p(s,b) = 0` vanish since `0 * x = 0`). -/
noncomputable def mutualInfo (f : Fin m → Bool) : ℝ :=
  ∑ s : Fin m, ∑ b : Bool,
    joint f s b * Real.log (joint f s b / ((1 : ℝ) / m * probBit f b))

/-- Kelly log-growth with even (2-for-1) odds when betting fraction `q s b` of wealth
on outcome `b`, possibly depending on the seed `s`: `E[log (2 q(bit))]`. -/
noncomputable def kellyGrowth (f : Fin m → Bool) (q : Fin m → Bool → ℝ) : ℝ :=
  ∑ s : Fin m, (1 : ℝ) / m * Real.log (2 * q s (f s))

/-! ### Helper lemmas -/

lemma card_bit (f : Fin m → Bool)
    (hf : 2 * (univ.filter fun s => f s = true).card = m) (b : Bool) :
    2 * (univ.filter fun s => f s = b).card = m := by
  cases b
  · have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
      (fun s => f s = true)
    simp only [Bool.not_eq_true, card_univ, Fintype.card_fin] at h
    omega
  · exact hf

lemma probBit_half (hm : 2 ≤ m) (f : Fin m → Bool)
    (hf : 2 * (univ.filter fun s => f s = true).card = m) (b : Bool) :
    probBit f b = 1 / 2 := by
  have h := card_bit f hf b
  have hm' : (m : ℝ) ≠ 0 := by positivity
  unfold probBit
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have h' : (2 : ℝ) * ((univ.filter fun s => f s = b).card : ℝ) = m := by exact_mod_cast h
  field_simp
  linarith

lemma condProb_eq (hm : 2 ≤ m) (f : Fin m → Bool) (s₀ : Fin m) (b : Bool) :
    condProb f s₀ b = if f s₀ = b then 1 else 0 := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  unfold condProb
  simp only [ite_and]
  rw [Finset.sum_ite_eq' , Finset.sum_ite_eq']
  simp only [mem_univ, ite_true]
  split_ifs
  · field_simp
  · simp

/-! ### Main statements (identical to the `.statements` file) -/

/-- (1) The uninformed observer sees a fair bit. -/
theorem uninformed_fair (hm : 2 ≤ m) (f : Fin m → Bool)
    (hf : 2 * (univ.filter fun s => f s = true).card = m) (b : Bool) :
    probBit f b = 1 / 2 := by
  exact probBit_half hm f hf b

/-- (2) The informed observer predicts with certainty: conditional probability is 1 if the
program outputs `b` on that seed, else 0. -/
theorem informed_certain (hm : 2 ≤ m) (f : Fin m → Bool) (s₀ : Fin m) (b : Bool) :
    condProb f s₀ b = if f s₀ = b then 1 else 0 := by
  exact condProb_eq hm f s₀ b

theorem informed_zero_or_one (hm : 2 ≤ m) (f : Fin m → Bool) (s₀ : Fin m) (b : Bool) :
    condProb f s₀ b = 0 ∨ condProb f s₀ b = 1 := by
  rw [condProb_eq hm f s₀ b]
  split_ifs <;> simp

/-- (3) Tower property: averaging the informed forecasts over the seed recovers the
uninformed forecast. -/
theorem tower (hm : 2 ≤ m) (f : Fin m → Bool) (b : Bool) :
    ∑ s : Fin m, (1 : ℝ) / m * condProb f s b = probBit f b := by
  unfold probBit
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [condProb_eq hm f s b]
  split_ifs <;> simp

/-- (4) Log-loss values and gain. -/
theorem lossUninformed_eq (hm : 2 ≤ m) (f : Fin m → Bool)
    (hf : 2 * (univ.filter fun s => f s = true).card = m) :
    lossUninformed f = Real.log 2 := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  unfold lossUninformed
  simp only [probBit_half hm f hf, one_div, Real.log_inv, neg_neg, Finset.sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem lossInformed_eq (hm : 2 ≤ m) (f : Fin m → Bool) :
    lossInformed f = 0 := by
  unfold lossInformed
  simp [condProb_eq hm f]

theorem entropyBit_eq (hm : 2 ≤ m) (f : Fin m → Bool)
    (hf : 2 * (univ.filter fun s => f s = true).card = m) :
    entropyBit f = Real.log 2 := by
  unfold entropyBit
  simp only [Fintype.sum_bool, probBit_half hm f hf, one_div, Real.log_inv]
  ring

theorem mutualInfo_eq (hm : 2 ≤ m) (f : Fin m → Bool)
    (hf : 2 * (univ.filter fun s => f s = true).card = m) :
    mutualInfo f = Real.log 2 := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  unfold mutualInfo
  have inner : ∀ s : Fin m, ∑ b : Bool,
      joint f s b * Real.log (joint f s b / ((1 : ℝ) / m * probBit f b))
        = (1 : ℝ) / m * Real.log 2 := by
    intro s
    have : ∀ b : Bool, joint f s b * Real.log (joint f s b / ((1 : ℝ) / m * probBit f b))
        = if f s = b then (1 : ℝ) / m * Real.log 2 else 0 := by
      intro b
      unfold joint
      rw [probBit_half hm f hf b]
      split_ifs
      · congr 2
        field_simp
      · simp
    simp_rw [this]
    rw [Finset.sum_ite_eq]
    simp
  simp_rw [inner]
  simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Headline: log-loss gain = log 2 = H(bit) = I(bit; seed). -/
theorem gain_eq_entropy_eq_mi (hm : 2 ≤ m) (f : Fin m → Bool)
    (hf : 2 * (univ.filter fun s => f s = true).card = m) :
    lossUninformed f - lossInformed f = Real.log 2 ∧
      entropyBit f = Real.log 2 ∧ mutualInfo f = Real.log 2 := by
  refine ⟨?_, entropyBit_eq hm f hf, mutualInfo_eq hm f hf⟩
  rw [lossUninformed_eq hm f hf, lossInformed_eq hm f, sub_zero]

/-- (5) Kelly: informed bettor (bets all on the known outcome) grows at `log 2` per bit. -/
theorem kelly_informed (hm : 2 ≤ m) (f : Fin m → Bool) :
    kellyGrowth f (fun s b => condProb f s b) = Real.log 2 := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  unfold kellyGrowth
  simp only [condProb_eq hm f, ite_true, mul_one, Finset.sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Uninformed bettor betting its own fair forecast grows at rate 0. -/
theorem kelly_uninformed (hm : 2 ≤ m) (f : Fin m → Bool)
    (hf : 2 * (univ.filter fun s => f s = true).card = m) :
    kellyGrowth f (fun _ b => probBit f b) = 0 := by
  unfold kellyGrowth
  simp [probBit_half hm f hf]

/-- No seed-independent strictly positive betting split beats rate 0 (fair game). -/
theorem kelly_uninformed_le_zero (hm : 2 ≤ m) (f : Fin m → Bool)
    (hf : 2 * (univ.filter fun s => f s = true).card = m)
    (a : Bool → ℝ) (ha : 0 < a true) (hb : 0 < a false) (hab : a true + a false = 1) :
    kellyGrowth f (fun _ b => a b) ≤ 0 := by
  have hm' : (0 : ℝ) < m := by positivity
  unfold kellyGrowth
  have hsplit : ∀ s : Fin m, (1 : ℝ) / m * Real.log (2 * a (f s))
      = if f s = true then (1 : ℝ) / m * Real.log (2 * a true)
        else (1 : ℝ) / m * Real.log (2 * a false) := by
    intro s
    cases h : f s <;> simp
  simp_rw [hsplit]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have h1 := card_bit f hf true
  have h2 := card_bit f hf false
  have e2 : (univ.filter fun s => ¬ f s = true) = (univ.filter fun s => f s = false) := by
    ext s; simp
  rw [e2]
  have c1 : (2 : ℝ) * ((univ.filter fun s => f s = true).card : ℝ) = m := by exact_mod_cast h1
  have c2 : (2 : ℝ) * ((univ.filter fun s => f s = false).card : ℝ) = m := by exact_mod_cast h2
  have l1 := Real.log_le_sub_one_of_pos (show 0 < 2 * a true by positivity)
  have l2 := Real.log_le_sub_one_of_pos (show 0 < 2 * a false by positivity)
  have key : ((univ.filter fun s => f s = true).card : ℝ) * ((1 : ℝ) / m * Real.log (2 * a true))
      + ((univ.filter fun s => f s = false).card : ℝ) * ((1 : ℝ) / m * Real.log (2 * a false))
      = (Real.log (2 * a true) + Real.log (2 * a false)) / 2 := by
    field_simp
    linear_combination (Real.log (2 * a true)) * c1 + (Real.log (2 * a false)) * c2
  rw [key]
  linarith

/-- Kelly gain of the informed bettor over the uninformed fair bet (`1/2` on each outcome)
is exactly `log 2`. (Combined with `kelly_uninformed_le_zero`, the gain over any strictly
positive seed-independent split is `≥ log 2`; that combination is not stated as a theorem.) -/
theorem kelly_gain (hm : 2 ≤ m) (f : Fin m → Bool)
    (hf : 2 * (univ.filter fun s => f s = true).card = m) :
    kellyGrowth f (fun s b => condProb f s b) - kellyGrowth f (fun _ b => probBit f b)
      = Real.log 2 := by
  rw [kelly_informed hm f, kelly_uninformed hm f hf, sub_zero]


/-! ### Adversarial additions -/

lemma condProb_eq_of_pos (hm : 0 < m) (f : Fin m → Bool) (s₀ : Fin m) (b : Bool) :
    condProb f s₀ b = if f s₀ = b then 1 else 0 := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  unfold condProb
  simp only [ite_and]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [mem_univ, ite_true]
  split_ifs
  · field_simp
  · simp

lemma avg_eq_sum_probBit (f : Fin m → Bool) (g : Bool → ℝ) :
    ∑ s : Fin m, (1 : ℝ) / m * g (f s) = ∑ b : Bool, probBit f b * g b := by
  unfold probBit
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

/-- Generalisation (going up): for ANY program `f` (no half-true hypothesis, any `m ≥ 1`),
the informed observer's log-loss gain equals `H(bit)`, and `I(bit; seed) = H(bit)`. -/
theorem gain_eq_entropy_eq_mi_general (hm : 0 < m) (f : Fin m → Bool) :
    lossUninformed f - lossInformed f = entropyBit f ∧ mutualInfo f = entropyBit f := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hinf : lossInformed f = 0 := by
    unfold lossInformed
    simp [condProb_eq_of_pos hm f]
  have hunf : lossUninformed f = entropyBit f := by
    unfold lossUninformed entropyBit
    rw [avg_eq_sum_probBit f (fun b => -Real.log (probBit f b))]
    simp only [mul_neg, Finset.sum_neg_distrib]
  refine ⟨by rw [hinf, sub_zero, hunf], ?_⟩
  rw [← hunf]
  unfold mutualInfo lossUninformed
  refine Finset.sum_congr rfl fun s _ => ?_
  have hc : (1 : ℝ) / m ≠ 0 := by positivity
  have : ∀ b : Bool, joint f s b * Real.log (joint f s b / ((1 : ℝ) / m * probBit f b))
      = if f s = b then (1 : ℝ) / m * (-Real.log (probBit f (f s))) else 0 := by
    intro b
    unfold joint
    split_ifs with h
    · subst h
      rw [div_mul_cancel_left₀ hc, Real.log_inv]
    · simp
  simp_rw [this]
  rw [Finset.sum_ite_eq]
  simp

/-- Concrete instance of the headline with `m = 2`, `f s = (s = 0)`. -/
example :
    lossUninformed (fun s : Fin 2 => decide (s = 0)) - lossInformed (fun s : Fin 2 => decide (s = 0))
        = Real.log 2 ∧
      entropyBit (fun s : Fin 2 => decide (s = 0)) = Real.log 2 ∧
      mutualInfo (fun s : Fin 2 => decide (s = 0)) = Real.log 2 :=
  gain_eq_entropy_eq_mi (by norm_num) _ (by decide)

/-- The half-true hypothesis is satisfiable for every even `m = 2k`: it is not vacuous. -/
example (k : ℕ) :
    2 * (univ.filter fun s : Fin (2 * k) => decide (s.val < k) = true).card = 2 * k := by
  have : (univ.filter fun s : Fin (2 * k) => s.val < k).card = k := by
    rw [← Finset.card_map Fin.valEmbedding]
    have : (univ.filter fun s : Fin (2 * k) => s.val < k).map Fin.valEmbedding
        = Finset.range k := by
      ext x
      simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
      constructor
      · rintro ⟨s, hs, rfl⟩; exact hs
      · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
    rw [this, card_range]
  simp only [decide_eq_true_eq]
  omega

/-- Concrete corollary of the general theorem at a NON-half program (`m = 3`, one true seed):
the gain is `H(bit) = log 3 - (2/3) log 2` (≈ 0.637 nats), not `log 2`. -/
example :
    lossUninformed (fun s : Fin 3 => decide (s = 0)) - lossInformed (fun s : Fin 3 => decide (s = 0))
      = Real.log 3 - 2 / 3 * Real.log 2 := by
  rw [(gain_eq_entropy_eq_mi_general (by norm_num) _).1]
  have h1 : probBit (fun s : Fin 3 => decide (s = 0)) true = 1 / 3 := by
    simp [probBit]
  have h0 : probBit (fun s : Fin 3 => decide (s = 0)) false = 2 / 3 := by
    simp [probBit, Fin.sum_univ_three]; norm_num
  unfold entropyBit
  rw [Fintype.sum_bool, h1, h0, Real.log_div (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), Real.log_one]
  ring

end A12
