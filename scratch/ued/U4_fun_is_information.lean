import Mathlib

/-!
# U4. Fun is information: expected learning progress equals mutual information

**Interpretation (not proved).** "Fun as learning progress" (Schmidhuber's compression progress; Oudeyer's
intrinsic motivation by learning progress) is quantified here as *expected information gain*: the
average, over what the environment shows you, of how far your beliefs move (KL of posterior from prior).
The claim that this is what curiosity/fun *is* is an interpretation; nothing below proves anything about
agents, brains, or motivation.

**Proved.** Finite hypotheses `Θ`, finite observations `O`, strictly positive prior `w` summing to 1,
strictly positive likelihood `ℓ θ ·` summing to 1 for each `θ`. With joint `p θ o = w θ * ℓ θ o`,
marginal `q o = ∑ θ, p θ o`, posterior `post θ o = p θ o / q o`:

* `U4a` expected KL(posterior ‖ prior) = mutual information `∑ θ, ∑ o, p * log (p / (w * q))`;
* `U4b` it is `≥ 0`;
* `U4c` it is `= 0` when the likelihood does not depend on `θ` (an uninformative environment teaches nothing).
* `U4d` (added by the second agent, going *up*) the converse: expected gain `= 0` **iff** the likelihood
  does not depend on `θ` (equality case of Gibbs);
* `U4e` corollary: any informative environment gives *strictly positive* expected gain.

The proof file also has a concrete non-vacuity check: a two-hypothesis 3:1 coin with uniform prior
(strictly positive gain, via U4e) and a fair coin (exactly zero gain, via U4c).

Logs are natural (nats). Supporting lemmas (`gibbs`, `margX`, `margY`, `MI`, `MI_nonneg`,
`posterior_divergence_eq_MI`) are copied from `scratch/KellyInformation.lean` so this file stands alone.
-/

open Finset Real

namespace U4FunIsInformation

variable {Θ O : Type*} [Fintype Θ] [Fintype O]

/-- Joint distribution `p θ o = w θ * ℓ θ o`. -/
noncomputable def joint (w : Θ → ℝ) (ℓ : Θ → O → ℝ) (θ : Θ) (o : O) : ℝ := w θ * ℓ θ o

/-- Marginal (predictive) probability of observation `o`. -/
noncomputable def marg (w : Θ → ℝ) (ℓ : Θ → O → ℝ) (o : O) : ℝ := ∑ θ, joint w ℓ θ o

/-- Bayesian posterior over hypotheses after seeing `o`. -/
noncomputable def post (w : Θ → ℝ) (ℓ : Θ → O → ℝ) (θ : Θ) (o : O) : ℝ := joint w ℓ θ o / marg w ℓ o

set_option linter.unusedSectionVars false

/-! ## Supporting lemmas (copied verbatim from `scratch/KellyInformation.lean`) -/

section Helpers

variable {ι X Y : Type*} [Fintype ι] [Fintype X] [Fintype Y]

/-- Gibbs' inequality (KellyInformation K1). -/
theorem gibbs (p b : ι → ℝ) (hp : ∀ i, 0 < p i) (hb : ∀ i, 0 < b i)
    (hp1 : ∑ i, p i = 1) (hb1 : ∑ i, b i ≤ 1) :
    ∑ i, p i * log (b i) ≤ ∑ i, p i * log (p i) := by
  have key : ∀ i, p i * log (b i) - p i * log (p i) ≤ b i - p i := by
    intro i
    have h := log_le_sub_one_of_pos (div_pos (hb i) (hp i))
    rw [log_div (hb i).ne' (hp i).ne'] at h
    have h2 : p i * (log (b i) - log (p i)) ≤ p i * (b i / p i - 1) := mul_le_mul_of_nonneg_left h (hp i).le
    have e : p i * (b i / p i - 1) = b i - p i := by
      have hp0 := (hp i).ne'
      field_simp
    linarith [h2, e, show p i * (log (b i) - log (p i)) = p i * log (b i) - p i * log (p i) by ring]
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at this
  linarith

noncomputable def margX (p : X → Y → ℝ) (x : X) : ℝ := ∑ y, p x y
noncomputable def margY (p : X → Y → ℝ) (y : Y) : ℝ := ∑ x, p x y
noncomputable def MI (p : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, p x y * log (p x y / (margX p x * margY p y))

lemma margX_pos [Nonempty Y] (p : X → Y → ℝ) (hp : ∀ x y, 0 < p x y) (x : X) : 0 < margX p x :=
  Finset.sum_pos (fun y _ => hp x y) Finset.univ_nonempty

lemma margY_pos [Nonempty X] (p : X → Y → ℝ) (hp : ∀ x y, 0 < p x y) (y : Y) : 0 < margY p y :=
  Finset.sum_pos (fun x _ => hp x y) Finset.univ_nonempty

/-- Mutual information is nonnegative (KellyInformation K4). -/
theorem MI_nonneg [Nonempty X] [Nonempty Y] (p : X → Y → ℝ) (hp : ∀ x y, 0 < p x y)
    (hp1 : ∑ x, ∑ y, p x y = 1) : 0 ≤ MI p := by
  have hx := margX_pos p hp
  have hy := margY_pos p hp
  have sx : ∑ x, margX p x = 1 := hp1
  have sy : ∑ y, margY p y = 1 := by
    unfold margY
    rw [Finset.sum_comm]
    exact hp1
  have g := gibbs (fun q : X × Y => p q.1 q.2) (fun q => margX p q.1 * margY p q.2)
    (fun q => hp q.1 q.2) (fun q => mul_pos (hx q.1) (hy q.2))
    (by rw [Fintype.sum_prod_type]; exact hp1)
    (le_of_eq (by rw [Fintype.sum_prod_type]; simp_rw [← Finset.mul_sum, sy, mul_one]; exact sx))
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at g
  simp only at g
  unfold MI
  have e : ∀ x y, p x y * log (p x y / (margX p x * margY p y)) =
      p x y * log (p x y) - p x y * log (margX p x * margY p y) := by
    intro x y
    rw [log_div (hp x y).ne' (mul_pos (hx x) (hy y)).ne']
    ring
  simp_rw [e, Finset.sum_sub_distrib]
  linarith

/-- Average posterior-from-prior divergence equals MI (KellyInformation K5). -/
theorem posterior_divergence_eq_MI [Nonempty X] [Nonempty Y] (p : X → Y → ℝ) (hp : ∀ x y, 0 < p x y) :
    ∑ y, margY p y * ∑ x, (p x y / margY p y) * log ((p x y / margY p y) / margX p x) = MI p := by
  have hx := margX_pos p hp
  have hy := margY_pos p hp
  unfold MI
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have h1 := (hy y).ne'
  rw [div_div, mul_comm (margY p y) (margX p x), ← mul_assoc,
    show margY p y * (p x y / margY p y) = p x y by field_simp]

end Helpers

/-! ## Bridging lemmas -/

lemma joint_pos (w : Θ → ℝ) (ℓ : Θ → O → ℝ) (hw : ∀ θ, 0 < w θ) (hℓ : ∀ θ o, 0 < ℓ θ o) :
    ∀ θ o, 0 < joint w ℓ θ o := fun θ o => mul_pos (hw θ) (hℓ θ o)

/-- With normalised likelihoods the `θ`-marginal of the joint is the prior. -/
lemma margX_joint (w : Θ → ℝ) (ℓ : Θ → O → ℝ) (hℓ1 : ∀ θ, ∑ o, ℓ θ o = 1) (θ : Θ) :
    margX (joint w ℓ) θ = w θ := by
  unfold margX joint
  rw [← Finset.mul_sum, hℓ1, mul_one]

lemma margY_joint (w : Θ → ℝ) (ℓ : Θ → O → ℝ) : margY (joint w ℓ) = marg w ℓ := rfl

/-- The joint `∑ θ, w θ * ℓ θ o` sums to `1`. -/
lemma joint_sum_one (w : Θ → ℝ) (ℓ : Θ → O → ℝ) (hw1 : ∑ θ, w θ = 1) (hℓ1 : ∀ θ, ∑ o, ℓ θ o = 1) :
    ∑ θ, ∑ o, joint w ℓ θ o = 1 := by
  unfold joint
  simp_rw [← Finset.mul_sum, hℓ1, mul_one]
  exact hw1

/-- Sanity check: the posterior is a probability distribution over `Θ`. -/
lemma post_sum_one [Nonempty Θ] (w : Θ → ℝ) (ℓ : Θ → O → ℝ) (hw : ∀ θ, 0 < w θ)
    (hℓ : ∀ θ o, 0 < ℓ θ o) (o : O) : ∑ θ, post w ℓ θ o = 1 := by
  have hq : 0 < marg w ℓ o := Finset.sum_pos (fun θ _ => joint_pos w ℓ hw hℓ θ o) Finset.univ_nonempty
  unfold post
  rw [← Finset.sum_div]
  exact div_self hq.ne'

/-! ## Main results -/

/-- **U4a.** Expected learning progress equals mutual information: the `q`-average of
`KL(post(·|o) ‖ w)` equals `I(θ; o) = ∑ θ, ∑ o, p θ o * log (p θ o / (w θ * q o))`. -/
theorem U4a_expected_info_gain_eq_MI [Nonempty Θ] [Nonempty O] (w : Θ → ℝ) (ℓ : Θ → O → ℝ)
    (hw : ∀ θ, 0 < w θ) (hℓ : ∀ θ o, 0 < ℓ θ o) (hℓ1 : ∀ θ, ∑ o, ℓ θ o = 1) :
    ∑ o, marg w ℓ o * ∑ θ, post w ℓ θ o * log (post w ℓ θ o / w θ) =
      ∑ θ, ∑ o, joint w ℓ θ o * log (joint w ℓ θ o / (w θ * marg w ℓ o)) := by
  have h := posterior_divergence_eq_MI (joint w ℓ) (joint_pos w ℓ hw hℓ)
  unfold MI at h
  simp only [margX_joint w ℓ hℓ1, margY_joint] at h
  exact h

/-- **U4b.** Expected learning progress is nonnegative. -/
theorem U4b_expected_info_gain_nonneg [Nonempty Θ] [Nonempty O] (w : Θ → ℝ) (ℓ : Θ → O → ℝ)
    (hw : ∀ θ, 0 < w θ) (hw1 : ∑ θ, w θ = 1) (hℓ : ∀ θ o, 0 < ℓ θ o) (hℓ1 : ∀ θ, ∑ o, ℓ θ o = 1) :
    0 ≤ ∑ o, marg w ℓ o * ∑ θ, post w ℓ θ o * log (post w ℓ θ o / w θ) := by
  rw [U4a_expected_info_gain_eq_MI w ℓ hw hℓ hℓ1]
  have h := MI_nonneg (joint w ℓ) (joint_pos w ℓ hw hℓ) (joint_sum_one w ℓ hw1 hℓ1)
  unfold MI at h
  simp only [margX_joint w ℓ hℓ1, margY_joint] at h
  exact h

/-- **U4c.** An uninformative environment teaches nothing: if the likelihood does not depend on the
hypothesis, expected learning progress is exactly zero. -/
theorem U4c_uninformative_zero [Nonempty Θ] [Nonempty O] (w : Θ → ℝ) (ℓ : Θ → O → ℝ)
    (hw : ∀ θ, 0 < w θ) (hw1 : ∑ θ, w θ = 1) (hℓ : ∀ θ o, 0 < ℓ θ o) (hℓ1 : ∀ θ, ∑ o, ℓ θ o = 1)
    (hflat : ∀ θ θ' o, ℓ θ o = ℓ θ' o) :
    ∑ o, marg w ℓ o * ∑ θ, post w ℓ θ o * log (post w ℓ θ o / w θ) = 0 := by
  rw [U4a_expected_info_gain_eq_MI w ℓ hw hℓ hℓ1]
  apply Finset.sum_eq_zero
  intro θ _
  apply Finset.sum_eq_zero
  intro o _
  have hq : marg w ℓ o = ℓ θ o := by
    unfold marg joint
    rw [Finset.sum_congr rfl (fun θ' _ => by rw [hflat θ' θ o]), ← Finset.sum_mul, hw1, one_mul]
  have hr : joint w ℓ θ o / (w θ * marg w ℓ o) = 1 := by
    rw [hq]
    exact div_self (mul_pos (hw θ) (hℓ θ o)).ne'
  rw [hr, log_one, mul_zero]

/-! ## Going up: the converse of U4c (added by the adversarial second agent)

`U4c` only says *uninformative ⇒ zero gain*. Here we close the loop: zero expected gain happens
**only** for an uninformative environment. This needs the equality case of Gibbs' inequality
(`log x = x - 1 ⇒ x = 1`), which the copied helpers do not supply. -/

lemma marg_pos [Nonempty Θ] (w : Θ → ℝ) (ℓ : Θ → O → ℝ) (hw : ∀ θ, 0 < w θ)
    (hℓ : ∀ θ o, 0 < ℓ θ o) (o : O) : 0 < marg w ℓ o :=
  Finset.sum_pos (fun θ _ => joint_pos w ℓ hw hℓ θ o) Finset.univ_nonempty

lemma marg_sum_one (w : Θ → ℝ) (ℓ : Θ → O → ℝ) (hw1 : ∑ θ, w θ = 1) (hℓ1 : ∀ θ, ∑ o, ℓ θ o = 1) :
    ∑ o, marg w ℓ o = 1 := by
  unfold marg
  rw [Finset.sum_comm]
  exact joint_sum_one w ℓ hw1 hℓ1

/-- Pointwise Gibbs term `b - a + a log (a/b) ≥ 0`. -/
lemma gibbs_term_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ b - a + a * log (a / b) := by
  have h := log_le_sub_one_of_pos (div_pos hb ha)
  rw [log_div hb.ne' ha.ne'] at h
  rw [log_div ha.ne' hb.ne']
  have h2 : a * (log b - log a) ≤ a * (b / a - 1) := mul_le_mul_of_nonneg_left h ha.le
  have e : a * (b / a - 1) = b - a := by field_simp
  nlinarith

/-- Equality case: the pointwise Gibbs term vanishes only when `a = b`. -/
lemma gibbs_term_eq_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h0 : b - a + a * log (a / b) = 0) :
    a = b := by
  by_contra hne
  have hr : b / a ≠ 1 := fun h => hne ((div_eq_one_iff_eq ha.ne').mp h).symm
  have h := log_lt_sub_one_of_pos (div_pos hb ha) hr
  rw [log_div hb.ne' ha.ne'] at h
  rw [log_div ha.ne' hb.ne'] at h0
  have h2 : a * (log b - log a) < a * (b / a - 1) := mul_lt_mul_of_pos_left h ha
  have e : a * (b / a - 1) = b - a := by field_simp
  nlinarith

/-- **U4d (new).** Zero expected learning progress **iff** the environment is uninformative.
Under the U4 hypotheses, `∑ o, q o * KL(post(·|o) ‖ w) = 0 ↔ ∀ θ θ' o, ℓ θ o = ℓ θ' o`.
The `←` direction is `U4c`; the `→` direction is the equality case of Gibbs. -/
theorem U4d_zero_gain_iff_uninformative [Nonempty Θ] [Nonempty O] (w : Θ → ℝ) (ℓ : Θ → O → ℝ)
    (hw : ∀ θ, 0 < w θ) (hw1 : ∑ θ, w θ = 1) (hℓ : ∀ θ o, 0 < ℓ θ o) (hℓ1 : ∀ θ, ∑ o, ℓ θ o = 1) :
    (∑ o, marg w ℓ o * ∑ θ, post w ℓ θ o * log (post w ℓ θ o / w θ) = 0) ↔
      ∀ θ θ' o, ℓ θ o = ℓ θ' o := by
  constructor
  · intro h0
    rw [U4a_expected_info_gain_eq_MI w ℓ hw hℓ hℓ1] at h0
    have hq := marg_pos w ℓ hw hℓ
    have hp := joint_pos w ℓ hw hℓ
    let t : Θ → O → ℝ := fun θ o => w θ * marg w ℓ o - joint w ℓ θ o +
      joint w ℓ θ o * log (joint w ℓ θ o / (w θ * marg w ℓ o))
    have ht : ∀ θ o, 0 ≤ t θ o := fun θ o =>
      gibbs_term_nonneg (hp θ o) (mul_pos (hw θ) (hq o))
    have hA : ∑ θ, ∑ o, w θ * marg w ℓ o = 1 := by
      simp_rw [← Finset.mul_sum, marg_sum_one w ℓ hw1 hℓ1, mul_one]
      exact hw1
    have hsum : ∑ θ, ∑ o, t θ o = 0 := by
      have e : ∑ θ, ∑ o, t θ o = (∑ θ, ∑ o, w θ * marg w ℓ o) - (∑ θ, ∑ o, joint w ℓ θ o) +
          ∑ θ, ∑ o, joint w ℓ θ o * log (joint w ℓ θ o / (w θ * marg w ℓ o)) := by
        simp only [t, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [e, hA, joint_sum_one w ℓ hw1 hℓ1, h0]
      ring
    have hzero : ∀ θ o, t θ o = 0 := by
      intro θ o
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun θ _ => Finset.sum_nonneg (fun o _ => ht θ o))).mp hsum θ (Finset.mem_univ _)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun o _ => ht θ o)).mp h1 o (Finset.mem_univ _)
    have hlq : ∀ θ o, ℓ θ o = marg w ℓ o := by
      intro θ o
      have e := gibbs_term_eq_zero (hp θ o) (mul_pos (hw θ) (hq o)) (hzero θ o)
      unfold joint at e
      exact mul_left_cancel₀ (hw θ).ne' e
    intro θ θ' o
    rw [hlq θ o, hlq θ' o]
  · intro hflat
    exact U4c_uninformative_zero w ℓ hw hw1 hℓ hℓ1 hflat

/-- **U4e (corollary of U4d + U4b).** Any informative environment (some observation whose likelihood
depends on the hypothesis) gives *strictly positive* expected learning progress. -/
theorem U4e_informative_pos [Nonempty Θ] [Nonempty O] (w : Θ → ℝ) (ℓ : Θ → O → ℝ)
    (hw : ∀ θ, 0 < w θ) (hw1 : ∑ θ, w θ = 1) (hℓ : ∀ θ o, 0 < ℓ θ o) (hℓ1 : ∀ θ, ∑ o, ℓ θ o = 1)
    (hinf : ∃ θ θ' o, ℓ θ o ≠ ℓ θ' o) :
    0 < ∑ o, marg w ℓ o * ∑ θ, post w ℓ θ o * log (post w ℓ θ o / w θ) := by
  rcases (U4b_expected_info_gain_nonneg w ℓ hw hw1 hℓ hℓ1).lt_or_eq with h | h
  · exact h
  · obtain ⟨θ, θ', o, hne⟩ := hinf
    exact absurd ((U4d_zero_gain_iff_uninformative w ℓ hw hw1 hℓ hℓ1).mp h.symm θ θ' o) hne

/-! ## Non-vacuity: a concrete coin

Two hypotheses about a coin (`Bool`), uniform prior, likelihood `3/4` for "the face matching the
hypothesis" and `1/4` otherwise. All U4 hypotheses hold, so U4b/U4e give strictly positive gain;
the fair-coin likelihood `1/2` gives exactly zero (U4c). -/

section Example

/-- Uniform prior on two hypotheses. -/
noncomputable def wEx : Bool → ℝ := fun _ => 1 / 2

/-- Informative likelihood: hypothesis `θ` says the coin favours face `θ` at 3:1. -/
noncomputable def ℓEx : Bool → Bool → ℝ := fun θ o => if θ = o then 3 / 4 else 1 / 4

lemma wEx_pos : ∀ θ, 0 < wEx θ := fun _ => by norm_num [wEx]
lemma wEx_sum : ∑ θ, wEx θ = 1 := by norm_num [wEx]
lemma ℓEx_pos : ∀ θ o, 0 < ℓEx θ o := fun θ o => by unfold ℓEx; split_ifs <;> norm_num
lemma ℓEx_sum : ∀ θ, ∑ o, ℓEx θ o = 1 := fun θ => by cases θ <;> norm_num [ℓEx]

/-- The informative coin teaches something: strictly positive expected learning progress. -/
example : 0 < ∑ o, marg wEx ℓEx o * ∑ θ, post wEx ℓEx θ o * log (post wEx ℓEx θ o / wEx θ) :=
  U4e_informative_pos wEx ℓEx wEx_pos wEx_sum ℓEx_pos ℓEx_sum
    ⟨true, false, true, by norm_num [ℓEx]⟩

/-- Fair-coin likelihood: ignores the hypothesis. -/
noncomputable def ℓFair : Bool → Bool → ℝ := fun _ _ => 1 / 2

/-- The fair coin, whose likelihood ignores the hypothesis, teaches exactly nothing. -/
example : ∑ o, marg wEx ℓFair o * ∑ θ, post wEx ℓFair θ o * log (post wEx ℓFair θ o / wEx θ) = 0 :=
  U4c_uninformative_zero wEx ℓFair wEx_pos wEx_sum (fun _ _ => by norm_num [ℓFair])
    (fun _ => by norm_num [ℓFair]) (fun _ _ _ => rfl)

end Example

end U4FunIsInformation
