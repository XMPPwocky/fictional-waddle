/-
# Selection bias is the gradient of a forgotten log-normalizer

A finite population x ∈ ι has distribution p(·; θ), with one real parameter θ (the general case is
coordinatewise). A filter keeps x with probability w x, which does not depend on θ. The chance of
passing is Z(θ) = P(S; θ) = ∑ w x p(x; θ). The score of x is p'(x)/p(x), where p' = ∂θ p.

PROVED
1. `log_normalizer_grad`: ∂θ log Z = E[score | S], the survivors' mean score.
2. `survivor_grad`: the correct gradient for a survivor, ∂θ log P(x | S; θ), equals
   score(x) − ∂θ log Z. Fitting survivors with log p(x; θ) alone ("forgetting S") differs from it by
   exactly ∂θ log Z: forgetting to condition on S is, differentially, forgetting to divide by Z.
3. `score_mean_zero`, `cov_score`: if p sums to 1 for every θ, the score has mean 0 and
   Cov(score, b) = ∑ p' b for any b.
4. `selection_differential`: E[score | S] = Cov(score, w) / E[w]. This is the Price / Robertson
   selection differential.
5. `reinforce`: with reward R in place of w, ∂θ E[R] = Cov(score, R): the policy gradient.
6. `logPartition_grad`, `selection_bias_exp_family`: for an exponential family
   p(x; θ) = exp(θ f x) / Z₀(θ), log P(S; θ) = log Z_w(θ) − log Z₀(θ) with Z_w = ∑ w exp(θ f), and its
   derivative is E[f | S] − E[f]: the gap between the selected and the unselected mean, each the
   derivative of a log-partition function.

INTERPRETED (not formalized)
- "Knowing your own partition function": an agent that can compute Z₀ and the selection's Z_w can
  subtract the bias in item 6; a selection it does not model is a partition function it does not
  know.
-/

import Mathlib

namespace SelectionGradient

open Finset Real

variable {ι : Type*} [Fintype ι]

/-- Probability of passing the filter: P(S; θ) = ∑ w x p(x; θ). -/
def Z (w : ι → ℝ) (p : ι → ℝ → ℝ) (θ : ℝ) : ℝ := ∑ i, w i * p i θ

theorem hasDerivAt_Z (w : ι → ℝ) (p : ι → ℝ → ℝ) (p' : ι → ℝ) (θ : ℝ)
    (hp : ∀ i, HasDerivAt (p i) (p' i) θ) :
    HasDerivAt (Z w p) (∑ i, w i * p' i) θ := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ => (hp i).const_mul (w i))
  unfold Z
  convert h using 1
  funext t
  simp

theorem log_normalizer_grad (w : ι → ℝ) (p : ι → ℝ → ℝ) (p' : ι → ℝ) (θ : ℝ)
    (hp : ∀ i, HasDerivAt (p i) (p' i) θ) (hpos : ∀ i, 0 < p i θ) (hZ : 0 < Z w p θ) :
    HasDerivAt (fun t => Real.log (Z w p t))
      (∑ i, (w i * p i θ / Z w p θ) * (p' i / p i θ)) θ := by
  have h := (hasDerivAt_Z w p p' θ hp).log hZ.ne'
  convert h using 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have := (hpos i).ne'
  field_simp

theorem survivor_grad (w : ι → ℝ) (p : ι → ℝ → ℝ) (p' : ι → ℝ) (θ : ℝ)
    (hp : ∀ i, HasDerivAt (p i) (p' i) θ) (hpos : ∀ i, 0 < p i θ) (hZ : 0 < Z w p θ)
    (i : ι) (hw : 0 < w i) :
    HasDerivAt (fun t => Real.log (w i * p i t / Z w p t))
      (p' i / p i θ - (∑ j, w j * p' j) / Z w p θ) θ := by
  have hq := ((hp i).const_mul (w i)).div (hasDerivAt_Z w p p' θ hp) hZ.ne'
  have hval : w i * p i θ / Z w p θ ≠ 0 := (div_pos (mul_pos hw (hpos i)) hZ).ne'
  have hl := hq.log hval
  convert hl using 1
  have h1 := (hpos i).ne'
  have h2 := hZ.ne'
  have h3 := hw.ne'
  simp only [Pi.div_apply]
  field_simp

/-- The score has mean zero when `p` is a probability distribution for every θ. -/
theorem score_mean_zero (p : ι → ℝ → ℝ) (p' : ι → ℝ) (θ : ℝ)
    (hp : ∀ i, HasDerivAt (p i) (p' i) θ) (hpos : ∀ i, 0 < p i θ)
    (hnorm : ∀ t, ∑ i, p i t = 1) :
    ∑ i, p i θ * (p' i / p i θ) = 0 := by
  have hsum : HasDerivAt (fun t => ∑ i, p i t) (∑ i, p' i) θ := by
    have h := HasDerivAt.sum (u := Finset.univ) (fun i _ => hp i)
    convert h using 1
    funext t; simp
  have hconst : (fun t => ∑ i, p i t) = fun _ => (1 : ℝ) := funext hnorm
  rw [hconst] at hsum
  have h0 : ∑ i, p' i = 0 := (hasDerivAt_const θ (1 : ℝ)).unique hsum |>.symm
  rw [← h0]
  apply Finset.sum_congr rfl
  intro i _
  have := (hpos i).ne'
  field_simp

/-- Covariance under weights `q`, in centred form. -/
def cov (q a b : ι → ℝ) : ℝ :=
  ∑ i, q i * (a i - ∑ j, q j * a j) * (b i - ∑ j, q j * b j)

theorem cov_score (p : ι → ℝ → ℝ) (p' : ι → ℝ) (θ : ℝ)
    (hp : ∀ i, HasDerivAt (p i) (p' i) θ) (hpos : ∀ i, 0 < p i θ)
    (hnorm : ∀ t, ∑ i, p i t = 1) (b : ι → ℝ) :
    cov (fun i => p i θ) (fun i => p' i / p i θ) b = ∑ i, p' i * b i := by
  unfold cov
  rw [score_mean_zero p p' θ hp hpos hnorm]
  set m := ∑ j, p j θ * b j
  have h0 : ∑ i, p' i = 0 := by
    have := score_mean_zero p p' θ hp hpos hnorm
    rw [← this]
    apply Finset.sum_congr rfl
    intro i _
    have := (hpos i).ne'
    field_simp
  have hterm : ∀ i, p i θ * (p' i / p i θ - 0) * (b i - m) = p' i * b i - p' i * m := by
    intro i
    have := (hpos i).ne'
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib, ← Finset.sum_mul, h0,
    zero_mul, sub_zero]

theorem selection_differential (w : ι → ℝ) (p : ι → ℝ → ℝ) (p' : ι → ℝ) (θ : ℝ)
    (hp : ∀ i, HasDerivAt (p i) (p' i) θ) (hpos : ∀ i, 0 < p i θ)
    (hnorm : ∀ t, ∑ i, p i t = 1) (hZ : 0 < Z w p θ) :
    ∑ i, (w i * p i θ / Z w p θ) * (p' i / p i θ) =
      cov (fun i => p i θ) (fun i => p' i / p i θ) w / Z w p θ := by
  rw [cov_score p p' θ hp hpos hnorm w, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have := (hpos i).ne'
  have := hZ.ne'
  field_simp

theorem reinforce (R : ι → ℝ) (p : ι → ℝ → ℝ) (p' : ι → ℝ) (θ : ℝ)
    (hp : ∀ i, HasDerivAt (p i) (p' i) θ) (hpos : ∀ i, 0 < p i θ)
    (hnorm : ∀ t, ∑ i, p i t = 1) :
    HasDerivAt (fun t => ∑ i, R i * p i t) (cov (fun i => p i θ) (fun i => p' i / p i θ) R) θ := by
  rw [cov_score p p' θ hp hpos hnorm R]
  have h := hasDerivAt_Z R p p' θ hp
  unfold Z at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ## Exponential families: the bias is a difference of partition-function gradients -/

/-- Log of the weighted partition function ∑ w exp(θ f). -/
noncomputable def logPartition (w f : ι → ℝ) (θ : ℝ) : ℝ :=
  Real.log (∑ i, w i * Real.exp (θ * f i))

theorem partition_pos (w f : ι → ℝ) (θ : ℝ) (hw : ∀ i, 0 ≤ w i) (hne : ∃ i, 0 < w i) :
    0 < ∑ i, w i * Real.exp (θ * f i) := by
  obtain ⟨i0, hi0⟩ := hne
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le)
    ⟨i0, Finset.mem_univ _, mul_pos hi0 (Real.exp_pos _)⟩

theorem logPartition_grad (w f : ι → ℝ) (θ : ℝ) (hw : ∀ i, 0 ≤ w i) (hne : ∃ i, 0 < w i) :
    HasDerivAt (logPartition w f)
      ((∑ i, w i * Real.exp (θ * f i) * f i) / ∑ i, w i * Real.exp (θ * f i)) θ := by
  have hterm : ∀ i, HasDerivAt (fun t => w i * Real.exp (t * f i))
      (w i * (Real.exp (θ * f i) * (1 * f i))) θ :=
    fun i => (((hasDerivAt_id θ).mul_const (f i)).exp).const_mul (w i)
  have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ => hterm i)
  have hs' : HasDerivAt (fun t => ∑ i, w i * Real.exp (t * f i))
      (∑ i, w i * Real.exp (θ * f i) * f i) θ := by
    convert hs using 1
    · funext t; simp
    · apply Finset.sum_congr rfl; intro i _; ring
  have hl := hs'.log (partition_pos w f θ hw hne).ne'
  unfold logPartition
  exact hl

theorem selection_bias_exp_family [Nonempty ι] (w f : ι → ℝ) (θ : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hne : ∃ i, 0 < w i) :
    HasDerivAt
      (fun t => Real.log (∑ i, w i * (Real.exp (t * f i) / ∑ j, Real.exp (t * f j))))
      ((∑ i, w i * Real.exp (θ * f i) * f i) / (∑ i, w i * Real.exp (θ * f i)) -
        (∑ i, Real.exp (θ * f i) * f i) / (∑ i, Real.exp (θ * f i))) θ := by
  have hone : ∃ i : ι, (0 : ℝ) < (fun _ => (1 : ℝ)) i := ⟨Classical.arbitrary ι, one_pos⟩
  have h1 := logPartition_grad w f θ hw hne
  have h0 := logPartition_grad (fun _ => (1 : ℝ)) f θ (fun _ => zero_le_one) hone
  have hfun : (fun t => Real.log (∑ i, w i * (Real.exp (t * f i) / ∑ j, Real.exp (t * f j)))) =
      fun t => logPartition w f t - logPartition (fun _ => (1 : ℝ)) f t := by
    funext t
    unfold logPartition
    have hA := partition_pos w f t hw hne
    have hB := partition_pos (fun _ => (1 : ℝ)) f t (fun _ => zero_le_one) hone
    simp only [one_mul] at hB ⊢
    rw [← Real.log_div hA.ne' hB.ne', Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfun]
  convert h1.sub h0 using 1
  simp only [one_mul]

end SelectionGradient

#print axioms SelectionGradient.log_normalizer_grad
#print axioms SelectionGradient.survivor_grad
#print axioms SelectionGradient.score_mean_zero
#print axioms SelectionGradient.cov_score
#print axioms SelectionGradient.selection_differential
#print axioms SelectionGradient.reinforce
#print axioms SelectionGradient.logPartition_grad
#print axioms SelectionGradient.selection_bias_exp_family
