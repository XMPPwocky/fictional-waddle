import Mathlib

/-!
# Even/odd split of the Price selection covariance under an involution

Setting: `ι` a finite type, `σ : ι ≃ ι` with `σ (σ i) = i`, weights `q : ι → ℝ`
with `q (σ i) = q i`. `E q f = ∑ i, q i * f i`,
`Cov q f h = E q (f * h) - E q f * E q h`,
`fEven σ f i = (f i + f (σ i)) / 2`, `fOdd σ f i = (f i - f (σ i)) / 2`.

The hypotheses `q i > 0` and `∑ q = 1` of the original statement are not used:
every result below holds for any `σ`-invariant real weight vector `q`
(this is a strengthening). The theorem `cov_split_prob` restates the main
decomposition with all original hypotheses present.

PROVED
* `split`: `f = fEven σ f + fOdd σ f` (no hypotheses).
* `even_comp`: `fEven σ f ∘ σ = fEven σ f` when `σ` is an involution.
* `odd_comp`: `fOdd σ f ∘ σ = -fOdd σ f` when `σ` is an involution.
* `E_comp`: `E q (g ∘ σ) = E q g` when `q` is `σ`-invariant.
* `E_eq_zero_of_odd`: `E q g = 0` whenever `g ∘ σ = -g` and `q` is `σ`-invariant.
* `E_odd`: `E q (fOdd σ f) = 0`.
* `cov_even_odd`: `Cov q (fEven σ w) (fOdd σ z) = 0`.
* `cov_odd_even`: `Cov q (fOdd σ w) (fEven σ z) = 0`.
* `cov_split`: `Cov q w z = Cov q (fEven σ w) (fEven σ z) + Cov q (fOdd σ w) (fOdd σ z)`.
* `cov_split_prob`: the same decomposition under the full original hypotheses
  (`q i > 0`, `∑ q = 1`, `q ∘ σ = q`, `σ` an involution).

INTERPRETED: none.
-/

namespace PriceEvenOddSplit

open Finset

variable {ι : Type*} [Fintype ι]

/-- Expectation under weights `q`. -/
noncomputable def E (q f : ι → ℝ) : ℝ := ∑ i, q i * f i

/-- Covariance under weights `q`. -/
noncomputable def Cov (q f h : ι → ℝ) : ℝ := E q (fun i => f i * h i) - E q f * E q h

/-- The `σ`-even part of `f`. -/
noncomputable def fEven (σ : ι ≃ ι) (f : ι → ℝ) : ι → ℝ := fun i => (f i + f (σ i)) / 2

/-- The `σ`-odd part of `f`. -/
noncomputable def fOdd (σ : ι ≃ ι) (f : ι → ℝ) : ι → ℝ := fun i => (f i - f (σ i)) / 2

omit [Fintype ι] in
theorem split (σ : ι ≃ ι) (f : ι → ℝ) : f = fEven σ f + fOdd σ f := by
  funext i
  simp only [fEven, fOdd, Pi.add_apply]
  ring

omit [Fintype ι] in
theorem even_comp (σ : ι ≃ ι) (hσ : ∀ i, σ (σ i) = i) (f : ι → ℝ) :
    fEven σ f ∘ σ = fEven σ f := by
  funext i
  simp only [fEven, Function.comp_apply, hσ]
  ring

omit [Fintype ι] in
theorem odd_comp (σ : ι ≃ ι) (hσ : ∀ i, σ (σ i) = i) (f : ι → ℝ) :
    fOdd σ f ∘ σ = -fOdd σ f := by
  funext i
  simp only [fOdd, Function.comp_apply, hσ, Pi.neg_apply]
  ring

theorem E_comp (σ : ι ≃ ι) (q : ι → ℝ) (hq : ∀ i, q (σ i) = q i) (g : ι → ℝ) :
    E q (g ∘ σ) = E q g := by
  unfold E
  calc ∑ i, q i * (g ∘ σ) i = ∑ i, q (σ i) * g (σ i) := by
        simp only [Function.comp_apply, hq]
    _ = ∑ i, q i * g i := Equiv.sum_comp σ (fun i => q i * g i)

theorem E_eq_zero_of_odd (σ : ι ≃ ι) (q : ι → ℝ) (hq : ∀ i, q (σ i) = q i)
    (g : ι → ℝ) (hg : g ∘ σ = -g) : E q g = 0 := by
  have h1 := E_comp σ q hq g
  rw [hg] at h1
  have h2 : E q (-g) = -E q g := by
    unfold E
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  linarith

theorem E_odd (σ : ι ≃ ι) (hσ : ∀ i, σ (σ i) = i) (q : ι → ℝ)
    (hq : ∀ i, q (σ i) = q i) (f : ι → ℝ) : E q (fOdd σ f) = 0 :=
  E_eq_zero_of_odd σ q hq _ (odd_comp σ hσ f)

theorem cov_even_odd (σ : ι ≃ ι) (hσ : ∀ i, σ (σ i) = i) (q : ι → ℝ)
    (hq : ∀ i, q (σ i) = q i) (w z : ι → ℝ) :
    Cov q (fEven σ w) (fOdd σ z) = 0 := by
  have hprod : (fun i => fEven σ w i * fOdd σ z i) ∘ σ
      = -(fun i => fEven σ w i * fOdd σ z i) := by
    funext i
    have he := congrFun (even_comp σ hσ w) i
    have ho := congrFun (odd_comp σ hσ z) i
    simp only [Function.comp_apply, Pi.neg_apply] at he ho ⊢
    rw [he, ho]
    ring
  unfold Cov
  rw [E_eq_zero_of_odd σ q hq _ hprod, E_odd σ hσ q hq z]
  ring

theorem cov_odd_even (σ : ι ≃ ι) (hσ : ∀ i, σ (σ i) = i) (q : ι → ℝ)
    (hq : ∀ i, q (σ i) = q i) (w z : ι → ℝ) :
    Cov q (fOdd σ w) (fEven σ z) = 0 := by
  have hprod : (fun i => fOdd σ w i * fEven σ z i) ∘ σ
      = -(fun i => fOdd σ w i * fEven σ z i) := by
    funext i
    have he := congrFun (even_comp σ hσ z) i
    have ho := congrFun (odd_comp σ hσ w) i
    simp only [Function.comp_apply, Pi.neg_apply] at he ho ⊢
    rw [he, ho]
    ring
  unfold Cov
  rw [E_eq_zero_of_odd σ q hq _ hprod, E_odd σ hσ q hq w]
  ring

theorem cov_add_add (q a b c d : ι → ℝ) :
    Cov q (a + b) (c + d) = Cov q a c + Cov q a d + Cov q b c + Cov q b d := by
  unfold Cov E
  simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  ring

theorem cov_split (σ : ι ≃ ι) (hσ : ∀ i, σ (σ i) = i) (q : ι → ℝ)
    (hq : ∀ i, q (σ i) = q i) (w z : ι → ℝ) :
    Cov q w z = Cov q (fEven σ w) (fEven σ z) + Cov q (fOdd σ w) (fOdd σ z) := by
  conv_lhs => rw [split σ w, split σ z]
  rw [cov_add_add, cov_even_odd σ hσ q hq, cov_odd_even σ hσ q hq]
  ring

theorem cov_split_prob (σ : ι ≃ ι) (hσ : ∀ i, σ (σ i) = i) (q : ι → ℝ)
    (_hpos : ∀ i, 0 < q i) (_hsum : ∑ i, q i = 1) (hq : ∀ i, q (σ i) = q i)
    (w z : ι → ℝ) :
    Cov q w z = Cov q (fEven σ w) (fEven σ z) + Cov q (fOdd σ w) (fOdd σ z) :=
  cov_split σ hσ q hq w z

end PriceEvenOddSplit
