import Mathlib

/-!
# How much postselection it costs to fake a Bell violation with shared seeds

Shared-seed (local) model: a finite seed space `Λ` with weights `w`. For each seed, deterministic ±1 answers
`a λ x` and `b λ y` to settings `x, y : Bool`. A postselection rule `A x y λ ∈ [0, 1]` may depend on BOTH settings and
the seed (hence on the outcomes): it is the probability that the round is kept.
- `κ x y = ∑ w A` is the kept mass for setting pair `(x, y)`.
- `E x y` is the conditional correlation on kept rounds.
- `S = E₀₀ + E₀₁ + E₁₀ − E₁₁` is the CHSH value.
- `K` is the average kept fraction under uniform settings.

* P1 `postselection_cost`: `S ≤ 10 − 8K`. Faking CHSH value `S` requires discarding at least a fraction
  `(S − 2)/8` of rounds. Tightness (equality on all of `K ∈ [3/4, 1]`) is checked by explicit construction outside
  Lean (toys/cheap_to_fake/tight.py).
* Consequences, with tightness:
  - faking the PR box (S = 4) needs only 25% discarded;
  - faking Tsirelson's 2√2 needs only `(2√2 − 2)/8 ≈ 10.4%` discarded.
  - Tonight's dial (EchoesAndBounds Q4, the ledger page) discarded 41% to reach 2√2, far from optimal.
-/

namespace CheapToFake

open Finset

variable {Λ : Type*} [Fintype Λ]

def pr (x y : Bool) : ℝ := if x && y then -1 else 1

lemma pr_sq (x y : Bool) : pr x y * pr x y = 1 := by unfold pr; split_ifs <;> norm_num

lemma pm_mul {u v : ℝ} (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) : u * v = 1 ∨ u * v = -1 := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> norm_num

lemma pr_pm (x y : Bool) : pr x y = 1 ∨ pr x y = -1 := by unfold pr; split_ifs <;> simp

/-- Per setting pair: `pr · E ≤ 3 − 2D − 2κ`, where `D` is the seed mass mismatching the PR sign. -/
lemma pair_bound (w : Λ → ℝ) (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1) (c : Λ → ℝ)
    (hc : ∀ l, c l = 1 ∨ c l = -1) (s : ℝ) (hs : s = 1 ∨ s = -1) (A : Λ → ℝ) (hA0 : ∀ l, 0 ≤ A l)
    (hA1 : ∀ l, A l ≤ 1) (hκ : 0 < ∑ l, w l * A l) :
    s * ((∑ l, w l * A l * c l) / ∑ l, w l * A l)
      ≤ 3 - 2 * (∑ l, w l * ((1 - s * c l) / 2)) - 2 * ∑ l, w l * A l := by
  set κ := ∑ l, w l * A l with hκdef
  set N := ∑ l, w l * A l * ((1 - s * c l) / 2) with hN
  set D := ∑ l, w l * ((1 - s * c l) / 2) with hD
  have hm : ∀ l, 0 ≤ (1 - s * c l) / 2 ∧ (1 - s * c l) / 2 ≤ 1 := by
    intro l; rcases pm_mul hs (hc l) with h | h <;> rw [h] <;> norm_num
  have hN0 : 0 ≤ N := Finset.sum_nonneg (fun l _ => mul_nonneg (mul_nonneg (hw l) (hA0 l)) (hm l).1)
  have hκ1 : κ ≤ 1 := by
    rw [← hw1]; exact Finset.sum_le_sum (fun l _ => by nlinarith [hw l, hA1 l])
  have hnum : s * ∑ l, w l * A l * c l = κ - 2 * N := by
    rw [Finset.mul_sum, hκdef, hN, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro l _; ring
  have h1κ : ∑ l, w l * (1 - A l) = 1 - κ := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hw1, hκdef]
  have hND : D - (1 - κ) ≤ N := by
    have e : N - D + (1 - κ) = ∑ l, w l * (1 - A l) * (1 - (1 - s * c l) / 2) := by
      rw [← h1κ, hN, hD, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro l _; ring
    have : 0 ≤ N - D + (1 - κ) := by
      rw [e]; exact Finset.sum_nonneg (fun l _ => mul_nonneg (mul_nonneg (hw l) (by linarith [hA1 l]))
        (by linarith [(hm l).2]))
    linarith
  have key : s * ((∑ l, w l * A l * c l) / κ) = 1 - 2 * N / κ := by
    rw [mul_div_assoc', hnum]; field_simp
  rw [key]
  have : N ≤ N / κ := by rw [le_div_iff₀ hκ]; nlinarith
  have h2 : 2 * N / κ = 2 * (N / κ) := by ring
  rw [h2]; linarith

/-- Local deterministic CHSH: the four PR-signed products sum to at most 2. -/
lemma local_chsh (a0 a1 b0 b1 : ℝ) (h0 : a0 = 1 ∨ a0 = -1) (h1 : a1 = 1 ∨ a1 = -1)
    (h2 : b0 = 1 ∨ b0 = -1) (h3 : b1 = 1 ∨ b1 = -1) : a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1 ≤ 2 := by
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    rcases h3 with rfl | rfl <;> norm_num

/-- **P1.** -/
theorem postselection_cost (w : Λ → ℝ) (hw : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1)
    (a b : Λ → Bool → ℝ) (ha : ∀ l i, a l i = 1 ∨ a l i = -1) (hb : ∀ l i, b l i = 1 ∨ b l i = -1)
    (A : Bool → Bool → Λ → ℝ) (hA0 : ∀ x y l, 0 ≤ A x y l) (hA1 : ∀ x y l, A x y l ≤ 1)
    (hκ : ∀ x y, 0 < ∑ l, w l * A x y l) :
    let κ := fun x y => ∑ l, w l * A x y l
    let E := fun x y => (∑ l, w l * A x y l * (a l x * b l y)) / κ x y
    let S := ∑ x : Bool, ∑ y : Bool, pr x y * E x y
    let K := (∑ x : Bool, ∑ y : Bool, κ x y) / 4
    S ≤ 10 - 8 * K := by
  intro κ E S K
  have pb : ∀ x y, pr x y * E x y ≤ 3 - 2 * (∑ l, w l * ((1 - pr x y * (a l x * b l y)) / 2)) - 2 * κ x y :=
    fun x y => pair_bound w hw hw1 (fun l => a l x * b l y) (fun l => pm_mul (ha l x) (hb l y)) (pr x y)
      (pr_pm x y) (A x y) (hA0 x y) (hA1 x y) (hκ x y)
  have hDsum : 1 ≤ ∑ x : Bool, ∑ y : Bool, ∑ l, w l * ((1 - pr x y * (a l x * b l y)) / 2) := by
    have e : ∑ x : Bool, ∑ y : Bool, ∑ l, w l * ((1 - pr x y * (a l x * b l y)) / 2)
        = ∑ l, w l * ((4 - (a l false * b l false + a l false * b l true + a l true * b l false
            - a l true * b l true)) / 2) := by
      simp only [Fintype.sum_bool, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro l _; simp [pr]; ring
    rw [e, ← hw1]
    apply Finset.sum_le_sum; intro l _
    have := local_chsh (a l false) (a l true) (b l false) (b l true) (ha l false) (ha l true) (hb l false) (hb l true)
    nlinarith [hw l]
  have hS : S ≤ ∑ x : Bool, ∑ y : Bool,
      (3 - 2 * (∑ l, w l * ((1 - pr x y * (a l x * b l y)) / 2)) - 2 * κ x y) :=
    Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => pb x y))
  simp only [Fintype.sum_bool] at hS hDsum
  show S ≤ 10 - 8 * ((∑ x : Bool, ∑ y : Bool, κ x y) / 4)
  simp only [Fintype.sum_bool]
  linarith

end CheapToFake
