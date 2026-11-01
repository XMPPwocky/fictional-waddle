import Mathlib

/-!
# Spatial market, AM–GM as KL, Nash product, dagger

Source: derivations (spatial market, AM–GM/KL, Nash product, dagger).
Mathlib has no general Brouwer fixed-point theorem, so the *existence* halves of
Propositions 1 and 5 are NOT stated. Only properties *of* fixed points are stated.

Status: every statement below is proved unconditionally (no `sorry`).
-/

open Real BigOperators

namespace SpatialMarket

/-- **P1 (no profit at a clearing point).** If prices `p` are a fixed point of the clamped
market-maker update `p ↦ clamp₀¹ (p + T)`, then the trade `T` cannot profit in any world
`W ∈ [0,1]^ι`. -/
theorem clamp_fixed_no_profit {ι : Type*} [Fintype ι] (p T W : ι → ℝ)
    (hfix : ∀ i, p i = max 0 (min 1 (p i + T i)))
    (hW : ∀ i, 0 ≤ W i ∧ W i ≤ 1) :
    ∑ i, T i * (W i - p i) ≤ 0 := by
  refine Finset.sum_nonpos fun i _ => ?_
  have h := hfix i
  obtain ⟨hW0, hW1⟩ := hW i
  rcases le_total (p i + T i) 1 with h1 | h1
  · rw [min_eq_right h1] at h
    rcases le_total 0 (p i + T i) with h0 | h0
    · rw [max_eq_right h0] at h
      have : T i = 0 := by linarith
      simp [this]
    · rw [max_eq_left h0] at h
      nlinarith
  · rw [min_eq_left h1, max_eq_right zero_le_one] at h
    nlinarith

/-- **P4a (a covered loop is flat).** An arbitrageur whose demand `g` is strictly increasing
with `g 0 = 0` trades nothing at a fixed point only if the loop holonomy `H` is zero. -/
theorem covered_loop_flat (g : ℝ → ℝ) (hg : StrictMono g) (h0 : g 0 = 0) (H : ℝ)
    (hfix : g H = 0) : H = 0 :=
  hg.injective (hfix.trans h0.symm)

/-- **P4b (an uncovered winding loop can stay curved).** On the cycle `ZMod n` (n ≥ 1), a
constant edge log-rate `ℓ ≠ 0` has holonomy `n • ℓ ≠ 0` around the whole cycle. So curvature
survives on a loop that no local trader spans. -/
theorem winding_holonomy_ne_zero (n : ℕ) (hn : 0 < n) (ℓ : ℝ) (hℓ : ℓ ≠ 0) :
    (∑ _i : Fin n, ℓ) ≠ 0 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') hℓ

end SpatialMarket

namespace AMGM

/-- **S-KL (the AM–GM gap is a KL divergence).** For `x : Fin n → ℝ` with `n ≥ 1`:
log-sum-exp − mean − log n = KL(uniform ‖ softmax x). -/
theorem lse_sub_mean_eq_kl (n : ℕ) [NeZero n] (x : Fin n → ℝ) :
    Real.log (∑ i, Real.exp (x i)) - (∑ i, x i) / n - Real.log n
      = ∑ i, (1 / (n : ℝ)) *
          Real.log ((1 / (n : ℝ)) / (Real.exp (x i) / ∑ j, Real.exp (x j))) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hS : 0 < ∑ j, Real.exp (x j) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have hterm : ∀ i, Real.log ((1 / (n : ℝ)) / (Real.exp (x i) / ∑ j, Real.exp (x j)))
      = Real.log (∑ j, Real.exp (x j)) - x i - Real.log n := by
    intro i
    rw [Real.log_div (by positivity) (by positivity), Real.log_div (Real.exp_pos _).ne' hS.ne',
      Real.log_exp, one_div, Real.log_inv]
    ring
  simp only [hterm, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **S-KL+ (so the gap is nonnegative: AM–GM on `exp x`).** -/
theorem lse_sub_mean_nonneg (n : ℕ) [NeZero n] (x : Fin n → ℝ) :
    0 ≤ Real.log (∑ i, Real.exp (x i)) - (∑ i, x i) / n - Real.log n := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  set S := ∑ j, Real.exp (x j) with hSdef
  have hS : 0 < S := Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  rw [lse_sub_mean_eq_kl]
  have hkey : ∀ i, (1 / (n : ℝ)) * (1 - n * (Real.exp (x i) / S))
      ≤ (1 / (n : ℝ)) * Real.log ((1 / (n : ℝ)) / (Real.exp (x i) / S)) := by
    intro i
    have hpos : 0 < n * (Real.exp (x i) / S) := by positivity
    have hl := Real.log_le_sub_one_of_pos hpos
    have heq : Real.log ((1 / (n : ℝ)) / (Real.exp (x i) / S))
        = - Real.log (n * (Real.exp (x i) / S)) := by
      rw [← Real.log_inv]; congr 1; field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc (0 : ℝ) = ∑ i, (1 / (n : ℝ)) * (1 - n * (Real.exp (x i) / S)) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        rw [← hSdef, div_self hS.ne']
        field_simp
        ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => hkey i

end AMGM

namespace NashProduct

/-- **N1.** Nash product = (common interest)² − (conflict)². -/
theorem nash_product_eq (A B : ℝ) : A * B = ((A + B) / 2) ^ 2 - ((A - B) / 2) ^ 2 := by
  ring

/-- **N2.** Rescaling utility units inversely (a "boost") leaves the Nash product invariant. -/
theorem boost_invariant (A B η : ℝ) :
    (Real.exp η * A) * (Real.exp (-η) * B) = A * B := by
  have h : Real.exp η * Real.exp (-η) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  linear_combination (A * B) * h

/-- **N3.** The boost acts on (common, conflict) = ((A+B)/2, (A−B)/2) as a hyperbolic rotation. -/
theorem boost_hyperbolic_rotation (A B η : ℝ) :
    (Real.exp η * A + Real.exp (-η) * B) / 2
        = ((A + B) / 2) * Real.cosh η + ((A - B) / 2) * Real.sinh η ∧
    (Real.exp η * A - Real.exp (-η) * B) / 2
        = ((A + B) / 2) * Real.sinh η + ((A - B) / 2) * Real.cosh η := by
  rw [Real.cosh_eq, Real.sinh_eq]
  constructor <;> ring

end NashProduct

namespace Dagger

/-- **D1 (time reversal is contravariant).** The adjoint reverses the order of composition:
`(A B)ᴴ = Bᴴ Aᴴ`. -/
theorem dagger_contravariant {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.conjTranspose (A * B) = Matrix.conjTranspose B * Matrix.conjTranspose A :=
  Matrix.conjTranspose_mul A B

end Dagger
