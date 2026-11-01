import Mathlib

/-!
# Causal barriers make things holomorphic

The established theorem behind this is Titchmarsh (1937) and Paley–Wiener: a response that vanishes before `t = 0`
has a Fourier transform holomorphic in a half-plane, and then its real and imaginary parts determine each other
(Kramers–Kronig). Below is the discrete-time version: a sequence `a n` is a response, and "causal" means it is
indexed by `ℕ`, so nothing exists before time 0.

* C1 `causal_is_holomorphic` (the barrier makes it holomorphic): a bounded causal sequence has a generating function
  `F z = ∑' n, a n * z ^ n` that is complex-differentiable on the whole open unit disk.
* C2 `no_barrier_no_convergence` (without the barrier, nothing): the simplest bounded two-sided sequence, `a n = 1` for
  every `n : ℤ`, has a two-sided series `∑ z ^ n` that is summable for NO nonzero `z`. Removing the barrier destroys
  convergence everywhere, not just holomorphy.
* C3 `barrier_pairs_phase_with_amplitude` (the phase is tied to the amplitude): for a causal polynomial on the unit
  circle, writing `a n = α n + i β n`, the real part is `∑ (α n cos nθ − β n sin nθ)` and the imaginary part is
  `∑ (α n sin nθ + β n cos nθ)`. The imaginary part is obtained from the real part by the mode-wise conjugation
  `cos nθ ↦ sin nθ`, `sin nθ ↦ −cos nθ`, which is the Hilbert transform. With uniqueness of trigonometric
  coefficients (orthogonality, not proved here), this is Kramers–Kronig for polynomials: knowing the real part on
  the barrier determines the phase.
-/

namespace CausalIsHolomorphic

open Complex

/-- **C1.** -/
theorem causal_is_holomorphic (a : ℕ → ℂ) (C : ℝ) (ha : ∀ n, ‖a n‖ ≤ C) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' n, a n * z ^ n) (Metric.ball 0 1) := by
  set p := FormalMultilinearSeries.ofScalars ℂ a with hp
  have hrad : (1 : ENNReal) ≤ p.radius := by
    have h := p.le_radius_of_bound C (r := 1) (fun n => by
      rw [hp, FormalMultilinearSeries.ofScalars_norm]; simpa using ha n)
    simpa using h
  have hpos : 0 < p.radius := lt_of_lt_of_le (by norm_num) hrad
  have hball := p.hasFPowerSeriesOnBall hpos
  have hdiff := hball.differentiableOn
  have heq : (fun z : ℂ => ∑' n, a n * z ^ n) = p.sum := by
    funext z
    have := FormalMultilinearSeries.ofScalars_sum_eq (E := ℂ) a z
    simp only [FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] at this
    rw [← hp] at this
    exact this.symm
  rw [heq]
  refine hdiff.mono ?_
  intro z hz
  have : ‖z‖ < 1 := by simpa using hz
  rw [Metric.mem_eball, edist_zero_right]
  calc (‖z‖₊ : ENNReal) < 1 := by exact_mod_cast this
    _ ≤ p.radius := hrad

/-- **C2.** -/
theorem no_barrier_no_convergence (z : ℂ) (hz : z ≠ 0) : ¬ Summable (fun n : ℤ => z ^ n) := by
  intro hs
  have ht := hs.tendsto_cofinite_zero
  have hpos : Filter.Tendsto (fun n : ℕ => z ^ (n : ℤ)) Filter.atTop (nhds 0) :=
    ht.comp (Nat.cast_injective.tendsto_cofinite.mono_left Nat.cofinite_eq_atTop.symm.le)
  have hneg : Filter.Tendsto (fun n : ℕ => z ^ (-(n : ℤ))) Filter.atTop (nhds 0) := by
    have inj : Function.Injective (fun n : ℕ => -(n : ℤ)) := fun x y h => by simpa using h
    exact ht.comp (inj.tendsto_cofinite.mono_left Nat.cofinite_eq_atTop.symm.le)
  have hprod := hpos.mul hneg
  rw [mul_zero] at hprod
  have hone : (fun n : ℕ => z ^ (n : ℤ) * z ^ (-(n : ℤ))) = fun _ => 1 := by
    funext n; rw [← zpow_add₀ hz]; simp
  rw [hone] at hprod
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hprod)

/-- **C3.** -/
theorem barrier_pairs_phase_with_amplitude (a : ℕ → ℂ) (N : ℕ) (θ : ℝ) :
    (∑ n ∈ Finset.range N, a n * exp ((n * θ : ℝ) * I)).re
        = ∑ n ∈ Finset.range N, ((a n).re * Real.cos (n * θ) - (a n).im * Real.sin (n * θ)) ∧
      (∑ n ∈ Finset.range N, a n * exp ((n * θ : ℝ) * I)).im
        = ∑ n ∈ Finset.range N, ((a n).re * Real.sin (n * θ) + (a n).im * Real.cos (n * θ)) := by
  have e : ∀ n : ℕ, exp ((n * θ : ℝ) * I) = (Real.cos (n * θ) : ℂ) + (Real.sin (n * θ) : ℂ) * I := by
    intro n; rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  constructor
  · rw [re_sum]; apply Finset.sum_congr rfl; intro n _; rw [e n]
    simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im]; ring
  · rw [im_sum]; apply Finset.sum_congr rfl; intro n _; rw [e n]
    simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im]; ring

end CausalIsHolomorphic
