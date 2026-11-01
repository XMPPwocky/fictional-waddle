/-
# Cellular automata with random update times: causal, linear, and lazily averaged

Cells on ℤ. At each step a schedule says which cells update; a cell that updates applies a local rule
to itself and its two neighbours, and a cell that does not keeps its value. Schedules may be chosen
arbitrarily (or at random) step by step, independently of the state.

PROVED
1. `light_cone_any_schedule`: for EVERY schedule, after n steps cell i depends only on the initial
   cells in [i − n, i + n]. Random clocks can slow influence down but never speed it up, and every
   observer, whatever its clock, agrees on what could have caused what.
2. `superposition`: with a linear rule (new value = a · left + b · self + c · right, complex
   coefficients), the evolution under any schedule is linear in the initial state.
3. `plane_wave_eigen`: when every cell updates, the plane wave x ↦ exp(i k x) is an eigenvector with
   eigenvalue λ(k) = a e^{−ik} + b + c e^{ik}: the response to each frequency is a single analytic
   function of k (the dispersion relation).
4. `mean_step`: if a cell updates with probability p, the expected next value is
   (1 − p) · current + p · (rule): random timing averages the rule with doing nothing.
2b. `superposition_smul`: and homogeneous: scaling the initial state scales the evolution.
5. `mean_eigenvalue`, `mean_stable`: so the averaged dynamics has eigenvalue 1 − p + p λ(k) on each
   plane wave, and if |λ(k)| ≤ 1 then |1 − p + p λ(k)| ≤ 1: random clocks preserve stability and act
   as a low-pass blend toward the identity.

INTERPRETED (not formalized)
- "Stochastic time" changes proper time (how often each cell ticks) but not causal structure: item 1
  holds pathwise for every schedule. On average (items 4–5) it is a slower linear system with the same
  light cone.
-/

import Mathlib

namespace StochasticTimeCA

variable {S : Type*}

/-- One step: cells with `mask i = true` apply the rule; the others keep their value. -/
def stepM (rule : S → S → S → S) (mask : ℤ → Bool) (f : ℤ → S) : ℤ → S :=
  fun i => if mask i then rule (f (i - 1)) (f i) (f (i + 1)) else f i

/-- Run n steps with a schedule of masks. -/
def run (rule : S → S → S → S) (masks : ℕ → ℤ → Bool) : ℕ → (ℤ → S) → (ℤ → S)
  | 0, f => f
  | n + 1, f => stepM rule (masks n) (run rule masks n f)

theorem light_cone_any_schedule (rule : S → S → S → S) (masks : ℕ → ℤ → Bool) (n : ℕ)
    (f g : ℤ → S) (i : ℤ) (h : ∀ j, i - n ≤ j → j ≤ i + n → f j = g j) :
    run rule masks n f i = run rule masks n g i := by
  induction n generalizing i with
  | zero => exact h i (by simp) (by simp)
  | succ n ih =>
    have hm : run rule masks n f (i - 1) = run rule masks n g (i - 1) :=
      ih (i - 1) fun j h1 h2 => h j (by push_cast; omega) (by push_cast; omega)
    have h0 : run rule masks n f i = run rule masks n g i :=
      ih i fun j h1 h2 => h j (by push_cast; omega) (by push_cast; omega)
    have hp : run rule masks n f (i + 1) = run rule masks n g (i + 1) :=
      ih (i + 1) fun j h1 h2 => h j (by push_cast; omega) (by push_cast; omega)
    simp only [run, stepM]
    rw [hm, h0, hp]

open Complex

/-- The linear rule a · left + b · self + c · right. -/
def lin (a b c : ℂ) : ℂ → ℂ → ℂ → ℂ := fun x y z => a * x + b * y + c * z

theorem superposition (a b c : ℂ) (masks : ℕ → ℤ → Bool) (n : ℕ) (f g : ℤ → ℂ) :
    run (lin a b c) masks n (f + g) = run (lin a b c) masks n f + run (lin a b c) masks n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    simp only [run, stepM, ih, Pi.add_apply, lin]
    split_ifs <;> ring

theorem superposition_smul (a b c : ℂ) (masks : ℕ → ℤ → Bool) (n : ℕ) (r : ℂ) (f : ℤ → ℂ) :
    run (lin a b c) masks n (r • f) = r • run (lin a b c) masks n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    simp only [run, stepM, ih, Pi.smul_apply, smul_eq_mul, lin]
    split_ifs <;> ring

/-- Plane wave with wavenumber k. -/
noncomputable def wave (k : ℝ) : ℤ → ℂ := fun x => exp (I * k * x)

noncomputable def lam (a b c : ℂ) (k : ℝ) : ℂ := a * exp (-(I * k)) + b + c * exp (I * k)

theorem plane_wave_eigen (a b c : ℂ) (k : ℝ) :
    stepM (lin a b c) (fun _ => true) (wave k) = lam a b c k • wave k := by
  funext x
  simp only [stepM, if_true, lin, wave, lam, Pi.smul_apply, smul_eq_mul]
  have e1 : I * (k : ℂ) * ((x - 1 : ℤ) : ℂ) = I * k * x + -(I * k) := by push_cast; ring
  have e2 : I * (k : ℂ) * ((x + 1 : ℤ) : ℂ) = I * k * x + I * k := by push_cast; ring
  rw [e1, e2, exp_add, exp_add]
  ring

/-- Expected next value at a cell that updates with probability p. -/
def meanStep (rule : ℂ → ℂ → ℂ → ℂ) (p : ℂ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun i => (1 - p) * stepM rule (fun _ => false) f i + p * stepM rule (fun _ => true) f i

theorem mean_step (a b c p : ℂ) (f : ℤ → ℂ) (i : ℤ) :
    meanStep (lin a b c) p f i = (1 - p) * f i + p * (a * f (i - 1) + b * f i + c * f (i + 1)) := by
  simp [meanStep, stepM, lin]

theorem mean_eigenvalue (a b c p : ℂ) (k : ℝ) :
    meanStep (lin a b c) p (wave k) = (1 - p + p * lam a b c k) • wave k := by
  funext x
  have h := congrFun (plane_wave_eigen a b c k) x
  simp only [meanStep, Pi.smul_apply, smul_eq_mul] at h ⊢
  rw [h]
  simp only [stepM, Bool.false_eq_true, if_false]
  ring

theorem mean_stable (lamk : ℂ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hl : ‖lamk‖ ≤ 1) :
    ‖(1 - (p : ℂ)) + p * lamk‖ ≤ 1 := by
  calc ‖(1 - (p : ℂ)) + p * lamk‖ ≤ ‖(1 - (p : ℂ))‖ + ‖(p : ℂ) * lamk‖ := norm_add_le _ _
    _ = (1 - p) + p * ‖lamk‖ := by
        rw [norm_mul]
        have h1 : ‖(1 - (p : ℂ))‖ = 1 - p := by
          rw [show (1 - (p : ℂ)) = ((1 - p : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
            Real.norm_of_nonneg (by linarith)]
        rw [h1, Complex.norm_real, Real.norm_of_nonneg hp0]
    _ ≤ (1 - p) + p * 1 := by gcongr
    _ = 1 := by ring

end StochasticTimeCA

#print axioms StochasticTimeCA.light_cone_any_schedule
#print axioms StochasticTimeCA.superposition
#print axioms StochasticTimeCA.superposition_smul
#print axioms StochasticTimeCA.plane_wave_eigen
#print axioms StochasticTimeCA.mean_step
#print axioms StochasticTimeCA.mean_eigenvalue
#print axioms StochasticTimeCA.mean_stable
