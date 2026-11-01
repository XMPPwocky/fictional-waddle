import Mathlib

/-!
# Roots-of-unity games

PROVED
* (1) Twos: `twos_order_two` (`!!b = b`), `twos_no_fixed_point` (`!b ≠ b`).
* (2) Threes: `sigma_iter_three` (`σ^[3] = id`), `sigma_ne_id`, `sigma_iter_two_ne_id`,
  `beats_sigma` (`i` beats `σ i`), `P_pow_three` (`P ^ 3 = 1`),
  `P_charpoly` (`P.charpoly = X ^ 3 - 1`), `P_charpoly_isRoot_iff`
  (`μ` is a root of the characteristic polynomial iff `μ ^ 3 = 1`),
  `P_hasEigenvalue_iff` (`μ` is an eigenvalue of `P` iff `μ ^ 3 = 1`),
  `P_eigenvector` (`(1, μ, μ²)` is an explicit eigenvector for each cube root of unity `μ`).
* (3) Fours: `encode_step` (`encode (step p) = -I * encode p`),
  `encode_level` (`encode (level k) = (-I) ^ k * (1 + I)`), `step_iter_four`
  (`step^[4] = id`), `step_iter_two_ne_id`, and `step_iter_eq_id_iff`
  (`step^[n] = id ↔ 4 ∣ n`, i.e. the order is exactly 4).
* (4) Growth: `norm_exp_mul` (`‖exp (λ t) z₀‖ = exp (μ t) ‖z₀‖`), `norm_const_of_re_zero`
  (constant modulus when `μ = 0`), `strictMono_iff_re_pos`
  (`t ↦ ‖exp (λ t) z₀‖` strictly increasing iff `μ > 0`, for `z₀ ≠ 0`).

INTERPRETED
* "beats" on `Fin 3` is the relation `beats i j ↔ j = i + 1`.
* The 3×3 cyclic permutation matrix is `P i j = if j = σ i then 1 else 0`, so `(P v) i = v (i + 1)`.
* "Eigenvalues are the cube roots of unity" is stated both as the root set of the
  characteristic polynomial and as `Module.End.HasEigenvalue (Matrix.toLin' P) μ ↔ μ ^ 3 = 1`.
* The yomi state is `Bool × Bool` = (Matcher, Mismatcher); `step (a, b) = (b, !a)`;
  `level 0 = (true, true)`, `level (k + 1) = step (level k)`.
* `λ = μ + I ω` with `μ ω : ℝ`, time `t : ℝ`, and the trajectory is `exp (λ t) * z₀`.
-/

namespace RootsOfUnityGamesA

open Complex Polynomial

/-! ## (1) Twos -/

theorem twos_order_two (b : Bool) : (!!b) = b := Bool.not_not b

theorem twos_no_fixed_point : ∀ b : Bool, (!b) ≠ b := by decide

/-! ## (2) Threes -/

/-- `i` beats `j` iff `j = i + 1` (mod 3). -/
def beats (i j : Fin 3) : Prop := j = i + 1

/-- The cyclic shift on `Fin 3`. -/
def σ (i : Fin 3) : Fin 3 := i + 1

theorem beats_sigma (i : Fin 3) : beats i (σ i) := rfl

theorem sigma_iter_three : σ^[3] = id := by
  funext i; fin_cases i <;> rfl

theorem sigma_ne_id : σ ≠ id := by
  intro h
  have := congrFun h 0
  exact absurd this (by decide)

theorem sigma_iter_two_ne_id : σ^[2] ≠ id := by
  intro h
  have := congrFun h 0
  exact absurd this (by decide)

/-- The 3×3 cyclic permutation matrix over `ℂ`. -/
def P : Matrix (Fin 3) (Fin 3) ℂ := Matrix.of fun i j => if j = σ i then 1 else 0

theorem P_pow_three : P ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, P, σ]

theorem P_charpoly : P.charpoly = X ^ 3 - 1 := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp [P, σ]
  ring

theorem P_charpoly_isRoot_iff (μ : ℂ) : P.charpoly.IsRoot μ ↔ μ ^ 3 = 1 := by
  rw [P_charpoly]
  simp [sub_eq_zero]

theorem P_eigenvector (μ : ℂ) (hμ : μ ^ 3 = 1) :
    P.mulVec ![1, μ, μ ^ 2] = μ • ![1, μ, μ ^ 2] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, P, σ]
  · ring
  · rw [← hμ]; ring

theorem P_hasEigenvalue_iff (μ : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' P) μ ↔ μ ^ 3 = 1 := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin',
    Matrix.mem_spectrum_iff_isRoot_charpoly]
  exact P_charpoly_isRoot_iff μ

/-! ## (3) Fours -/

/-- One level deeper of reading: the Matcher copies the Mismatcher's previous action,
the Mismatcher negates the Matcher's previous action. -/
def step : Bool × Bool → Bool × Bool
  | (a, b) => (b, !a)

/-- The yomi recursion. -/
def level : ℕ → Bool × Bool
  | 0 => (true, true)
  | k + 1 => step (level k)

/-- `true ↦ 1`, `false ↦ -1`. -/
def enc : Bool → ℂ
  | true => 1
  | false => -1

/-- `z = enc a + I * enc b`. -/
def encode (p : Bool × Bool) : ℂ := enc p.1 + I * enc p.2

theorem encode_step (a b : Bool) : encode (step (a, b)) = -I * encode (a, b) := by
  cases a <;> cases b <;>
    simp [encode, step, enc] <;> ring_nf <;> simp [I_sq] <;> ring

theorem encode_level (k : ℕ) : encode (level k) = (-I) ^ k * (1 + I) := by
  induction k with
  | zero => simp [level, encode, enc]
  | succ k ih =>
    show encode (step ((level k).1, (level k).2)) = _
    rw [encode_step]
    change -I * encode (level k) = _
    rw [ih, pow_succ]
    ring

theorem step_iter_four : step^[4] = id := by
  funext p; obtain ⟨a, b⟩ := p; cases a <;> cases b <;> rfl

theorem step_iter_two_ne_id : step^[2] ≠ id := by
  intro h
  have := congrFun h (true, true)
  exact absurd this (by decide)

theorem step_iter_eq_id_iff (n : ℕ) : step^[n] = id ↔ 4 ∣ n := by
  have key : step^[n] = step^[n % 4] := by
    conv_lhs => rw [← Nat.mod_add_div n 4]
    rw [Function.iterate_add, Function.iterate_mul, step_iter_four, Function.iterate_id]
    rfl
  rw [key, Nat.dvd_iff_mod_eq_zero]
  have hlt : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize n % 4 = r at hlt ⊢
  interval_cases r
  · simp
  · refine iff_of_false (fun h => ?_) (by norm_num)
    exact absurd (congrFun h (true, true)) (by decide)
  · refine iff_of_false (fun h => ?_) (by norm_num)
    exact absurd (congrFun h (true, true)) (by decide)
  · refine iff_of_false (fun h => ?_) (by norm_num)
    exact absurd (congrFun h (true, true)) (by decide)

/-! ## (4) Growth needs a real part -/

theorem norm_exp_mul (μ ω t : ℝ) (z₀ : ℂ) :
    ‖exp (((μ : ℂ) + I * ω) * t) * z₀‖ = Real.exp (μ * t) * ‖z₀‖ := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp

theorem norm_const_of_re_zero (ω t : ℝ) (z₀ : ℂ) :
    ‖exp ((((0 : ℝ) : ℂ) + I * ω) * t) * z₀‖ = ‖z₀‖ := by
  rw [norm_exp_mul]; simp

theorem strictMono_iff_re_pos (μ ω : ℝ) (z₀ : ℂ) (hz : z₀ ≠ 0) :
    StrictMono (fun t : ℝ => ‖exp (((μ : ℂ) + I * ω) * t) * z₀‖) ↔ 0 < μ := by
  simp only [norm_exp_mul]
  have hn : 0 < ‖z₀‖ := norm_pos_iff.mpr hz
  constructor
  · intro h
    by_contra hμ
    push Not at hμ
    have h01 := h (show (0 : ℝ) < 1 by norm_num)
    simp only [mul_zero, Real.exp_zero, one_mul, mul_one] at h01
    have : Real.exp μ ≤ 1 := Real.exp_le_one_iff.mpr hμ
    nlinarith
  · intro hμ s t hst
    simp only
    have : Real.exp (μ * s) < Real.exp (μ * t) :=
      Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hst hμ)
    exact mul_lt_mul_of_pos_right this hn

end RootsOfUnityGamesA
