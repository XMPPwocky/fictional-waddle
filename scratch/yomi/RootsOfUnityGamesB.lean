import Mathlib

/-!
# Roots of unity in reading games

PROVED
* `twos_order`, `twos_no_fixed`: Bool negation is an involution with no fixed point.
* `sigma_beats`: on `Fin 3`, with `beats i j :↔ j = i + 1`, every `i` beats `σ i`.
* `sigma_iter_three`, `sigma_ne_id`, `sigma_iter_two_ne_id`: `σ^[3] = id`, `σ ≠ id`, `σ^[2] ≠ id`.
* `P_pow_three`: the cyclic permutation matrix `P` over `ℂ` satisfies `P ^ 3 = 1`.
* `P_charpoly`: `P.charpoly = X ^ 3 - 1`.
* `P_mem_spectrum_iff`, `P_spectrum`: `μ ∈ spectrum ℂ P ↔ μ ^ 3 = 1`.
* `enc_step`: `zenc (step p) = -I * zenc p` for every Bool pair `p`.
* `enc_level`: `zenc (level k) = (-I) ^ k * (1 + I)`.
* `step_iter_four`, `step_iter_two_ne_id`, `step_ne_id`, `step_iter_ne_id_of_lt_four`:
  `step` has order exactly 4 on `Bool × Bool`.
* `norm_exp_mul`: `‖exp ((μ + I ω) t) z₀‖ = exp (μ t) ‖z₀‖`.
* `norm_const_of_re_zero`: for `μ = 0` the modulus is constant in `t`.
* `strictMono_iff_re_pos`: for `z₀ ≠ 0`, `t ↦ ‖exp ((μ + I ω) t) z₀‖` is strictly increasing
  iff `0 < μ`.

INTERPRETED
* Level 2 (Bool): the opponent's best response to a prediction is its negation, which has order 2
  and no fixed point; a prediction of it is always wrong.
* Level 3 (rock-paper-scissors on `Fin 3`): going one level deeper is the shift `σ`, of order 3;
  its matrix has the cube roots of unity as eigenvalues.
* Level 4 (Matcher/Mismatcher pair): one yomi step multiplies the encoded state by `-i`, a
  primitive fourth root of unity; the joint recursion is a pure rotation of order 4.
* Growth: a linear flow `exp (λ t)` changes modulus only through `Re λ`; pure rotation
  (`Re λ = 0`) conserves modulus, and modulus grows iff `Re λ > 0`.
-/

namespace RootsOfUnityGamesB

open Complex Polynomial

/-! ## Twos -/

theorem twos_order (b : Bool) : (!!b) = b := by cases b <;> rfl

theorem twos_no_fixed (b : Bool) : (!b) ≠ b := by cases b <;> decide

/-! ## Threes -/

/-- `i` beats `j` iff `j = i + 1` (mod 3). -/
def beats (i j : Fin 3) : Prop := j = i + 1

/-- Cyclic shift on `Fin 3`. -/
def sigma (i : Fin 3) : Fin 3 := i + 1

theorem sigma_beats (i : Fin 3) : beats i (sigma i) := rfl

theorem sigma_iter_three : sigma^[3] = id := by
  funext i; fin_cases i <;> rfl

theorem sigma_ne_id : sigma ≠ id := by
  intro h
  have := congrFun h 0
  exact absurd this (by decide)

theorem sigma_iter_two_ne_id : sigma^[2] ≠ id := by
  intro h
  have := congrFun h 0
  exact absurd this (by decide)

/-- The 3×3 cyclic permutation matrix: `P i j = 1` iff `j = i + 1`. -/
def P : Matrix (Fin 3) (Fin 3) ℂ := fun i j => if j = i + 1 then 1 else 0

theorem P_pow_three : P ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, P]

theorem P_charpoly : P.charpoly = X ^ 3 - 1 := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp [P]
  ring

theorem P_mem_spectrum_iff (μ : ℂ) : μ ∈ spectrum ℂ P ↔ μ ^ 3 = 1 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, P_charpoly]
  simp [sub_eq_zero]

theorem P_spectrum : spectrum ℂ P = {μ : ℂ | μ ^ 3 = 1} := by
  ext μ; exact P_mem_spectrum_iff μ

/-! ## Fours -/

/-- One yomi level: the Matcher copies the Mismatcher's previous action, the Mismatcher negates
the Matcher's previous action. -/
def step (p : Bool × Bool) : Bool × Bool := (p.2, !p.1)

/-- The yomi recursion. -/
def level : ℕ → Bool × Bool
  | 0 => (true, true)
  | k + 1 => step (level k)

/-- `true ↦ 1`, `false ↦ -1`. -/
def enc (b : Bool) : ℂ := if b then 1 else -1

/-- `z = enc a + I * enc b`. -/
def zenc (p : Bool × Bool) : ℂ := enc p.1 + I * enc p.2

theorem enc_step (p : Bool × Bool) : zenc (step p) = -I * zenc p := by
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;> simp [zenc, step, enc] <;> ring_nf <;> simp [I_sq] <;> ring

theorem enc_step' (a b : Bool) : zenc (step (a, b)) = -I * zenc (a, b) := enc_step (a, b)

theorem enc_level (k : ℕ) : zenc (level k) = (-I) ^ k * (1 + I) := by
  induction k with
  | zero => simp [level, zenc, enc]
  | succ k ih => rw [level, enc_step, ih, pow_succ]; ring

theorem step_iter_four : step^[4] = id := by
  funext p; obtain ⟨a, b⟩ := p; cases a <;> cases b <;> rfl

theorem step_iter_two_ne_id : step^[2] ≠ id := by
  intro h
  have := congrFun h (true, true)
  exact absurd this (by decide)

theorem step_ne_id : step ≠ id := by
  intro h
  have := congrFun h (true, true)
  exact absurd this (by decide)

theorem step_iter_three_ne_id : step^[3] ≠ id := by
  intro h
  have := congrFun h (true, true)
  exact absurd this (by decide)

theorem step_iter_ne_id_of_lt_four {n : ℕ} (h0 : 0 < n) (h4 : n < 4) : step^[n] ≠ id := by
  interval_cases n
  · exact step_ne_id
  · exact step_iter_two_ne_id
  · exact step_iter_three_ne_id

/-! ## Growth needs a real part -/

theorem norm_exp_mul (μ ω t : ℝ) (z₀ : ℂ) :
    ‖exp ((μ + I * ω) * t) * z₀‖ = Real.exp (μ * t) * ‖z₀‖ := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp

theorem norm_const_of_re_zero (ω t : ℝ) (z₀ : ℂ) :
    ‖exp (((0 : ℝ) + I * ω) * t) * z₀‖ = ‖z₀‖ := by
  rw [norm_exp_mul]; simp

theorem strictMono_iff_re_pos (μ ω : ℝ) {z₀ : ℂ} (hz : z₀ ≠ 0) :
    StrictMono (fun t : ℝ => ‖exp ((μ + I * ω) * t) * z₀‖) ↔ 0 < μ := by
  have hn : 0 < ‖z₀‖ := norm_pos_iff.mpr hz
  simp only [norm_exp_mul]
  constructor
  · intro h
    have h01 := h (show (0 : ℝ) < 1 by norm_num)
    simp only [mul_zero, Real.exp_zero, one_mul, mul_one] at h01
    have : 1 < Real.exp μ := by
      by_contra hc
      have hc' := not_lt.mp hc
      nlinarith
    exact Real.one_lt_exp_iff.mp this
  · intro hμ s t hst
    have : Real.exp (μ * s) < Real.exp (μ * t) :=
      Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hst hμ)
    exact mul_lt_mul_of_pos_right this hn

end RootsOfUnityGamesB
