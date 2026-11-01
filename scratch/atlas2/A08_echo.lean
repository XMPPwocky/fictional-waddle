import Mathlib

/-!
# A08 — Mutual-prediction echo (proofs)

Two linear best responses `x = a*y + c`, `y = b*x + d` with `a*b ≠ 1`.

**Proved (in `A08_echo.lean`):**
* the unique fixed point is `x* = (a d + c)/(1 - a b)`, `y* = (b c + d)/(1 - a b)`;
* `∂x*/∂d = a/(1 - a b)` and `∂y*/∂d = 1/(1 - a b)` (as `HasDerivAt` in `d`);
* the composed iteration `x_{n+1} = a (b x_n + d) + c` has error
  `x_n - x* = (a b)^n (x_0 - x*)` exactly;
* if `|a b| < 1` it converges to `x*`;
* if `|a b| > 1` and `x_0 ≠ x*`, `|x_n - x*| → ∞` and `|x_n| → ∞`.
* (added by second agent) if `|a b| < 1`, `a/(1 - a b) = ∑_k a (a b)^k` (`HasSum`):
  the multiplier is literally the geometric series of re-predictions.

**Interpretation (not proved):** `a/(1 - a b)` is the "echo" multiplier — a shock `d`
to the other side's intercept reaches `x` directly with weight `a` and is amplified by the
geometric series `∑ (a b)^k` of mutual re-prediction. Nothing here models agents; it is
two affine maps.
-/

open Filter Topology

namespace A08Echo

/-- Fixed-point `x`-coordinate of the echo system. -/
noncomputable def xStar (a b c d : ℝ) : ℝ := (a * d + c) / (1 - a * b)

/-- Fixed-point `y`-coordinate of the echo system. -/
noncomputable def yStar (a b c d : ℝ) : ℝ := (b * c + d) / (1 - a * b)

/-- The `(x, y)` solving both best responses is exactly `(xStar, yStar)`. -/
theorem fixed_point_iff (a b c d : ℝ) (h : a * b ≠ 1) (x y : ℝ) :
    (x = a * y + c ∧ y = b * x + d) ↔ (x = xStar a b c d ∧ y = yStar a b c d) := by
  have h1 : (1 - a * b) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨?_, ?_⟩
    · unfold xStar
      rw [eq_div_iff h1]
      linear_combination hx + a * hy
    · unfold yStar
      rw [eq_div_iff h1]
      linear_combination hy + b * hx
  · rintro ⟨rfl, rfl⟩
    unfold xStar yStar
    constructor
    · field_simp
      ring
    · rw [eq_comm, eq_div_iff h1, add_mul, mul_assoc, div_mul_cancel₀ _ h1]
      ring

/-- Existence and uniqueness packaged as `∃!`. -/
theorem fixed_point_existsUnique (a b c d : ℝ) (h : a * b ≠ 1) :
    ∃! p : ℝ × ℝ, p.1 = a * p.2 + c ∧ p.2 = b * p.1 + d := by
  refine ⟨(xStar a b c d, yStar a b c d), (fixed_point_iff a b c d h _ _).2 ⟨rfl, rfl⟩, ?_⟩
  intro p hp
  obtain ⟨h1, h2⟩ := (fixed_point_iff a b c d h p.1 p.2).1 hp
  ext
  · exact h1
  · exact h2

/-- `∂x*/∂d = a / (1 - a b)`. -/
theorem hasDerivAt_xStar_d (a b c d : ℝ) (_h : a * b ≠ 1) :
    HasDerivAt (fun d' => xStar a b c d') (a / (1 - a * b)) d := by
  have := (((hasDerivAt_id d).const_mul a).add_const c).div_const (1 - a * b)
  simpa [xStar] using this

/-- `∂y*/∂d = 1 / (1 - a b)`. -/
theorem hasDerivAt_yStar_d (a b c d : ℝ) (_h : a * b ≠ 1) :
    HasDerivAt (fun d' => yStar a b c d') (1 / (1 - a * b)) d := by
  have := ((hasDerivAt_id d).const_add (b * c)).div_const (1 - a * b)
  simpa [yStar] using this

/-- The composed best-response iteration `x_{n+1} = a (b x_n + d) + c`. -/
def iter (a b c d x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | n + 1 => a * (b * iter a b c d x0 n + d) + c

/-- `x*` is a fixed point of the composed map. -/
theorem xStar_fixed (a b c d : ℝ) (h : a * b ≠ 1) :
    a * (b * xStar a b c d + d) + c = xStar a b c d := by
  have h1 : (1 - a * b) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  unfold xStar
  field_simp
  ring

/-- Exact error law: `x_n - x* = (a b)^n (x_0 - x*)`. -/
theorem iter_sub_xStar (a b c d x0 : ℝ) (h : a * b ≠ 1) (n : ℕ) :
    iter a b c d x0 n - xStar a b c d = (a * b) ^ n * (x0 - xStar a b c d) := by
  induction n with
  | zero => simp [iter]
  | succ n ih =>
    have hf := xStar_fixed a b c d h
    rw [iter, pow_succ]
    linear_combination (a * b) * ih + hf

/-- Absolute error law: `|x_n - x*| = |a b|^n |x_0 - x*|`. -/
theorem abs_iter_sub_xStar (a b c d x0 : ℝ) (h : a * b ≠ 1) (n : ℕ) :
    |iter a b c d x0 n - xStar a b c d| = |a * b| ^ n * |x0 - xStar a b c d| := by
  rw [iter_sub_xStar a b c d x0 h n, abs_mul, abs_pow]

/-- Convergence when `|a b| < 1`. -/
theorem iter_tendsto (a b c d x0 : ℝ) (h : |a * b| < 1) :
    Tendsto (iter a b c d x0) atTop (𝓝 (xStar a b c d)) := by
  have hab : a * b ≠ 1 := by
    intro e
    rw [e] at h
    simp at h
  have h2 := ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one h).mul_const
    (x0 - xStar a b c d)).add_const (xStar a b c d)
  rw [zero_mul, zero_add] at h2
  refine h2.congr (fun n => ?_)
  have := iter_sub_xStar a b c d x0 hab n
  linarith

/-- Divergence of the error when `|a b| > 1` and `x_0 ≠ x*`. -/
theorem iter_error_tendsto_atTop (a b c d x0 : ℝ) (h : 1 < |a * b|)
    (hx : x0 ≠ xStar a b c d) :
    Tendsto (fun n => |iter a b c d x0 n - xStar a b c d|) atTop atTop := by
  have hab : a * b ≠ 1 := by
    intro e
    rw [e] at h
    simp at h
  have hpos : 0 < |x0 - xStar a b c d| := abs_pos.mpr (sub_ne_zero.mpr hx)
  have h2 := (tendsto_pow_atTop_atTop_of_one_lt h).atTop_mul_const hpos
  refine h2.congr (fun n => ?_)
  rw [abs_iter_sub_xStar a b c d x0 hab n]

/-- Divergence in absolute value when `|a b| > 1` and `x_0 ≠ x*`. -/
theorem iter_abs_tendsto_atTop (a b c d x0 : ℝ) (h : 1 < |a * b|)
    (hx : x0 ≠ xStar a b c d) :
    Tendsto (fun n => |iter a b c d x0 n|) atTop atTop := by
  have h2 := tendsto_atTop_add_const_right atTop (-|xStar a b c d|)
    (iter_error_tendsto_atTop a b c d x0 h hx)
  refine tendsto_atTop_mono (fun n => ?_) h2
  have := abs_sub (iter a b c d x0 n) (xStar a b c d)
  linarith

/-- **Added (second agent).** When `|a b| < 1`, the echo multiplier `a/(1 - a b)` is the
sum of the series `∑_k a (a b)^k`. Proved: the `HasSum`. Interpretation (not proved): term `k`
is the contribution of the `k`-th round of mutual re-prediction. -/
theorem hasSum_echo_multiplier (a b : ℝ) (h : |a * b| < 1) :
    HasSum (fun k : ℕ => a * (a * b) ^ k) (a / (1 - a * b)) := by
  rw [div_eq_mul_inv]
  exact (hasSum_geometric_of_abs_lt_one h).mul_left a

/-! ### Concrete instantiations (sanity checks, second agent) -/

/-- `a = b = 1/2`, `c = d = 1`: fixed point `(2, 2)`. -/
example : xStar (1/2) (1/2) 1 1 = 2 ∧ yStar (1/2) (1/2) 1 1 = 2 := by
  unfold xStar yStar; norm_num

/-- The main theorem instantiated: `(2, 2)` is the unique solution, and it is a solution. -/
example : (2 : ℝ) = 1/2 * 2 + 1 ∧ (2 : ℝ) = 1/2 * 2 + 1 :=
  (fixed_point_iff (1/2) (1/2) 1 1 (by norm_num) 2 2).2
    ⟨by unfold xStar; norm_num, by unfold yStar; norm_num⟩

/-- Derivative instantiated: `∂x*/∂d = (1/2)/(3/4) = 2/3`. -/
example (d : ℝ) : HasDerivAt (fun d' => xStar (1/2) (1/2) 1 d') (2/3) d := by
  have := hasDerivAt_xStar_d (1/2) (1/2) 1 d (by norm_num)
  convert this using 1; norm_num

/-- Convergence instantiated: from any `x_0`, iterates go to `2`. -/
example (x0 : ℝ) : Tendsto (iter (1/2) (1/2) 1 1 x0) atTop (𝓝 2) := by
  have := iter_tendsto (1/2) (1/2) 1 1 x0 (by norm_num [abs_of_pos])
  convert this using 2; unfold xStar; norm_num

/-- Divergence instantiated: `a = b = 2`, `c = d = 0` gives `x* = 0`; from `x_0 = 1`, `|x_n| → ∞`. -/
example : Tendsto (fun n => |iter 2 2 0 0 1 n|) atTop atTop :=
  iter_abs_tendsto_atTop 2 2 0 0 1 (by norm_num) (by unfold xStar; norm_num)

/-- The hypothesis `a b ≠ 1` is not decorative: with `a = b = 1`, `c = d = 0`, both `(0,0)` and
`(1,1)` solve the system, so uniqueness fails. -/
example : ¬ ∃! p : ℝ × ℝ, p.1 = 1 * p.2 + 0 ∧ p.2 = 1 * p.1 + 0 := by
  rintro ⟨p, _, hu⟩
  have h0 := hu (0, 0) (by norm_num)
  have h1 := hu (1, 1) (by norm_num)
  have := h0.trans h1.symm
  simp [Prod.ext_iff] at this

/-- Series instantiated: `∑ (1/2)(1/4)^k = 2/3`. -/
example : HasSum (fun k : ℕ => (1/2 : ℝ) * (1/2 * (1/2)) ^ k) (2/3) := by
  have := hasSum_echo_multiplier (1/2) (1/2) (by norm_num [abs_of_pos])
  convert this using 1; norm_num

end A08Echo
