import Mathlib

/-!
# A06 — Pólya urn martingale (proofs)

All quantities are real numbers `a b : ℝ` (red, blue counts). Every theorem assumes
`0 < a + b`; only `polya_inc_var_nonneg` also assumes `0 ≤ a`, `0 ≤ b` (the algebraic
identities hold without them). Natural-number urns are covered by casting
(see `polya_kstep_nat`).

Statement change log: the first draft also assumed `0 ≤ a` and `0 ≤ b` in
`polya_kstep`, `polya_inc_var`, `polya_inc_var_frac`, `polya_inc_var_le`,
`polya_inc_var_le_inv_sq`; those hypotheses were unused by the proofs and were removed in
both files (a strict strengthening). They remain in `polya_inc_var_nonneg`, where they are
needed. The probabilistic reading still requires `a, b ≥ 0`.

Adversarial-pass additions (second agent): concrete `example`s (a hand-unfolded 3-step
value, an instance of `polya_kstep_nat`, and `expFrac 1 = nextFrac`), plus one generalization:
`expFracC c` (each draw adds `c ≥ 0` balls of the drawn colour), with
`expFracC_one : expFracC 1 = expFrac` and `polya_kstep_reinforce` (the `k`-step martingale
identity for every reinforcement `c ≥ 0`). No earlier statement was changed in this pass.
-/

namespace Atlas2.A06

/-- Expected red fraction after one Pólya draw from an urn with `a` red, `b` blue. -/
noncomputable def nextFrac (a b : ℝ) : ℝ :=
  (a / (a + b)) * ((a + 1) / (a + b + 1)) + (b / (a + b)) * (a / (a + b + 1))

/-- Expected red fraction after `k` Pólya draws, defined by first-step recursion. -/
noncomputable def expFrac : ℕ → ℝ → ℝ → ℝ
  | 0, a, b => a / (a + b)
  | k + 1, a, b => (a / (a + b)) * expFrac k (a + 1) b + (b / (a + b)) * expFrac k a (b + 1)

/-- Variance of the one-step increment of the red fraction. -/
noncomputable def incVar (a b : ℝ) : ℝ :=
  (a / (a + b)) * ((a + 1) / (a + b + 1) - a / (a + b)) ^ 2
    + (b / (a + b)) * (a / (a + b + 1) - a / (a + b)) ^ 2

/-- **Proved:** for real `a b` with `a + b > 0`, the algebraic identity
`(a/(a+b))·(a+1)/(a+b+1) + (b/(a+b))·a/(a+b+1) = a/(a+b)`.
**Interpretation:** for a genuine urn (`a, b ≥ 0`) the left side is the expected red
fraction after one draw, so the red fraction is a one-step martingale. Nonnegativity is
not needed for the identity. -/
theorem polya_one_step (a b : ℝ) (hab : 0 < a + b) : nextFrac a b = a / (a + b) := by
  have h1 : a + b + 1 ≠ 0 := by linarith
  have h2 : a + b ≠ 0 := hab.ne'
  unfold nextFrac
  field_simp
  ring

/-- **Proved:** the first-step recursion `expFrac k a b` equals `a/(a+b)` for every `k`,
whenever `a + b > 0` (induction on `k`, generalizing `a b`).
**Interpretation:** the expected red fraction after `k` Pólya draws equals the initial
fraction (martingale property, `k`-step). `expFrac` is defined by conditioning on the first
draw; that this recursion equals the path-space expectation is the modelling step, not
derived here from a measure-theoretic Markov chain. -/
theorem polya_kstep (k : ℕ) (a b : ℝ) (hab : 0 < a + b) :
    expFrac k a b = a / (a + b) := by
  induction k generalizing a b with
  | zero => simp [expFrac]
  | succ k ih =>
    have e1 := ih (a + 1) b (by linarith)
    have e2 := ih a (b + 1) (by linarith)
    simp only [expFrac, e1, e2]
    have h1 : a + b + 1 ≠ 0 := by linarith
    have h1' : a + 1 + b ≠ 0 := by linarith
    have h1'' : a + (b + 1) ≠ 0 := by linarith
    have h2 : a + b ≠ 0 := hab.ne'
    field_simp
    ring

/-- **Proved:** the `k`-step identity for natural-number ball counts (cast to `ℝ`). -/
theorem polya_kstep_nat (k a b : ℕ) (hab : 0 < a + b) :
    expFrac k (a : ℝ) (b : ℝ) = (a : ℝ) / ((a : ℝ) + b) := by
  have hab' : (0 : ℝ) < (a : ℝ) + b := by exact_mod_cast hab
  exact polya_kstep k a b hab'

/-- **Proved:** the one-step increment of the fraction has (weighted) mean zero. -/
theorem polya_inc_mean_zero (a b : ℝ) (hab : 0 < a + b) :
    (a / (a + b)) * ((a + 1) / (a + b + 1) - a / (a + b))
      + (b / (a + b)) * (a / (a + b + 1) - a / (a + b)) = 0 := by
  have h1 : a + b + 1 ≠ 0 := by linarith
  have h2 : a + b ≠ 0 := hab.ne'
  field_simp
  ring

/-- **Proved:** with `N = a + b > 0`, the weighted second moment of the increment
(equal to its variance since the mean is zero, `polya_inc_mean_zero`) is
`a b / (N² (N+1)²)`. -/
theorem polya_inc_var (a b : ℝ) (hab : 0 < a + b) :
    incVar a b = a * b / ((a + b) ^ 2 * (a + b + 1) ^ 2) := by
  have h1 : a + b + 1 ≠ 0 := by linarith
  have h2 : a + b ≠ 0 := hab.ne'
  unfold incVar
  field_simp
  ring

/-- **Proved:** equivalently, with `p = a/N`, the increment variance is `p(1-p)/(N+1)²`. -/
theorem polya_inc_var_frac (a b : ℝ) (hab : 0 < a + b) :
    incVar a b = (a / (a + b)) * (1 - a / (a + b)) / (a + b + 1) ^ 2 := by
  rw [polya_inc_var a b hab]
  have h1 : a + b + 1 ≠ 0 := by linarith
  have h2 : a + b ≠ 0 := hab.ne'
  field_simp
  ring

/-- **Proved:** the increment variance is at most `1/(4 (N+1)²)` (from `4ab ≤ (a+b)²`).
**Interpretation:** the one-step variance decays like `1/N²`, uniformly in the fraction;
by `polya_inc_var_frac` it is exactly `p(1-p)/(N+1)²`, so `Θ(1/N²)` at fixed `p ∈ (0,1)`. -/
theorem polya_inc_var_le (a b : ℝ) (hab : 0 < a + b) :
    incVar a b ≤ 1 / (4 * (a + b + 1) ^ 2) := by
  rw [polya_inc_var a b hab]
  have h1 : 0 < a + b + 1 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg (a + b + 1)) (sq_nonneg (a - b))]

/-- **Proved:** the increment variance is at most `1/(4 N²)`. -/
theorem polya_inc_var_le_inv_sq (a b : ℝ) (hab : 0 < a + b) :
    incVar a b ≤ 1 / (4 * (a + b) ^ 2) := by
  refine le_trans (polya_inc_var_le a b hab) ?_
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- **Proved:** for a genuine urn (`a, b ≥ 0`) the increment variance is nonnegative. -/
theorem polya_inc_var_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    0 ≤ incVar a b := by
  have h1 : 0 < a + b + 1 := by linarith
  unfold incVar
  positivity

/-- Expected red fraction after `k` draws of a generalized Pólya urn that adds `c` balls of
the drawn colour (first-step recursion). `c = 1` is the classical urn (`expFracC_one`). -/
noncomputable def expFracC (c : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, a, b => a / (a + b)
  | k + 1, a, b =>
      (a / (a + b)) * expFracC c k (a + c) b + (b / (a + b)) * expFracC c k a (b + c)

/-- **Proved:** with reinforcement `c = 1` the generalized recursion is the classical one. -/
theorem expFracC_one (k : ℕ) (a b : ℝ) : expFracC 1 k a b = expFrac k a b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih => simp only [expFracC, expFrac, ih]

/-- **Proved (generalization of `polya_kstep`):** for every reinforcement `c ≥ 0` and every
`k`, `expFracC c k a b = a/(a+b)` whenever `a + b > 0`.
**Interpretation:** the red fraction stays a martingale when each draw adds `c` balls of
the drawn colour, for any `c ≥ 0`, including non-integer `c` and `c = 0` (drawing with
replacement and no reinforcement). `c ≥ 0` is used only to keep `a + b + c > 0` along every
path. -/
theorem polya_kstep_reinforce (c : ℝ) (hc : 0 ≤ c) (k : ℕ) (a b : ℝ) (hab : 0 < a + b) :
    expFracC c k a b = a / (a + b) := by
  induction k generalizing a b with
  | zero => simp [expFracC]
  | succ k ih =>
    have e1 := ih (a + c) b (by linarith)
    have e2 := ih a (b + c) (by linarith)
    simp only [expFracC, e1, e2]
    have h1 : a + b + c ≠ 0 := by linarith
    have h1' : a + c + b ≠ 0 := by linarith
    have h1'' : a + (b + c) ≠ 0 := by linarith
    have h2 : a + b ≠ 0 := hab.ne'
    field_simp
    ring

/-! ### Concrete sanity checks (not part of the spec's statements) -/

/-- The 3-step value for the urn (1 red, 2 blue), computed by unfolding the recursion
directly (independent of `polya_kstep`). -/
example : expFrac 3 (1 : ℝ) 2 = 1 / 3 := by
  simp only [expFrac]; norm_num

/-- `polya_kstep_nat` instantiated: after 10 draws from (1 red, 2 blue) the expected red
fraction is 1/3. -/
example : expFrac 10 ((1 : ℕ) : ℝ) ((2 : ℕ) : ℝ) = 1 / 3 := by
  rw [polya_kstep_nat 10 1 2 (by norm_num)]; norm_num

/-- One step of the recursion is `nextFrac`, so `polya_kstep` at `k = 1` is the spec's
one-step identity. -/
example (a b : ℝ) : expFrac 1 a b = nextFrac a b := by
  simp only [expFrac, nextFrac]; ring_nf

/-- Reinforcement `c = 3`, two draws from (2 red, 5 blue), unfolded directly. -/
example : expFracC 3 2 (2 : ℝ) 5 = 2 / 7 := by
  simp only [expFracC]; norm_num

end Atlas2.A06
