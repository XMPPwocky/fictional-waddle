import Mathlib

/-!
# A09 — The 90-degree rule (proofs)

Quadratic `f(x) = ½ xᵀ Q x - bᵀ x` on `Fin n → ℝ`, gradient `g(x) = Q x - b`.

## What is proved
* `grad_step_inner`: `g(x - α g)ᵀ g = gᵀg - α gᵀQg` for any square real `Q` (no hypotheses).
* `phi_expand`: for `Qᵀ = Q`, `φ(α) = f(x) - α gᵀg + (α²/2) gᵀQg`.
* `phi_hasDerivAt`: for `Qᵀ = Q`, `φ'(α) = -g(x - α g)ᵀ g`.
* `f_line_hasDerivAt` (added by the second agent): for `Qᵀ = Q` and any direction `v`,
  `d/dt f(x + t v) = g(x + t v)ᵀ v`, i.e. `grad` is the directional gradient of `f`.
* For `Q.PosDef` and `g ≠ 0`: `gᵀQg > 0`, `α* > 0`, `φ(α*) ≤ φ(α)` for all `α` (and strictly
  for `α ≠ α*`), `g(x - α* g)ᵀ g = 0`, the inner product is `> 0` for `α < α*`, `< 0` for
  `α > α*`, and `sign(g(x - α g)ᵀ g) = sign(α* - α)`.

Here `grad` is *defined* as `Q x - b`. `f_line_hasDerivAt` shows it is the gradient of `f`
along every line (Gateaux sense); the Fréchet derivative is not stated separately.
A concrete instance (`Q = diag(2,1)`, `b = 0`, `x = (1,1)`, `α* = 5/9`) is checked at the end:
`Qex_posDef`, `gex`, and `example`s for `α*`, orthogonality, and an overshoot value.

## Interpretation (not formalized)
The sign of the consecutive-gradient inner product is the undershoot/overshoot signal a
hypergradient learning-rate rule reacts to: positive means "step was too short, grow α",
negative means "too long, shrink α". Since it equals `-φ'(α)`, such a rule is gradient
descent on `φ` in `α`. Only the exact quadratic, single-step case is covered; nothing here
is about stochastic gradients, non-quadratic losses, or convergence of an α-adaptation loop.
-/

open Matrix

namespace Atlas2.A09

variable {n : ℕ}

/-- The quadratic objective `f(x) = ½ xᵀ Q x - bᵀ x`. -/
noncomputable def f (Q : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (x ⬝ᵥ (Q *ᵥ x)) - b ⬝ᵥ x

/-- The gradient `g(x) = Q x - b` (this *is* the gradient of `f` when `Q` is symmetric;
here it is simply a definition). -/
def grad (Q : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) : Fin n → ℝ :=
  Q *ᵥ x - b

/-- The line function `φ(α) = f(x - α g)` with `g = g(x)`. -/
noncomputable def phi (Q : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) (α : ℝ) : ℝ :=
  f Q b (x - α • grad Q b x)

/-- The exact line-search step `α* = gᵀg / gᵀQg`. -/
noncomputable def alphaStar (Q : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) : ℝ :=
  (grad Q b x ⬝ᵥ grad Q b x) / (grad Q b x ⬝ᵥ (Q *ᵥ grad Q b x))

/-- Consecutive-gradient inner product for any step size (no hypotheses on `Q`):
`g(x - α g)ᵀ g = gᵀ g - α gᵀ Q g`. -/
theorem grad_step_inner (Q : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) (α : ℝ) :
    grad Q b (x - α • grad Q b x) ⬝ᵥ grad Q b x
      = grad Q b x ⬝ᵥ grad Q b x - α * (grad Q b x ⬝ᵥ (Q *ᵥ grad Q b x)) := by
  have h : grad Q b (x - α • grad Q b x) = grad Q b x - α • (Q *ᵥ grad Q b x) := by
    simp only [grad, mulVec_sub, mulVec_smul]; abel
  rw [h, sub_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm (Q *ᵥ grad Q b x)]

/-- For symmetric `Q`, `φ` is the explicit quadratic
`φ(α) = f(x) - α gᵀg + (α²/2) gᵀQg`. -/
theorem phi_expand (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ = Q) (b x : Fin n → ℝ) (α : ℝ) :
    phi Q b x α = f Q b x - α * (grad Q b x ⬝ᵥ grad Q b x)
      + α ^ 2 / 2 * (grad Q b x ⬝ᵥ (Q *ᵥ grad Q b x)) := by
  set g := grad Q b x with hgdef
  have hsym : ∀ u v : Fin n → ℝ, u ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ (Q *ᵥ u) := by
    intro u v
    rw [dotProduct_mulVec, ← mulVec_transpose, hQ, dotProduct_comm]
  have hgg : g ⬝ᵥ g = g ⬝ᵥ (Q *ᵥ x) - g ⬝ᵥ b := by
    rw [hgdef, grad, dotProduct_sub]
  have hbg : b ⬝ᵥ g = g ⬝ᵥ b := dotProduct_comm _ _
  unfold phi f
  rw [← hgdef]
  simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  rw [hsym x g, hgg, hbg]
  ring

/-- Curvature along a nonzero gradient is positive for positive definite `Q`. -/
theorem curv_pos (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (b x : Fin n → ℝ)
    (hg : grad Q b x ≠ 0) : 0 < grad Q b x ⬝ᵥ (Q *ᵥ grad Q b x) := by
  simpa using hQ.dotProduct_mulVec_pos hg

/-- The exact step is positive. -/
theorem alphaStar_pos (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (b x : Fin n → ℝ)
    (hg : grad Q b x ≠ 0) : 0 < alphaStar Q b x := by
  have hc := curv_pos Q hQ b x hg
  have hs : 0 < grad Q b x ⬝ᵥ grad Q b x := by
    simpa using (Matrix.PosDef.one (n := Fin n) (R := ℝ)).dotProduct_mulVec_pos hg
  exact div_pos hs hc

/-- Exact line search: `φ(α*) ≤ φ(α)` for every `α`. -/
theorem alphaStar_minimizes (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (b x : Fin n → ℝ)
    (hg : grad Q b x ≠ 0) (α : ℝ) : phi Q b x (alphaStar Q b x) ≤ phi Q b x α := by
  have hsymm : Qᵀ = Q := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hQ.isHermitian.eq
  have hc := curv_pos Q hQ b x hg
  rw [phi_expand Q hsymm, phi_expand Q hsymm]
  unfold alphaStar
  set c := grad Q b x ⬝ᵥ (Q *ᵥ grad Q b x)
  set s := grad Q b x ⬝ᵥ grad Q b x
  have key : (f Q b x - α * s + α ^ 2 / 2 * c) - (f Q b x - s / c * s + (s / c) ^ 2 / 2 * c)
      = (α * c - s) ^ 2 / (2 * c) := by
    field_simp; ring
  have : 0 ≤ (α * c - s) ^ 2 / (2 * c) := by positivity
  linarith

/-- Strictness: `α*` is the unique minimizer of `φ`. -/
theorem alphaStar_strict_min (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (b x : Fin n → ℝ)
    (hg : grad Q b x ≠ 0) (α : ℝ) (hα : α ≠ alphaStar Q b x) :
    phi Q b x (alphaStar Q b x) < phi Q b x α := by
  have hsymm : Qᵀ = Q := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hQ.isHermitian.eq
  have hc := curv_pos Q hQ b x hg
  rw [phi_expand Q hsymm, phi_expand Q hsymm]
  unfold alphaStar at hα ⊢
  set c := grad Q b x ⬝ᵥ (Q *ᵥ grad Q b x)
  set s := grad Q b x ⬝ᵥ grad Q b x
  have key : (f Q b x - α * s + α ^ 2 / 2 * c) - (f Q b x - s / c * s + (s / c) ^ 2 / 2 * c)
      = (α * c - s) ^ 2 / (2 * c) := by
    field_simp; ring
  have hne : α * c - s ≠ 0 := by
    intro h; apply hα; field_simp; linarith
  have : 0 < (α * c - s) ^ 2 / (2 * c) := by positivity
  linarith

/-- The 90-degree rule: after an exact line-search step the new gradient is orthogonal
to the old one, `g(x')ᵀ g(x) = 0` with `x' = x - α* g`. -/
theorem ninety_degree (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (b x : Fin n → ℝ)
    (hg : grad Q b x ≠ 0) :
    grad Q b (x - alphaStar Q b x • grad Q b x) ⬝ᵥ grad Q b x = 0 := by
  rw [grad_step_inner]
  have hc := curv_pos Q hQ b x hg
  unfold alphaStar
  rw [div_mul_cancel₀ _ hc.ne', sub_self]

/-- Undershoot (`α < α*`): consecutive gradients have positive inner product. -/
theorem undershoot_pos (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (b x : Fin n → ℝ)
    (hg : grad Q b x ≠ 0) (α : ℝ) (hα : α < alphaStar Q b x) :
    0 < grad Q b (x - α • grad Q b x) ⬝ᵥ grad Q b x := by
  rw [grad_step_inner]
  have hc := curv_pos Q hQ b x hg
  unfold alphaStar at hα
  rw [lt_div_iff₀ hc] at hα
  linarith

/-- Overshoot (`α > α*`): consecutive gradients have negative inner product. -/
theorem overshoot_neg (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (b x : Fin n → ℝ)
    (hg : grad Q b x ≠ 0) (α : ℝ) (hα : alphaStar Q b x < α) :
    grad Q b (x - α • grad Q b x) ⬝ᵥ grad Q b x < 0 := by
  rw [grad_step_inner]
  have hc := curv_pos Q hQ b x hg
  unfold alphaStar at hα
  rw [div_lt_iff₀ hc] at hα
  linarith

/-- Sign trichotomy packaged: the sign of the consecutive-gradient inner product equals
the sign of `α* - α`. -/
theorem sign_inner_eq (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (b x : Fin n → ℝ)
    (hg : grad Q b x ≠ 0) (α : ℝ) :
    SignType.sign (grad Q b (x - α • grad Q b x) ⬝ᵥ grad Q b x)
      = SignType.sign (alphaStar Q b x - α) := by
  rcases lt_trichotomy α (alphaStar Q b x) with h | h | h
  · rw [sign_pos (undershoot_pos Q hQ b x hg α h), sign_pos (sub_pos.mpr h)]
  · subst h
    rw [ninety_degree Q hQ b x hg, sub_self]
  · rw [sign_neg (overshoot_neg Q hQ b x hg α h), sign_neg (sub_neg.mpr h)]

/-- Hypergradient link: for symmetric `Q`, `φ'(α) = -g(x - α g)ᵀ g`, so the
consecutive-gradient inner product is exactly minus the derivative of the line function. -/
theorem phi_hasDerivAt (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ = Q) (b x : Fin n → ℝ) (α : ℝ) :
    HasDerivAt (phi Q b x) (-(grad Q b (x - α • grad Q b x) ⬝ᵥ grad Q b x)) α := by
  have hfun : phi Q b x = fun a => f Q b x - a * (grad Q b x ⬝ᵥ grad Q b x)
      + a ^ 2 / 2 * (grad Q b x ⬝ᵥ (Q *ᵥ grad Q b x)) := funext (phi_expand Q hQ b x)
  rw [hfun, grad_step_inner]
  have := ((hasDerivAt_const α (f Q b x)).sub
    ((hasDerivAt_id α).mul_const (grad Q b x ⬝ᵥ grad Q b x))).add
    (((hasDerivAt_pow 2 α).div_const 2).mul_const (grad Q b x ⬝ᵥ (Q *ᵥ grad Q b x)))
  convert this using 1
  · funext a; simp only [Pi.add_apply, Pi.sub_apply, id]
  · simp; ring


/-- `grad` really is the gradient of `f` (directionally): for symmetric `Q`, along any line
`t ↦ x + t v` the derivative of `f` at `t` is `g(x + t v)ᵀ v`. -/
theorem f_line_hasDerivAt (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ = Q) (b x v : Fin n → ℝ)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => f Q b (x + s • v)) (grad Q b (x + t • v) ⬝ᵥ v) t := by
  have hsym : ∀ u w : Fin n → ℝ, u ⬝ᵥ (Q *ᵥ w) = w ⬝ᵥ (Q *ᵥ u) := by
    intro u w
    rw [dotProduct_mulVec, ← mulVec_transpose, hQ, dotProduct_comm]
  have hfun : (fun s : ℝ => f Q b (x + s • v)) = fun s => f Q b x
      + s * (x ⬝ᵥ (Q *ᵥ v) - b ⬝ᵥ v) + s ^ 2 / 2 * (v ⬝ᵥ (Q *ᵥ v)) := by
    funext s
    unfold f
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    rw [hsym v x]
    ring
  have hval : grad Q b (x + t • v) ⬝ᵥ v
      = (x ⬝ᵥ (Q *ᵥ v) - b ⬝ᵥ v) + t * (v ⬝ᵥ (Q *ᵥ v)) := by
    unfold grad
    simp only [mulVec_add, mulVec_smul, sub_dotProduct, add_dotProduct, smul_dotProduct,
      smul_eq_mul]
    rw [dotProduct_comm (Q *ᵥ x), dotProduct_comm (Q *ᵥ v), dotProduct_comm b, hsym v x]
    ring
  rw [hfun, hval]
  have := ((hasDerivAt_const t (f Q b x)).add
    ((hasDerivAt_id t).mul_const (x ⬝ᵥ (Q *ᵥ v) - b ⬝ᵥ v))).add
    (((hasDerivAt_pow 2 t).div_const 2).mul_const (v ⬝ᵥ (Q *ᵥ v)))
  convert this using 1
  · funext a; simp only [Pi.add_apply, id]
  · simp

/-! ### Concrete instance
`Q = diag(2, 1)`, `b = 0`, `x = (1, 1)`: `g = (2, 1)`, `gᵀg = 5`, `gᵀQg = 9`, `α* = 5/9`,
`x' = (-1/9, 4/9)`, `g(x') = (-2/9, 4/9)`, and `g(x') · g = -4/9 + 4/9 = 0`. -/

/-- The concrete matrix `diag(2, 1)`. -/
def Qex : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![2, 1]

theorem Qex_posDef : Qex.PosDef :=
  Matrix.PosDef.diagonal (fun i => by fin_cases i <;> norm_num)

theorem gex : grad Qex 0 ![1, 1] = ![2, 1] := by
  ext i; fin_cases i <;> simp [grad, Qex]

example : alphaStar Qex 0 ![1, 1] = 5 / 9 := by
  rw [alphaStar, gex]
  simp [Qex, mulVec_diagonal, dotProduct, Fin.sum_univ_two]
  norm_num

/-- Main theorem instantiated: the exact step on `diag(2,1)` from `(1,1)` gives orthogonal
consecutive gradients. -/
example : grad Qex 0 (![1, 1] - alphaStar Qex 0 ![1, 1] • grad Qex 0 ![1, 1])
    ⬝ᵥ grad Qex 0 ![1, 1] = 0 :=
  ninety_degree Qex Qex_posDef 0 ![1, 1] (by rw [gex]; intro h; simpa using congrFun h 0)

/-- Overshoot instance: `α = 1 > 5/9` gives negative inner product (`5 - 9 = -4`). -/
example : grad Qex 0 (![1, 1] - (1 : ℝ) • grad Qex 0 ![1, 1]) ⬝ᵥ grad Qex 0 ![1, 1] = -4 := by
  rw [grad_step_inner, gex]
  simp [Qex, mulVec_diagonal, dotProduct, Fin.sum_univ_two]
  norm_num

end Atlas2.A09
