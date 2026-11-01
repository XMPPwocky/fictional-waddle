import Mathlib

/-!
# Credit that no single parameter owns lives in the Hessian

Two parameters `x`, `y` and a quadratic loss with Hessian `[[a, c], [c, d]]` and gradient term `(bx, by)`:
`L x y = (a x² + 2 c x y + d y²)/2 + bx x + by y`. Every smooth loss looks like this to second order.

PROVED:
* `and_gate_gradient_zero`, `and_gate_joint_pays`: for `f x y = x y` (an AND gate) at the origin each parameter's own
  derivative is 0 and each solo move changes nothing, yet moving both together by `t ≠ 0` gives `t² > 0`. First-order
  credit assignment sees nothing; the gain is entirely in the cross term of the Hessian.
* `taylor_exact`: for the quadratic, `L (θ + δ) = L θ + g·δ + δᵀ H δ / 2` exactly.
* `interaction_credit`: the joint change minus the two solo changes is exactly `c δx δy`. The share of credit that
  belongs to neither parameter alone is the off-diagonal Hessian entry.
* `hvp_is_an_intervention`: nudging the parameters by `ε v` and watching the gradient move gives exactly `ε H v`.
  Reading the Hessian is a perturbation experiment: shine a light along `v`, see whose credit changes.
* `hutchinson_two`: averaging `vᵀ H v` over the four random sign vectors `v ∈ {±1}²` gives the trace `a + d` exactly,
  so random seeds read curvature without knowing the Hessian.
INTERPRETED (not formalized): parameters as agents; the off-diagonal block as one agent's causal effect on another's
credit; games, where the Jacobian is not symmetric, are covered by the atlas's CoCo split and swapped-credit results.
-/

namespace HessianCredit

theorem and_gate_gradient_zero :
    HasDerivAt (fun x : ℝ => x * 0) 0 0 ∧ HasDerivAt (fun y : ℝ => (0 : ℝ) * y) 0 0 := by
  refine ⟨?_, ?_⟩ <;> simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)

theorem and_gate_joint_pays (t : ℝ) (ht : t ≠ 0) : t * 0 = 0 ∧ 0 * t = 0 ∧ 0 < t * t := by
  exact ⟨mul_zero t, zero_mul t, mul_self_pos.mpr ht⟩

noncomputable def L (a c d bx by' x y : ℝ) : ℝ := (a * x ^ 2 + 2 * c * x * y + d * y ^ 2) / 2 + bx * x + by' * y

def gx (a c bx x y : ℝ) : ℝ := a * x + c * y + bx
def gy (c d by' x y : ℝ) : ℝ := c * x + d * y + by'

theorem taylor_exact (a c d bx by' x y dx dy : ℝ) :
    L a c d bx by' (x + dx) (y + dy) =
      L a c d bx by' x y + (gx a c bx x y * dx + gy c d by' x y * dy) + (a * dx ^ 2 + 2 * c * dx * dy + d * dy ^ 2) / 2 := by
  unfold L gx gy; ring

theorem interaction_credit (a c d bx by' x y dx dy : ℝ) :
    L a c d bx by' (x + dx) (y + dy) - L a c d bx by' (x + dx) y - L a c d bx by' x (y + dy) + L a c d bx by' x y
      = c * dx * dy := by
  unfold L; ring

theorem hvp_is_an_intervention (a c d bx by' x y vx vy ε : ℝ) :
    gx a c bx (x + ε * vx) (y + ε * vy) - gx a c bx x y = ε * (a * vx + c * vy) ∧
    gy c d by' (x + ε * vx) (y + ε * vy) - gy c d by' x y = ε * (c * vx + d * vy) := by
  unfold gx gy; constructor <;> ring

theorem hutchinson_two (a c d : ℝ) :
    ((a + 2 * c + d) + (a - 2 * c + d) + (a - 2 * c + d) + (a + 2 * c + d)) / 4 = a + d ∧
    (∀ vx vy : ℝ, (vx = 1 ∨ vx = -1) → (vy = 1 ∨ vy = -1) →
      a * vx ^ 2 + 2 * c * vx * vy + d * vy ^ 2 = a + 2 * c * (vx * vy) + d) := by
  refine ⟨by ring, fun vx vy hx hy => ?_⟩
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> ring

end HessianCredit
