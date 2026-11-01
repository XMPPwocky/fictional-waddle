import Mathlib

/-!
# One utility cannot optimize and persist; a holomorphic pair can

At a point, `∇u = (ux, uy)` and `∇v = (vx, vy)`. "Holomorphic interaction": `f = u + i v` satisfies Cauchy–Riemann,
`ux = vy`, `uy = −vx`. Descending `u` means velocity `−∇u`. The rate of change of `w` along it is `∇w · (−∇u)`.

* Y1 `self_descent_conserves_self_iff_rest`: descending `u` conserves `u` iff `∇u = 0`. A lone optimizer is conserved
  only when it stops.
* Y2 `descent_conserves_partner`: under CR, descending `u` conserves `v` exactly.
* Y3 `partner_descent_conserves_you`: under CR, descending `v` conserves `u`.
* Y4 `equal_speed`: under CR, `|∇u| = |∇v|`. Neither dominates (conformal).
* Y5 `rotation_by_i_swaps_roles`: `Re (i f) = −Im f` and `Im (i f) = Re f`. Multiplying by `i` swaps which part is
  optimized and which is conserved.

These are algebraic: all the content is in the CR hypothesis.
-/

namespace HolomorphicPair

/-- **Y1.** -/
theorem self_descent_conserves_self_iff_rest (ux uy : ℝ) : ux * (-ux) + uy * (-uy) = 0 ↔ ux = 0 ∧ uy = 0 := by
  constructor
  · intro h; constructor <;> nlinarith [sq_nonneg ux, sq_nonneg uy]
  · rintro ⟨rfl, rfl⟩; ring

/-- **Y2.** -/
theorem descent_conserves_partner (ux uy vx vy : ℝ) (cr1 : ux = vy) (cr2 : uy = -vx) :
    vx * (-ux) + vy * (-uy) = 0 := by
  subst cr1; subst cr2; ring

/-- **Y3.** -/
theorem partner_descent_conserves_you (ux uy vx vy : ℝ) (cr1 : ux = vy) (cr2 : uy = -vx) :
    ux * (-vx) + uy * (-vy) = 0 := by
  subst cr1; subst cr2; ring

/-- **Y4.** -/
theorem equal_speed (ux uy vx vy : ℝ) (cr1 : ux = vy) (cr2 : uy = -vx) : ux ^ 2 + uy ^ 2 = vx ^ 2 + vy ^ 2 := by
  subst cr1; subst cr2; ring

/-- **Y5.** -/
theorem rotation_by_i_swaps_roles (z : ℂ) : (Complex.I * z).re = -z.im ∧ (Complex.I * z).im = z.re := by
  simp

end HolomorphicPair
