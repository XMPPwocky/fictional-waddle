import Mathlib

/-!
# B03 — Bogoliubov mixing lies on a hyperbola

Setting: any ring `R` that is a `ℂ`-algebra, with `a, a† : R` satisfying the canonical
commutation relation `a a† - a† a = 1`. For `u v : ℂ` set
`b = u a + v a†`, `b† = ū a† + v̄ a`.

## Proved (in this file, no `sorry`, no extra axioms)
* `bogoliubov_comm` / `bogoliubov_comm_normSq`:
  `b b† - b† b = (‖u‖² - ‖v‖²) • 1`.
* `bogoliubov_canonical_iff`: in a nontrivial such ring, `b, b†` are again canonical
  (`b b† - b† b = 1`) iff `‖u‖² - ‖v‖² = 1` — the coefficient pair lies on a hyperbola.
* `hyperbola_cosh_sinh`, `boost_canonical`: `(cosh r, sinh r)` lies on it, so real
  "boosts" are canonical. `hyperbola_param_surj`: conversely every real point
  `(u, v)` with `u > 0`, `u² - v² = 1` is `(cosh r, sinh r)` (take `r = arsinh v`).
* `bogB_comp`, `bogBd_comp`: applying `(u₂,v₂)` to the operators `b, b†` produced by
  `(u₁,v₁)` is again a Bogoliubov map of `a, a†`, with coefficients `bogComp`
  (this is the SU(1,1) matrix product `[[u, v], [v̄, ū]]`).
* `bogComp_hyperbola`: `|u|² - |v|²` is multiplicative under composition (a determinant),
  so the hyperbola is closed under composition.
* `bogComp_boost`, `boost_compose`: for real boosts, composition adds rapidities,
  `(cosh r, sinh r)` then `(cosh s, sinh s)` gives `(cosh (r+s), sinh (r+s))`, like
  collinear Lorentz boosts.
* `bogB_inverse` (adversarial pass): on the hyperbola, `(ū, -v)` undoes `(u, v)`
  at operator level, so with closure and the identity `(1, 0)` the hyperbola is a group.
* `Weyl.weyl_ccr` + examples (adversarial pass, non-vacuity): `a = d/dX`, `a† = X·` on
  `ℂ[X]` satisfy the CCR; the boost, a complex point `(2, i√3)` and the off-hyperbola
  point `(1, 1)` (not canonical) are checked there.

## Interpreted (cited, NOT formalized)
This is the algebra behind Unruh / Hawking pair creation: the Minkowski vacuum
annihilated by `a` is not annihilated by `b` when `v ≠ 0`, and the `b`-mode particle
number in the `a`-vacuum is `|v|²` (= `sinh² r`; thermal for the Rindler/horizon
rapidity profile). None of the Hilbert-space, vacuum, or thermality statements are
formalized here — only the commutator algebra and the group law of the coefficients.
-/

open ComplexConjugate

namespace B03

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- The mixed annihilator `b = u a + v a†`. -/
def bogB (u v : ℂ) (a ad : R) : R := u • a + v • ad

/-- The mixed creator `b† = ū a† + v̄ a`. -/
def bogBd (u v : ℂ) (a ad : R) : R := (conj u) • ad + (conj v) • a

/-- Composition of coefficient pairs: first `(u₁, v₁)`, then `(u₂, v₂)`. -/
def bogComp (p q : ℂ × ℂ) : ℂ × ℂ :=
  (q.1 * p.1 + q.2 * conj p.2, q.1 * p.2 + q.2 * conj p.1)

/-- Core identity: the commutator of the mixed pair is `(u ū - v v̄)` times the old one. -/
theorem bogoliubov_comm_core (a ad : R) (u v : ℂ) :
    bogB u v a ad * bogBd u v a ad - bogBd u v a ad * bogB u v a ad
      = (u * conj u - v * conj v) • (a * ad - ad * a) := by
  simp only [bogB, bogBd, add_mul, mul_add, smul_mul_smul, sub_smul, smul_sub]
  rw [mul_comm (conj u) u, mul_comm (conj v) v, mul_comm (conj u) v, mul_comm (conj v) u]
  abel

theorem bogoliubov_comm_normSq (a ad : R) (h : a * ad - ad * a = 1) (u v : ℂ) :
    bogB u v a ad * bogBd u v a ad - bogBd u v a ad * bogB u v a ad
      = ((Complex.normSq u - Complex.normSq v : ℝ) : ℂ) • (1 : R) := by
  rw [bogoliubov_comm_core, h, Complex.mul_conj, Complex.mul_conj]
  push_cast
  rfl

theorem bogoliubov_comm (a ad : R) (h : a * ad - ad * a = 1) (u v : ℂ) :
    bogB u v a ad * bogBd u v a ad - bogBd u v a ad * bogB u v a ad
      = ((‖u‖ ^ 2 - ‖v‖ ^ 2 : ℝ) : ℂ) • (1 : R) := by
  rw [bogoliubov_comm_normSq a ad h, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]

theorem bogoliubov_canonical_iff [Nontrivial R] (a ad : R) (h : a * ad - ad * a = 1)
    (u v : ℂ) :
    bogB u v a ad * bogBd u v a ad - bogBd u v a ad * bogB u v a ad = 1
      ↔ ‖u‖ ^ 2 - ‖v‖ ^ 2 = 1 := by
  rw [bogoliubov_comm a ad h, ← Algebra.algebraMap_eq_smul_one,
    ← map_one (algebraMap ℂ R), (algebraMap ℂ R).injective.eq_iff, Complex.ofReal_eq_one]

theorem hyperbola_cosh_sinh (r : ℝ) : Real.cosh r ^ 2 - Real.sinh r ^ 2 = 1 :=
  Real.cosh_sq_sub_sinh_sq r

theorem boost_canonical (a ad : R) (h : a * ad - ad * a = 1) (r : ℝ) :
    bogB (Real.cosh r : ℂ) (Real.sinh r : ℂ) a ad * bogBd (Real.cosh r : ℂ) (Real.sinh r : ℂ) a ad
      - bogBd (Real.cosh r : ℂ) (Real.sinh r : ℂ) a ad * bogB (Real.cosh r : ℂ) (Real.sinh r : ℂ) a ad
      = 1 := by
  rw [bogoliubov_comm a ad h, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs, hyperbola_cosh_sinh]
  simp

theorem hyperbola_param_surj (u v : ℝ) (hu : 0 < u) (h : u ^ 2 - v ^ 2 = 1) :
    ∃ r : ℝ, Real.cosh r = u ∧ Real.sinh r = v := by
  refine ⟨Real.arsinh v, ?_, Real.sinh_arsinh v⟩
  rw [Real.cosh_arsinh, show 1 + v ^ 2 = u ^ 2 by linarith]
  exact Real.sqrt_sq hu.le

theorem bogB_comp (a ad : R) (p q : ℂ × ℂ) :
    bogB q.1 q.2 (bogB p.1 p.2 a ad) (bogBd p.1 p.2 a ad)
      = bogB (bogComp p q).1 (bogComp p q).2 a ad := by
  simp only [bogB, bogBd, bogComp, smul_add, add_smul, smul_smul]
  abel

theorem bogBd_comp (a ad : R) (p q : ℂ × ℂ) :
    bogBd q.1 q.2 (bogB p.1 p.2 a ad) (bogBd p.1 p.2 a ad)
      = bogBd (bogComp p q).1 (bogComp p q).2 a ad := by
  simp only [bogB, bogBd, bogComp, smul_add, add_smul, smul_smul, map_add, map_mul,
    Complex.conj_conj]
  abel

theorem bogComp_hyperbola (p q : ℂ × ℂ) :
    Complex.normSq (bogComp p q).1 - Complex.normSq (bogComp p q).2
      = (Complex.normSq p.1 - Complex.normSq p.2) * (Complex.normSq q.1 - Complex.normSq q.2) := by
  simp only [bogComp, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem bogComp_boost (r s : ℝ) :
    bogComp ((Real.cosh r : ℂ), (Real.sinh r : ℂ)) ((Real.cosh s : ℂ), (Real.sinh s : ℂ))
      = ((Real.cosh (r + s) : ℂ), (Real.sinh (r + s) : ℂ)) := by
  simp only [bogComp, Complex.conj_ofReal, Real.cosh_add, Real.sinh_add, Prod.mk.injEq]
  push_cast
  constructor <;> ring

theorem boost_compose (a ad : R) (r s : ℝ) :
    bogB (Real.cosh s : ℂ) (Real.sinh s : ℂ)
        (bogB (Real.cosh r : ℂ) (Real.sinh r : ℂ) a ad)
        (bogBd (Real.cosh r : ℂ) (Real.sinh r : ℂ) a ad)
      = bogB (Real.cosh (r + s) : ℂ) (Real.sinh (r + s) : ℂ) a ad := by
  have := bogB_comp a ad ((Real.cosh r : ℂ), (Real.sinh r : ℂ))
    ((Real.cosh s : ℂ), (Real.sinh s : ℂ))
  rw [bogComp_boost] at this
  exact this

/-! ## Adversarial-pass additions

### Going up: the hyperbola is a group (inverses)
`bogB_inverse`: for `(u, v)` on the hyperbola, the transform `(ū, -v)` undoes `(u, v)`:
applying it to `b, b†` returns `a`. With `bogComp_hyperbola` (closure) and `(1, 0)` as the
identity, this makes the hyperbola `|u|² - |v|² = 1` a group under `bogComp` (SU(1,1));
for a real boost `(cosh r, sinh r)` the inverse is `(cosh r, -sinh r) = (cosh (-r), sinh (-r))`. -/

theorem bogB_inverse (a ad : R) (u v : ℂ) (hp : Complex.normSq u - Complex.normSq v = 1) :
    bogB (conj u) (-v) (bogB u v a ad) (bogBd u v a ad) = a := by
  have hc : bogComp (u, v) (conj u, -v) = (1, 0) := by
    simp only [bogComp, Prod.mk.injEq]
    refine ⟨?_, by ring⟩
    rw [mul_comm (conj u) u, neg_mul, ← sub_eq_add_neg, Complex.mul_conj, Complex.mul_conj,
      ← Complex.ofReal_sub, hp, Complex.ofReal_one]
  have h1 := bogB_comp a ad (u, v) (conj u, -v)
  rw [hc] at h1
  rw [h1]
  simp [bogB]

end B03

/-! ### Non-vacuity: a concrete canonical pair (the Weyl algebra)
The CCR has no finite-dimensional matrix solutions (take traces), so the witness is
`a = d/dX`, `a† = (X ·)` acting on `ℂ[X]`, inside the `ℂ`-algebra `Module.End ℂ ℂ[X]`.
`weyl_ccr` proves `a a† - a† a = 1` there (the Leibniz rule), and the examples below
instantiate the main theorems at it, including both directions of the iff. -/

namespace B03.Weyl
open Polynomial

/-- The annihilator `a = d/dX` on `ℂ[X]`. -/
noncomputable def wA : Module.End ℂ ℂ[X] := Polynomial.derivative

/-- The creator `a† = X ·` on `ℂ[X]`. -/
noncomputable def wAd : Module.End ℂ ℂ[X] := LinearMap.mulLeft ℂ X

theorem weyl_ccr : wA * wAd - wAd * wA = 1 := by
  refine LinearMap.ext fun p => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply, wA, wAd,
    LinearMap.mulLeft_apply, Polynomial.derivative_mul, Polynomial.derivative_X, one_mul]
  abel

/-- A real boost of the Weyl pair is canonical. -/
example (r : ℝ) :
    bogB (Real.cosh r : ℂ) (Real.sinh r : ℂ) wA wAd * bogBd (Real.cosh r : ℂ) (Real.sinh r : ℂ) wA wAd
      - bogBd (Real.cosh r : ℂ) (Real.sinh r : ℂ) wA wAd * bogB (Real.cosh r : ℂ) (Real.sinh r : ℂ) wA wAd
      = 1 :=
  boost_canonical wA wAd weyl_ccr r

/-- `(u, v) = (1, 1)` is off the hyperbola, so it is NOT canonical (the `only if` bites):
the commutator of `b = a + a†` with itself vanishes. -/
example :
    bogB 1 1 wA wAd * bogBd 1 1 wA wAd - bogBd 1 1 wA wAd * bogB 1 1 wA wAd ≠ 1 := by
  rw [Ne, bogoliubov_canonical_iff wA wAd weyl_ccr]
  norm_num

/-- `(u, v) = (2, i√3)` is a genuinely complex point on the hyperbola: `4 - 3 = 1`. -/
example :
    bogB 2 (Complex.I * (Real.sqrt 3 : ℂ)) wA wAd * bogBd 2 (Complex.I * (Real.sqrt 3 : ℂ)) wA wAd
      - bogBd 2 (Complex.I * (Real.sqrt 3 : ℂ)) wA wAd * bogB 2 (Complex.I * (Real.sqrt 3 : ℂ)) wA wAd
      = 1 := by
  rw [bogoliubov_canonical_iff wA wAd weyl_ccr]
  simp
  norm_num

end B03.Weyl
