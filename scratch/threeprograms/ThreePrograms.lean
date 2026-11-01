import Mathlib

/-!
# Three programs: one cools, one rotates, one heats

Linear stochastic dynamics `dx = M x dt + √(2D) dW` has covariance flow `Σ' = M Σ + Σ Mᵀ + 2D`. Split the drift as
`M = −S + A` with `S` symmetric (the cooling part) and `A` antisymmetric (the rotating part); `D` is the heating part.

PROVED:
* `rotation_conserves`: the antisymmetric part never changes `|x|²`: `x · A x = 0`.
* `cooling_cools`: if `S` is positive semidefinite (`0 ≤ y · S y` for all `y`), the symmetric part never raises it: `x · (−S x) ≤ 0`.
* `balance_iff`: the target `Σ = I` is stationary iff `D = S`, whatever `A` is. Heating must exactly match cooling
  (fluctuation–dissipation), and any rotation leaves the target alone.
* `coco_unique`: a two-player payoff pair `(a, b)` splits uniquely into a shared part `t` and a zero-sum part `z`
  with `a = t + z`, `b = t − z`, namely `t = (a + b)/2`, `z = (a − b)/2` (the Kalai–Kalai CoCo split).
* `selfplay_is_cooperative`: in a symmetric game, against an exact copy, the zero-sum part is zero and the payoff
  is the shared part alone.
INTERPRETED (not formalized): the shared part of a game drives the cooling (gradient) flow and the zero-sum part the
rotating flow, as in the replicator dynamics of potential and zero-sum games.
-/

namespace ThreePrograms
open Matrix

variable {n : Type*} [Fintype n]

theorem rotation_conserves (A : Matrix n n ℝ) (hA : Aᵀ = -A) (x : n → ℝ) : x ⬝ᵥ (A *ᵥ x) = 0 := by
  have h1 : x ⬝ᵥ (A *ᵥ x) = (x ᵥ* A) ⬝ᵥ x := dotProduct_mulVec x A x
  have h2 : x ᵥ* A = Aᵀ *ᵥ x := (mulVec_transpose A x).symm
  have h3 : (Aᵀ *ᵥ x) ⬝ᵥ x = -(x ⬝ᵥ (A *ᵥ x)) := by
    rw [hA, neg_mulVec, neg_dotProduct, dotProduct_comm]
  linarith [h1, h2 ▸ h3]

theorem cooling_cools (S : Matrix n n ℝ) (hS : ∀ y : n → ℝ, 0 ≤ y ⬝ᵥ (S *ᵥ y)) (x : n → ℝ) :
    x ⬝ᵥ ((-S) *ᵥ x) ≤ 0 := by
  rw [neg_mulVec, dotProduct_neg, neg_nonpos]
  exact hS x

theorem balance_iff [DecidableEq n] (S A D : Matrix n n ℝ) (hS : Sᵀ = S) (hA : Aᵀ = -A) :
    (-S + A) * 1 + 1 * (-S + A)ᵀ + (2 : ℝ) • D = 0 ↔ D = S := by
  rw [Matrix.mul_one, Matrix.one_mul, transpose_add, transpose_neg, hS, hA]
  constructor
  · intro h
    have : (2 : ℝ) • D = (2 : ℝ) • S := by
      have h' : (2 : ℝ) • D - (2 : ℝ) • S = 0 := by rw [← h, two_smul, two_smul]; abel
      exact sub_eq_zero.mp h'
    exact smul_right_injective _ two_ne_zero this
  · intro h; subst h; rw [two_smul]; abel

theorem coco_unique {X : Type*} (a b t z : X → ℝ) :
    (a = t + z ∧ b = t - z) ↔ (t = (a + b) / 2 ∧ z = (a - b) / 2) := by
  constructor
  · rintro ⟨rfl, rfl⟩; constructor <;> funext x <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.ofNat_apply] <;> ring
  · rintro ⟨rfl, rfl⟩; constructor <;> funext x <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.ofNat_apply] <;> ring

/-- In a symmetric game (`b x y = a y x`), the zero-sum part vanishes on the diagonal: against an exact copy, a
player's payoff is the shared part alone. -/
theorem selfplay_is_cooperative {X : Type*} (a : X → X → ℝ) (x : X) :
    let t := fun u v => (a u v + a v u) / 2
    let z := fun u v => (a u v - a v u) / 2
    z x x = 0 ∧ a x x = t x x := by
  simp only
  constructor <;> ring

end ThreePrograms
