import Mathlib

/-!
# A lawful universe cannot choose a hand; an unlawful one decides cheaply and pays to arrive

A state space with a mirror `R`, a chirality functional `χ` that flips sign under the mirror (`χ ∘ R = −χ`), and a
dynamics `f`. "Lawful" here means the dynamics commutes with the mirror.

PROVED:
* `lawful_keeps_symmetry`: under lawful dynamics a mirror-symmetric state stays mirror-symmetric forever.
* `lawful_no_net_chirality`: so its chirality is zero forever. Net handedness needs a law or a start that is not
  mirror-symmetric.
* `bias_picks_branch`, `bias_gain_le`, `bias_gain_ge`: near a pitchfork, `r x − x³ + h = 0` with `r < 0` and bias
  `h > 0`, every equilibrium is on the side the bias favours, with `h / ((h/r)² − r) ≤ x ≤ h / (−r)`. The gain `x / h`
  is about `1/|r|`, unbounded as the bifurcation is approached: deciding which hand costs almost nothing there.
* `selection_destroys`: getting there by selection does cost. If a fraction `q` of the material is one hand, selection
  with survival at most 1 brings that hand's fraction to `p` only if the surviving fraction `S` satisfies
  `S ≤ q / p`. From a nearly racemic start (`q ≈ 1/2`) to 99% purity, at least about half the material is destroyed.
INTERPRETED (not formalized): which hand is chosen is one cheap bit near a bifurcation; reaching purity is
refrigeration and costs deaths or work, so the bifurcation is a free amplifier, not a free Maxwell's demon.
-/

namespace LawfulCannotChoose

variable {X : Type*} (R f : X → X) (χ : X → ℝ)

theorem lawful_keeps_symmetry (hf : ∀ x, f (R x) = R (f x)) (x₀ : X) (h₀ : R x₀ = x₀) (n : ℕ) :
    R (f^[n] x₀) = f^[n] x₀ := by
  induction n with
  | zero => simpa using h₀
  | succ n ih => rw [Function.iterate_succ_apply', ← hf, ih]

theorem lawful_no_net_chirality (hf : ∀ x, f (R x) = R (f x)) (hχ : ∀ x, χ (R x) = -χ x)
    (x₀ : X) (h₀ : R x₀ = x₀) (n : ℕ) : χ (f^[n] x₀) = 0 := by
  have h := hχ (f^[n] x₀)
  rw [lawful_keeps_symmetry R f hf x₀ h₀ n] at h
  linarith

theorem bias_picks_branch (r h x : ℝ) (hr : r < 0) (hh : 0 < h) (he : r * x - x ^ 3 + h = 0) : 0 < x := by
  by_contra hx
  push Not at hx
  nlinarith [sq_nonneg x, mul_nonneg (neg_nonneg.mpr hx) (sq_nonneg x)]

theorem bias_gain_le (r h x : ℝ) (hr : r < 0) (hh : 0 < h) (he : r * x - x ^ 3 + h = 0) : x ≤ h / (-r) := by
  have hx := bias_picks_branch r h x hr hh he
  rw [le_div_iff₀ (by linarith)]
  nlinarith [pow_pos hx 3]

theorem bias_gain_ge (r h x : ℝ) (hr : r < 0) (hh : 0 < h) (he : r * x - x ^ 3 + h = 0) :
    h / ((h / r) ^ 2 - r) ≤ x := by
  have hx := bias_picks_branch r h x hr hh he
  have hup := bias_gain_le r h x hr hh he
  have hx2 : x ^ 2 ≤ (h / r) ^ 2 := by
    have : h / (-r) = -(h / r) := by rw [div_neg]
    rw [this] at hup
    have h0 : 0 ≤ x := hx.le
    nlinarith [sq_nonneg (h / r)]
  have hden : 0 < (h / r) ^ 2 - r := by nlinarith [sq_nonneg (h / r)]
  rw [div_le_iff₀ hden]
  nlinarith [mul_le_mul_of_nonneg_left hx2 hx.le]

theorem selection_destroys (q sL S p : ℝ) (hq : 0 ≤ q) (hs : sL ≤ 1) (hS : 0 < S) (hp : 0 < p)
    (hpost : p = q * sL / S) : S ≤ q / p := by
  rw [le_div_iff₀ hp, hpost, mul_div_cancel₀ _ hS.ne']
  exact mul_le_of_le_one_right hq hs

end LawfulCannotChoose
