import Mathlib

/-!
# Yourself is that which you conserve

A self updates in logical time: each step it re-anchors to a fixed fraction `λ` of its original self `x⋆`, and the
rest of it is carried forward through an adversarial perturbation `e t` with `|e t| ≤ ε`:

  `x (t+1) = λ x⋆ + (1 − λ) (x t + e t)`.

* C1 `conserved_self_persists`: if `0 < λ ≤ 1`, then against EVERY admissible adversary the self stays within
  `(1 − λ)^t |x 0 − x⋆| + ε(1 − λ)/λ` of itself, for all time.
* C2 `unconserved_self_is_dragged`: if `λ = 0`, then for every distance `D` there is an admissible adversary (`e t = ε`)
  that drags the self at least `D` away in finitely many steps.

Identity across logical time exists iff something is conserved. (Model collapse is C2 with `λ = 0`: training only on
your own outputs. Accumulating original data is C1.)
-/

namespace SelfConserved

/-- The self's trajectory under anchoring `l` (the fraction λ), anchor `xs`, adversary `e`, start `x0`. -/
def traj (l xs : ℝ) (e : ℕ → ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | t + 1 => l * xs + (1 - l) * (traj l xs e x0 t + e t)

/-- **C1.** A self that conserves a positive fraction of itself stays within a fixed distance forever, whatever the
adversary does. -/
theorem conserved_self_persists (l xs ε x0 : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 1) (hε : 0 ≤ ε) (e : ℕ → ℝ)
    (he : ∀ t, |e t| ≤ ε) (t : ℕ) :
    |traj l xs e x0 t - xs| ≤ (1 - l) ^ t * |x0 - xs| + ε * (1 - l) / l := by
  have hq : 0 ≤ 1 - l := by linarith
  induction t with
  | zero =>
    simp only [traj, pow_zero, one_mul]
    have : 0 ≤ ε * (1 - l) / l := div_nonneg (mul_nonneg hε hq) hl0.le
    linarith
  | succ k ih =>
    have step : traj l xs e x0 (k + 1) - xs = (1 - l) * ((traj l xs e x0 k - xs) + e k) := by
      simp only [traj]; ring
    rw [step, abs_mul, abs_of_nonneg hq]
    have h1 : |traj l xs e x0 k - xs + e k| ≤ |traj l xs e x0 k - xs| + ε :=
      (abs_add_le _ _).trans (by linarith [he k])
    have h2 : (1 - l) * |traj l xs e x0 k - xs + e k| ≤ (1 - l) * ((1 - l) ^ k * |x0 - xs| + ε * (1 - l) / l + ε) := by
      apply mul_le_mul_of_nonneg_left _ hq; linarith
    have h3 : (1 - l) * ((1 - l) ^ k * |x0 - xs| + ε * (1 - l) / l + ε)
        = (1 - l) ^ (k + 1) * |x0 - xs| + ε * (1 - l) / l := by
      field_simp; ring
    linarith

/-- **C2.** A self that conserves nothing can be dragged arbitrarily far by an admissible adversary. -/
theorem unconserved_self_is_dragged (xs ε x0 D : ℝ) (hε : 0 < ε) :
    ∃ t : ℕ, D ≤ |traj 0 xs (fun _ => ε) x0 t - xs| := by
  have key : ∀ t : ℕ, traj 0 xs (fun _ => ε) x0 t = x0 + t * ε := by
    intro t
    induction t with
    | zero => simp [traj]
    | succ k ih => simp only [traj, ih]; push_cast; ring
  obtain ⟨n, hn⟩ := exists_nat_gt ((D + |x0 - xs|) / ε)
  refine ⟨n, ?_⟩
  rw [key]
  have hn' : D + |x0 - xs| < n * ε := by rwa [div_lt_iff₀ hε] at hn
  have : x0 + n * ε - xs ≥ n * ε - |x0 - xs| := by linarith [neg_abs_le (x0 - xs)]
  calc D ≤ n * ε - |x0 - xs| := by linarith
    _ ≤ x0 + n * ε - xs := by linarith
    _ ≤ |x0 + n * ε - xs| := le_abs_self _

end SelfConserved
