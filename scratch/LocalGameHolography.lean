import Mathlib

/-!
# Local games at equilibrium are holographic (a chain toy)

Players `0 … n+1` on a chain. The two ends are the boundary (fixed); every interior player `i` plays a local
coordination game with its two neighbours, payoff `-((x i - x (i-1))^2 + (x i - x (i+1))^2)` (a potential game: Lawful
Good). Statements:

* H1 `best_response_is_average`: the unique best response is the average of the two neighbours.
* H2 `equilibrium_is_affine`: an equilibrium (every interior player best-responding) is affine in position, fixed by the
  two boundary values alone.
* H3 `holographic_uniqueness`: two equilibria that agree on the boundary agree everywhere. The bulk carries no
  information beyond its boundary: n interior players, zero free parameters.
-/

namespace LocalGameHolography

/-- **H1.** In the local coordination game the unique best response to neighbours `a`, `b` is their average. -/
theorem best_response_is_average (a b x : ℝ) :
    (∀ y : ℝ, (x - a) ^ 2 + (x - b) ^ 2 ≤ (y - a) ^ 2 + (y - b) ^ 2) ↔ x = (a + b) / 2 := by
  constructor
  · intro hy
    have h := hy ((a + b) / 2)
    have hsq : (x - (a + b) / 2) ^ 2 ≤ 0 := by nlinarith [h]
    have h2 : (x - (a + b) / 2) ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
    have := (pow_eq_zero_iff (n := 2) (by norm_num)).1 h2
    linarith
  · intro hx y; subst hx; nlinarith [sq_nonneg (y - (a + b) / 2)]

/-- **H2.** If every interior player best-responds (`2 f i = f (i-1) + f (i+1)` for `1 ≤ i ≤ n`), the profile is the
straight line between the two boundary values. -/
theorem equilibrium_is_affine (n : ℕ) (f : ℕ → ℝ)
    (h : ∀ i, 1 ≤ i → i ≤ n → 2 * f i = f (i - 1) + f (i + 1)) :
    ∀ i, i ≤ n + 1 → f i = f 0 + i * (f (n + 1) - f 0) / (n + 1) := by
  have hd : ∀ i, i ≤ n → f (i + 1) - f i = f 1 - f 0 := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have e := h (k + 1) (by omega) hk
      have e' : f (k + 1 - 1) = f k := by simp
      rw [e'] at e
      have := ih (by omega)
      linarith
  have hlin : ∀ i, i ≤ n + 1 → f i = f 0 + i * (f 1 - f 0) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := hd k (by omega)
      have h2 := ih (by omega)
      push_cast
      linear_combination h1 + h2
  intro i hi
  have hn := hlin (n + 1) le_rfl
  push_cast at hn
  rw [hlin i hi, hn]
  have hpos : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- **H3.** Holographic uniqueness: equilibria agreeing on the boundary agree in the whole bulk. -/
theorem holographic_uniqueness (n : ℕ) (f g : ℕ → ℝ)
    (hf : ∀ i, 1 ≤ i → i ≤ n → 2 * f i = f (i - 1) + f (i + 1))
    (hg : ∀ i, 1 ≤ i → i ≤ n → 2 * g i = g (i - 1) + g (i + 1))
    (h0 : f 0 = g 0) (h1 : f (n + 1) = g (n + 1)) :
    ∀ i, i ≤ n + 1 → f i = g i := by
  intro i hi
  rw [equilibrium_is_affine n f hf i hi, equilibrium_is_affine n g hg i hi, h0, h1]

end LocalGameHolography
