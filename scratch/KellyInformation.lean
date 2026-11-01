import Mathlib

/-!
# Edge is mutual information

K1 Gibbs' inequality. K2 Kelly: betting your true probabilities is optimal. K3 side information raises the
optimal growth rate by exactly the mutual information. K4 mutual information is nonnegative. K5 the average
divergence of posterior from prior equals the mutual information (the quantity a Szilard engine converts to
work at kT ln 2 per bit; the physics is cited, the identity is proved). K6 a sampler with weights w sees the
time average plus Cov(w, z) / mean(w). K7 data processing: passing the side information through any noisy
channel cannot increase it. Logs are natural; distributions are strictly positive on finite types.
-/

open Finset Real

namespace KellyInformation

variable {ι X Y Z : Type*} [Fintype ι] [Fintype X] [Fintype Y] [Fintype Z]

/-- **K1.** Gibbs' inequality. -/
theorem gibbs (p b : ι → ℝ) (hp : ∀ i, 0 < p i) (hb : ∀ i, 0 < b i)
    (hp1 : ∑ i, p i = 1) (hb1 : ∑ i, b i ≤ 1) :
    ∑ i, p i * log (b i) ≤ ∑ i, p i * log (p i) := by
  have key : ∀ i, p i * log (b i) - p i * log (p i) ≤ b i - p i := by
    intro i
    have h := log_le_sub_one_of_pos (div_pos (hb i) (hp i))
    rw [log_div (hb i).ne' (hp i).ne'] at h
    have h2 : p i * (log (b i) - log (p i)) ≤ p i * (b i / p i - 1) := mul_le_mul_of_nonneg_left h (hp i).le
    have e : p i * (b i / p i - 1) = b i - p i := by
      have hp0 := (hp i).ne'
      field_simp
    linarith [h2, e, show p i * (log (b i) - log (p i)) = p i * log (b i) - p i * log (p i) by ring]
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at this
  linarith

/-- **K2.** Kelly: with odds `o`, betting the true probabilities maximises the expected log growth. -/
theorem kelly_optimal (p b o : ι → ℝ) (hp : ∀ i, 0 < p i) (hb : ∀ i, 0 < b i) (ho : ∀ i, 0 < o i)
    (hp1 : ∑ i, p i = 1) (hb1 : ∑ i, b i ≤ 1) :
    ∑ i, p i * log (b i * o i) ≤ ∑ i, p i * log (p i * o i) := by
  have hsplit : ∀ q : ι → ℝ, (∀ i, 0 < q i) →
      ∑ i, p i * log (q i * o i) = ∑ i, p i * log (q i) + ∑ i, p i * log (o i) := by
    intro q hq
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [log_mul (hq i).ne' (ho i).ne']
    ring
  rw [hsplit b hb, hsplit p hp]
  linarith [gibbs p b hp hb hp1 hb1]

/-- Marginals and mutual information of a joint distribution on `X × Y`. -/
noncomputable def margX (p : X → Y → ℝ) (x : X) : ℝ := ∑ y, p x y
noncomputable def margY (p : X → Y → ℝ) (y : Y) : ℝ := ∑ x, p x y
noncomputable def MI (p : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, p x y * log (p x y / (margX p x * margY p y))

lemma margX_pos [Nonempty Y] (p : X → Y → ℝ) (hp : ∀ x y, 0 < p x y) (x : X) : 0 < margX p x :=
  Finset.sum_pos (fun y _ => hp x y) Finset.univ_nonempty

lemma margY_pos [Nonempty X] (p : X → Y → ℝ) (hp : ∀ x y, 0 < p x y) (y : Y) : 0 < margY p y :=
  Finset.sum_pos (fun x _ => hp x y) Finset.univ_nonempty

/-- **K3.** The value of side information: the optimal growth rate when betting on `X` after seeing `Y`
equals the optimal rate without `Y` plus exactly `I(X;Y)`. -/
theorem side_info_gain [Nonempty X] [Nonempty Y] (p : X → Y → ℝ) (o : X → ℝ)
    (hp : ∀ x y, 0 < p x y) (ho : ∀ x, 0 < o x) :
    ∑ x, ∑ y, p x y * log (p x y / margY p y * o x) =
      ∑ x, margX p x * log (margX p x * o x) + MI p := by
  have hx := margX_pos p hp
  have hy := margY_pos p hp
  have hterm : ∀ x y, p x y * log (p x y / margY p y * o x) =
      p x y * log (p x y / (margX p x * margY p y)) + p x y * log (margX p x * o x) := by
    intro x y
    rw [← mul_add, ← log_mul (div_pos (hp x y) (mul_pos (hx x) (hy y))).ne' (mul_pos (hx x) (ho x)).ne']
    congr 2
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff (hy y).ne' (mul_pos (hx x) (hy y)).ne']
    ring
  simp_rw [hterm, Finset.sum_add_distrib]
  unfold MI
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_mul]
  rfl

/-- **K4.** Mutual information is nonnegative. -/
theorem MI_nonneg [Nonempty X] [Nonempty Y] (p : X → Y → ℝ) (hp : ∀ x y, 0 < p x y)
    (hp1 : ∑ x, ∑ y, p x y = 1) : 0 ≤ MI p := by
  have hx := margX_pos p hp
  have hy := margY_pos p hp
  have sx : ∑ x, margX p x = 1 := hp1
  have sy : ∑ y, margY p y = 1 := by
    unfold margY
    rw [Finset.sum_comm]
    exact hp1
  have g := gibbs (fun q : X × Y => p q.1 q.2) (fun q => margX p q.1 * margY p q.2)
    (fun q => hp q.1 q.2) (fun q => mul_pos (hx q.1) (hy q.2))
    (by rw [Fintype.sum_prod_type]; exact hp1)
    (le_of_eq (by rw [Fintype.sum_prod_type]; simp_rw [← Finset.mul_sum, sy, mul_one]; exact sx))
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at g
  simp only at g
  unfold MI
  have e : ∀ x y, p x y * log (p x y / (margX p x * margY p y)) =
      p x y * log (p x y) - p x y * log (margX p x * margY p y) := by
    intro x y
    rw [log_div (hp x y).ne' (mul_pos (hx x) (hy y)).ne']
    ring
  simp_rw [e, Finset.sum_sub_distrib]
  linarith

/-- **K5.** The demon's accounting: the `Y`-average of the divergence of the posterior `p(·|y)` from the
prior `p(·)` equals the mutual information. -/
theorem posterior_divergence_eq_MI [Nonempty X] [Nonempty Y] (p : X → Y → ℝ) (hp : ∀ x y, 0 < p x y) :
    ∑ y, margY p y * ∑ x, (p x y / margY p y) * log ((p x y / margY p y) / margX p x) = MI p := by
  have hx := margX_pos p hp
  have hy := margY_pos p hp
  unfold MI
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have h1 := (hy y).ne'
  rw [div_div, mul_comm (margY p y) (margX p x), ← mul_assoc,
    show margY p y * (p x y / margY p y) = p x y by field_simp]

/-- **K6.** A sampler with weights `w` over `n` time points sees the time average of `z` plus
`Cov(w, z) / mean(w)`; with no covariance it sees exactly the time average. -/
theorem weighted_sampler (n : ℕ) (hn : 0 < n) (w z : Fin n → ℝ) (hw : 0 < ∑ t, w t) :
    (∑ t, w t * z t) / (∑ t, w t) - (∑ t, z t) / n =
      ((∑ t, w t * z t) / n - (∑ t, w t) / n * ((∑ t, z t) / n)) / ((∑ t, w t) / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hw' := hw.ne'
  field_simp

/-- The log-sum inequality. -/
theorem log_sum (a b : ι → ℝ) [Nonempty ι] (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    (∑ i, a i) * log ((∑ i, a i) / (∑ i, b i)) ≤ ∑ i, a i * log (a i / b i) := by
  set A := ∑ i, a i with hA
  set B := ∑ i, b i with hB
  have hA0 : 0 < A := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have hB0 : 0 < B := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have g := gibbs (fun i => a i / A) (fun i => b i / B) (fun i => div_pos (ha i) hA0)
    (fun i => div_pos (hb i) hB0) (by rw [← Finset.sum_div]; exact div_self hA0.ne')
    (le_of_eq (by rw [← Finset.sum_div]; exact div_self hB0.ne'))
  have e1 : ∀ i, a i / A * log (b i / B) = A⁻¹ * (a i * log (b i) - a i * log B) := by
    intro i; rw [log_div (hb i).ne' hB0.ne']; ring
  have e2 : ∀ i, a i / A * log (a i / A) = A⁻¹ * (a i * log (a i) - a i * log A) := by
    intro i; rw [log_div (ha i).ne' hA0.ne']; ring
  simp only [e1, e2] at g
  rw [← Finset.mul_sum, ← Finset.mul_sum] at g
  have g2 := le_of_mul_le_mul_left g (inv_pos.mpr hA0)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul] at g2
  have e3 : ∀ i, a i * log (a i / b i) = a i * log (a i) - a i * log (b i) := by
    intro i; rw [log_div (ha i).ne' (hb i).ne']; ring
  rw [Finset.sum_congr rfl (fun i _ => e3 i), Finset.sum_sub_distrib, log_div hA0.ne' hB0.ne', mul_sub]
  linarith

/-- **K7.** Data processing: if `Z` is produced from `Y` by any channel `κ` (for example a noisy delay),
the mutual information of `X` with `Z` is at most that with `Y`. -/
theorem data_processing [Nonempty X] [Nonempty Y] [Nonempty Z] (p : X → Y → ℝ) (κ : Y → Z → ℝ)
    (hp : ∀ x y, 0 < p x y) (hκ : ∀ y z, 0 < κ y z) (hκ1 : ∀ y, ∑ z, κ y z = 1) :
    MI (fun x z => ∑ y, p x y * κ y z) ≤ MI p := by
  have hx := margX_pos p hp
  have hy := margY_pos p hp
  have hqx : ∀ x, margX (fun x z => ∑ y, p x y * κ y z) x = margX p x := by
    intro x
    unfold margX
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.mul_sum, hκ1, mul_one]
  have hqz : ∀ z, margY (fun x z => ∑ y, p x y * κ y z) z = ∑ y, margY p y * κ y z := by
    intro z
    unfold margY
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_mul]
  have key : ∀ x z, (∑ y, p x y * κ y z) * log ((∑ y, p x y * κ y z) /
      (margX (fun x z => ∑ y, p x y * κ y z) x * margY (fun x z => ∑ y, p x y * κ y z) z)) ≤
      ∑ y, p x y * κ y z * log (p x y / (margX p x * margY p y)) := by
    intro x z
    have ls := log_sum (fun y => p x y * κ y z) (fun y => margX p x * margY p y * κ y z)
      (fun y => mul_pos (hp x y) (hκ y z)) (fun y => mul_pos (mul_pos (hx x) (hy y)) (hκ y z))
    have sb : ∑ y, margX p x * margY p y * κ y z =
        margX (fun x z => ∑ y, p x y * κ y z) x * margY (fun x z => ∑ y, p x y * κ y z) z := by
      rw [hqx, hqz, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    have ratio : ∀ y, p x y * κ y z / (margX p x * margY p y * κ y z) = p x y / (margX p x * margY p y) := by
      intro y
      rw [div_eq_div_iff (mul_pos (mul_pos (hx x) (hy y)) (hκ y z)).ne' (mul_pos (hx x) (hy y)).ne']
      ring
    simp only [ratio] at ls
    rw [sb] at ls
    exact ls
  calc MI (fun x z => ∑ y, p x y * κ y z)
      = ∑ x, ∑ z, (∑ y, p x y * κ y z) * log ((∑ y, p x y * κ y z) /
          (margX (fun x z => ∑ y, p x y * κ y z) x * margY (fun x z => ∑ y, p x y * κ y z) z)) := rfl
    _ ≤ ∑ x, ∑ z, ∑ y, p x y * κ y z * log (p x y / (margX p x * margY p y)) :=
        Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun z _ => key x z))
    _ = MI p := by
        unfold MI
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        have e : ∀ z, p x y * κ y z * log (p x y / (margX p x * margY p y)) =
            (p x y * log (p x y / (margX p x * margY p y))) * κ y z := by intro z; ring
        simp_rw [e]
        rw [← Finset.mul_sum, hκ1, mul_one]

end KellyInformation
