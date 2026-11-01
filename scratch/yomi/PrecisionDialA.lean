import Mathlib

/-!
# PrecisionDialA: the precision-weighting dial

Estimate a quantity `θ` by `w · observation + (1 - w) · prior`, `w ∈ ℝ`, where the prior
error has variance `σp2 > 0` and the independent observation error has variance `σx2 > 0`.
The mean squared error is taken as the definition
`L σp2 σx2 w = w ^ 2 * σx2 + (1 - w) ^ 2 * σp2`, and is also derived from a finite model.

PROVED
* `mse_eq_L_of_uncorrelated`: on a finite space with weights `r` (no positivity or
  normalization is needed for this identity), if the prior error `ep` and observation error
  `ex` have zero weighted mean and zero weighted cross moment, then the mean squared error of the weighted estimate equals
  `L (var ep) (var ex) w`, with `var` the weighted variance.
* `mse_eq_L_of_independent`: the same on a product space `α × β` with product weights
  `p a * q b`, prior error depending only on `a` and observation error only on `b`
  (genuine independence); the variances are the marginal variances `∑ p a * ep a ^ 2`,
  `∑ q b * ex b ^ 2`.
* (1) `L_wstar_le`, `L_eq_L_wstar_iff`, `L_wstar_lt`, `isMinOn_L`, `unique_minimizer`:
  `L` attains its minimum at `w* = σp2 / (σp2 + σx2)` and only there.
* (2) `L_sub_L_wstar`: `L w - L w* = (w - w*) ^ 2 * (σp2 + σx2)`;
  `L_wstar_add_eq_L_wstar_sub`: overshooting and undershooting by the same `d` cost the same.
* (3) `L_wstar_eq`: `L w* = σp2 * σx2 / (σp2 + σx2)`; `L_wstar_lt_σp2`, `L_wstar_lt_σx2`.
* (4) `wstar_strictMonoOn_σp2`, `wstar_strictAntiOn_σx2` (and the two-point forms
  `wstar_lt_of_σp2_lt`, `wstar_lt_of_σx2_lt`): `w*` is strictly increasing in `σp2` and
  strictly decreasing in `σx2` on the positive reals.

INTERPRETED (not formal content)
* `w > w*` overweights the data relative to the prior: observation noise is read as structure.
* `w < w*` overweights the prior: evidence is ignored.
* Calibration is choosing `w = w*`; by (2) either miscalibration costs exactly
  `(w - w*) ^ 2 * (σp2 + σx2)`.
-/

namespace PrecisionDialA

open Finset

/-- Mean squared error of the estimate `w · obs + (1 - w) · prior`. -/
def L (σp2 σx2 w : ℝ) : ℝ := w ^ 2 * σx2 + (1 - w) ^ 2 * σp2

/-- The calibrated weight on the observation. -/
noncomputable def wstar (σp2 σx2 : ℝ) : ℝ := σp2 / (σp2 + σx2)

/-! ## Finite model -/

section FiniteModel

variable {Ω : Type*} [Fintype Ω]

/-- Weighted mean on a finite space. -/
def mean (r : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ i, r i * f i

/-- Weighted variance on a finite space. -/
def var (r : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ i, r i * (f i - mean r f) ^ 2

/-- Mean squared error of the weighted estimate when `prior = θ + ep`, `obs = θ + ex`. -/
def mse (r : Ω → ℝ) (θ : ℝ) (ep ex : Ω → ℝ) (w : ℝ) : ℝ :=
  ∑ i, r i * (w * (θ + ex i) + (1 - w) * (θ + ep i) - θ) ^ 2

theorem mse_eq_L_of_uncorrelated (r : Ω → ℝ) (θ : ℝ) (ep ex : Ω → ℝ) (w : ℝ)
    (hp : mean r ep = 0) (hx : mean r ex = 0) (hpx : ∑ i, r i * (ep i * ex i) = 0) :
    mse r θ ep ex w = L (var r ep) (var r ex) w := by
  unfold mse L var
  rw [hp, hx]
  have key : ∑ i, r i * (w * (θ + ex i) + (1 - w) * (θ + ep i) - θ) ^ 2
      = w ^ 2 * ∑ i, r i * (ex i - 0) ^ 2 + (1 - w) ^ 2 * ∑ i, r i * (ep i - 0) ^ 2
        + 2 * w * (1 - w) * ∑ i, r i * (ep i * ex i) := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [key, hpx]
  ring

variable {α β : Type*} [Fintype α] [Fintype β]

theorem mse_eq_L_of_independent (p : α → ℝ) (q : β → ℝ) (hp1 : ∑ a, p a = 1)
    (hq1 : ∑ b, q b = 1) (θ : ℝ) (ep : α → ℝ) (ex : β → ℝ)
    (hp : ∑ a, p a * ep a = 0) (hx : ∑ b, q b * ex b = 0) (w : ℝ) :
    mse (fun z : α × β => p z.1 * q z.2) θ (fun z => ep z.1) (fun z => ex z.2) w
      = L (∑ a, p a * ep a ^ 2) (∑ b, q b * ex b ^ 2) w := by
  set r : α × β → ℝ := fun z => p z.1 * q z.2
  have hmp : mean r (fun z => ep z.1) = 0 := by
    unfold mean
    rw [Fintype.sum_prod_type]
    simp only [r]
    have : ∀ a, ∑ b, p a * q b * ep a = p a * ep a * ∑ b, q b := fun a => by
      rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
    simp_rw [this, hq1, mul_one, hp]
  have hmx : mean r (fun z => ex z.2) = 0 := by
    unfold mean
    rw [Fintype.sum_prod_type]
    simp only [r]
    have : ∀ a, ∑ b, p a * q b * ex b = p a * ∑ b, q b * ex b := fun a => by
      rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
    simp_rw [this, hx, mul_zero, sum_const_zero]
  have hpx : ∑ z, r z * (ep z.1 * ex z.2) = 0 := by
    rw [Fintype.sum_prod_type]
    simp only [r]
    have : ∀ a, ∑ b, p a * q b * (ep a * ex b) = p a * ep a * ∑ b, q b * ex b := fun a => by
      rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
    simp_rw [this, hx, mul_zero, sum_const_zero]
  rw [mse_eq_L_of_uncorrelated r θ _ _ w hmp hmx hpx]
  have hvp : var r (fun z => ep z.1) = ∑ a, p a * ep a ^ 2 := by
    unfold var
    rw [hmp, Fintype.sum_prod_type]
    simp only [r]
    have : ∀ a, ∑ b, p a * q b * (ep a - 0) ^ 2 = p a * ep a ^ 2 * ∑ b, q b := fun a => by
      rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
    simp_rw [this, hq1, mul_one]
  have hvx : var r (fun z => ex z.2) = ∑ b, q b * ex b ^ 2 := by
    unfold var
    rw [hmx, Fintype.sum_prod_type]
    simp only [r]
    have : ∀ a, ∑ b, p a * q b * (ex b - 0) ^ 2 = p a * ∑ b, q b * ex b ^ 2 := fun a => by
      rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
    simp_rw [this, ← sum_mul, hp1, one_mul]
  rw [hvp, hvx]

end FiniteModel

/-! ## The dial -/

section Dial

variable {σp2 σx2 : ℝ}

/-- (2) Exact quadratic excess loss. -/
theorem L_sub_L_wstar (hp : 0 < σp2) (hx : 0 < σx2) (w : ℝ) :
    L σp2 σx2 w - L σp2 σx2 (wstar σp2 σx2) = (w - wstar σp2 σx2) ^ 2 * (σp2 + σx2) := by
  have hs : σp2 + σx2 ≠ 0 := by positivity
  unfold L wstar
  field_simp
  ring

/-- Overshooting and undershooting the calibrated weight by `d` cost the same. -/
theorem L_wstar_add_eq_L_wstar_sub (hp : 0 < σp2) (hx : 0 < σx2) (d : ℝ) :
    L σp2 σx2 (wstar σp2 σx2 + d) = L σp2 σx2 (wstar σp2 σx2 - d) := by
  have h1 := L_sub_L_wstar hp hx (wstar σp2 σx2 + d)
  have h2 := L_sub_L_wstar hp hx (wstar σp2 σx2 - d)
  have : L σp2 σx2 (wstar σp2 σx2 + d) - L σp2 σx2 (wstar σp2 σx2 - d) = 0 := by
    linear_combination h1 - h2
  linarith

/-- (1) `w*` is a minimizer. -/
theorem L_wstar_le (hp : 0 < σp2) (hx : 0 < σx2) (w : ℝ) :
    L σp2 σx2 (wstar σp2 σx2) ≤ L σp2 σx2 w := by
  have h := L_sub_L_wstar hp hx w
  have : 0 ≤ (w - wstar σp2 σx2) ^ 2 * (σp2 + σx2) := by positivity
  linarith

/-- (1) Equality with the minimum value holds only at `w*`. -/
theorem L_eq_L_wstar_iff (hp : 0 < σp2) (hx : 0 < σx2) (w : ℝ) :
    L σp2 σx2 w = L σp2 σx2 (wstar σp2 σx2) ↔ w = wstar σp2 σx2 := by
  have h := L_sub_L_wstar hp hx w
  have hs : 0 < σp2 + σx2 := by positivity
  constructor
  · intro he
    have h0 : (w - wstar σp2 σx2) ^ 2 * (σp2 + σx2) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0)
    · exact absurd h0 hs.ne'
  · rintro rfl; rfl

/-- (1) Strict inequality away from `w*`. -/
theorem L_wstar_lt (hp : 0 < σp2) (hx : 0 < σx2) {w : ℝ} (hw : w ≠ wstar σp2 σx2) :
    L σp2 σx2 (wstar σp2 σx2) < L σp2 σx2 w :=
  lt_of_le_of_ne (L_wstar_le hp hx w) fun h => hw ((L_eq_L_wstar_iff hp hx w).mp h.symm)

theorem isMinOn_L (hp : 0 < σp2) (hx : 0 < σx2) :
    IsMinOn (L σp2 σx2) Set.univ (wstar σp2 σx2) :=
  fun w _ => L_wstar_le hp hx w

/-- (1) `w*` is the unique global minimizer. -/
theorem unique_minimizer (hp : 0 < σp2) (hx : 0 < σx2) :
    ∃! w₀ : ℝ, ∀ w, L σp2 σx2 w₀ ≤ L σp2 σx2 w := by
  refine ⟨wstar σp2 σx2, L_wstar_le hp hx, fun w₀ hw₀ => ?_⟩
  have h1 := hw₀ (wstar σp2 σx2)
  have h2 := L_wstar_le hp hx w₀
  exact (L_eq_L_wstar_iff hp hx w₀).mp (le_antisymm h1 h2)

/-- (3) The minimum value. -/
theorem L_wstar_eq (hp : 0 < σp2) (hx : 0 < σx2) :
    L σp2 σx2 (wstar σp2 σx2) = σp2 * σx2 / (σp2 + σx2) := by
  have hs : σp2 + σx2 ≠ 0 := by positivity
  unfold L wstar
  field_simp
  ring

/-- (3) The minimum is below the prior variance. -/
theorem L_wstar_lt_σp2 (hp : 0 < σp2) (hx : 0 < σx2) :
    L σp2 σx2 (wstar σp2 σx2) < σp2 := by
  rw [L_wstar_eq hp hx, div_lt_iff₀ (by positivity)]
  nlinarith

/-- (3) The minimum is below the observation variance. -/
theorem L_wstar_lt_σx2 (hp : 0 < σp2) (hx : 0 < σx2) :
    L σp2 σx2 (wstar σp2 σx2) < σx2 := by
  rw [L_wstar_eq hp hx, div_lt_iff₀ (by positivity)]
  nlinarith

/-- (4) `w*` strictly increases with the prior variance. -/
theorem wstar_lt_of_σp2_lt {a b : ℝ} (ha : 0 < a) (hab : a < b) (hx : 0 < σx2) :
    wstar a σx2 < wstar b σx2 := by
  have hb : 0 < b := ha.trans hab
  unfold wstar
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- (4) `w*` strictly decreases with the observation variance. -/
theorem wstar_lt_of_σx2_lt {a b : ℝ} (ha : 0 < a) (hab : a < b) (hp : 0 < σp2) :
    wstar σp2 b < wstar σp2 a := by
  have hb : 0 < b := ha.trans hab
  unfold wstar
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem wstar_strictMonoOn_σp2 (hx : 0 < σx2) :
    StrictMonoOn (fun s => wstar s σx2) (Set.Ioi 0) :=
  fun _ ha _ _ hab => wstar_lt_of_σp2_lt ha hab hx

theorem wstar_strictAntiOn_σx2 (hp : 0 < σp2) :
    StrictAntiOn (fun s => wstar σp2 s) (Set.Ioi 0) :=
  fun _ ha _ _ hab => wstar_lt_of_σx2_lt ha hab hp

end Dial

end PrecisionDialA
