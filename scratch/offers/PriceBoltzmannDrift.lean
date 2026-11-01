import Mathlib

/-!
# Price's equation with Boltzmann-count fitness

Setting: `ι` a finite type, `q : ι → ℝ` a weighting, `w : ι → ℝ` a fitness.
`mean q z = ∑ i, q i * z i`, `cov q w z = mean q (w * z) - mean q w * mean q z`,
`reweight q w i = q i * w i / mean q w`, and the Boltzmann-count fitness
`boltz g β E i = g i * exp (-β * E i)`.

PROVED
* `mean_pos`: if `ι` is nonempty and `q, w > 0` pointwise, then `mean q w > 0`.
* `reweight_sum_one`: under the same hypotheses, `∑ i, reweight q w i = 1`.
* `mean_reweight`: `mean (reweight q w) z = mean q (w * z) / mean q w`.
* `price`: if `mean q w ≠ 0` then for every trait `z`,
  `mean q w * (mean (reweight q w) z - mean q z) = cov q w z` (Price's equation;
  needs neither positivity nor `∑ q = 1`).
* `price_div`: the same in the form `mean q' z - mean q z = cov q w z / mean q w`.
* `boltz_pos`: `g > 0` implies `boltz g β E i > 0`.
* `log_boltz`: `g > 0` implies `log (boltz g β E i) = log (g i) - β * E i`.
* `boltz_entropy_drift`: with `S = log ∘ g`,
  `mean q' S - mean q S = cov q w S / mean q w` for `w = boltz g β E`.
* `boltz_energy_drift`: `mean q' E - mean q E = cov q w E / mean q w` for `w = boltz g β E`.
* `cov_double_sum`: if `∑ q = 1` then
  `2 * cov q w z = ∑ i, ∑ j, q i * q j * ((w i - w j) * (z i - z j))`.
* `term_log_nonneg`: for `a, b > 0`, `(a - b) * (log a - log b) ≥ 0`.
* `term_log_pos`: for `a, b > 0` with `a ≠ b`, `(a - b) * (log a - log b) > 0`.
* `cov_log_nonneg`: if `∑ q = 1`, `q ≥ 0`, `w > 0`, then `cov q w (log ∘ w) ≥ 0`.
* `cov_log_eq_zero_iff`: if `∑ q = 1`, `q > 0`, `w > 0`, then
  `cov q w (log ∘ w) = 0 ↔ ∀ i j, w i = w j`.
* `drift_log_nonneg`: for any positive `w` (with `ι` nonempty, `q > 0`, `∑ q = 1`),
  `mean q' (log ∘ w) - mean q (log ∘ w) = cov q w (log ∘ w) / mean q w` and this is `≥ 0`.
* `drift_log_eq_zero_iff`: the drift of `log ∘ w` vanishes iff `w` is constant.
* `boltz_drift_log_nonneg`: for `w = boltz g β E` and `L i = log (g i) - β * E i`,
  `mean q' L - mean q L = cov q w L / mean q w ≥ 0`.
* `boltz_drift_log_eq_zero_iff`: that drift is `0` iff `boltz g β E` is constant on `ι`.
-/

namespace PriceBoltzmannDrift

open Finset Real

variable {ι : Type*} [Fintype ι]

/-- Expectation of `z` under the weighting `q`. -/
noncomputable def mean (q z : ι → ℝ) : ℝ := ∑ i, q i * z i

/-- Covariance of `w` and `z` under `q`. -/
noncomputable def cov (q w z : ι → ℝ) : ℝ :=
  mean q (fun i => w i * z i) - mean q w * mean q z

/-- Selected distribution `q' i = q i * w i / wbar`. -/
noncomputable def reweight (q w : ι → ℝ) (i : ι) : ℝ := q i * w i / mean q w

/-- Boltzmann-count fitness `g i * exp (-β * E i)`. -/
noncomputable def boltz (g : ι → ℝ) (β : ℝ) (E : ι → ℝ) (i : ι) : ℝ :=
  g i * exp (-β * E i)

theorem mean_pos [Nonempty ι] {q w : ι → ℝ} (hq : ∀ i, 0 < q i) (hw : ∀ i, 0 < w i) :
    0 < mean q w :=
  Finset.sum_pos (fun i _ => mul_pos (hq i) (hw i)) Finset.univ_nonempty

theorem reweight_sum_one [Nonempty ι] {q w : ι → ℝ} (hq : ∀ i, 0 < q i)
    (hw : ∀ i, 0 < w i) : ∑ i, reweight q w i = 1 := by
  have h := (mean_pos hq hw).ne'
  unfold reweight
  rw [← Finset.sum_div]
  exact div_self h

theorem mean_reweight {q w : ι → ℝ} (z : ι → ℝ) :
    mean (reweight q w) z = mean q (fun i => w i * z i) / mean q w := by
  unfold reweight mean
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

theorem price {q w : ι → ℝ} (hW : mean q w ≠ 0) (z : ι → ℝ) :
    mean q w * (mean (reweight q w) z - mean q z) = cov q w z := by
  rw [mean_reweight, cov, mul_sub, mul_div_cancel₀ _ hW]

theorem price_div {q w : ι → ℝ} (hW : mean q w ≠ 0) (z : ι → ℝ) :
    mean (reweight q w) z - mean q z = cov q w z / mean q w := by
  rw [← price hW z, mul_div_cancel_left₀ _ hW]

omit [Fintype ι] in
theorem boltz_pos {g : ι → ℝ} (hg : ∀ i, 0 < g i) (β : ℝ) (E : ι → ℝ) (i : ι) :
    0 < boltz g β E i :=
  mul_pos (hg i) (exp_pos _)

omit [Fintype ι] in
theorem log_boltz {g : ι → ℝ} (hg : ∀ i, 0 < g i) (β : ℝ) (E : ι → ℝ) (i : ι) :
    log (boltz g β E i) = log (g i) - β * E i := by
  unfold boltz
  rw [log_mul (hg i).ne' (exp_pos _).ne', log_exp]
  ring

theorem boltz_entropy_drift [Nonempty ι] {q g : ι → ℝ} (hq : ∀ i, 0 < q i)
    (hg : ∀ i, 0 < g i) (β : ℝ) (E : ι → ℝ) :
    mean (reweight q (boltz g β E)) (fun i => log (g i)) - mean q (fun i => log (g i)) =
      cov q (boltz g β E) (fun i => log (g i)) / mean q (boltz g β E) :=
  price_div (mean_pos hq (boltz_pos hg β E)).ne' _

theorem boltz_energy_drift [Nonempty ι] {q g : ι → ℝ} (hq : ∀ i, 0 < q i)
    (hg : ∀ i, 0 < g i) (β : ℝ) (E : ι → ℝ) :
    mean (reweight q (boltz g β E)) E - mean q E =
      cov q (boltz g β E) E / mean q (boltz g β E) :=
  price_div (mean_pos hq (boltz_pos hg β E)).ne' _

theorem cov_double_sum {q : ι → ℝ} (hsum : ∑ i, q i = 1) (w z : ι → ℝ) :
    2 * cov q w z = ∑ i, ∑ j, q i * q j * ((w i - w j) * (z i - z j)) := by
  have key : ∀ i j, q i * q j * ((w i - w j) * (z i - z j)) =
      q j * (q i * (w i * z i)) + q i * (q j * (w j * z j))
        - (q i * w i) * (q j * z j) - (q j * w j) * (q i * z i) := by
    intro i j; ring
  simp_rw [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, hsum]
  unfold cov mean
  simp only [one_mul, ← Finset.mul_sum]
  ring

theorem term_log_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (a - b) * (log a - log b) := by
  rcases le_total a b with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith)
      (by linarith [log_le_log ha h])
  · exact mul_nonneg (by linarith) (by linarith [log_le_log hb h])

theorem term_log_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    0 < (a - b) * (log a - log b) := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact mul_pos_of_neg_of_neg (by linarith) (by linarith [log_lt_log ha h])
  · exact mul_pos (by linarith) (by linarith [log_lt_log hb h])

theorem cov_log_nonneg {q w : ι → ℝ} (hsum : ∑ i, q i = 1) (hq : ∀ i, 0 ≤ q i)
    (hw : ∀ i, 0 < w i) : 0 ≤ cov q w (fun i => log (w i)) := by
  have h2 := cov_double_sum hsum w (fun i => log (w i))
  have : 0 ≤ ∑ i, ∑ j, q i * q j * ((w i - w j) * (log (w i) - log (w j))) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hq i) (hq j)) (term_log_nonneg (hw i) (hw j))
  linarith

theorem cov_log_eq_zero_iff {q w : ι → ℝ} (hsum : ∑ i, q i = 1) (hq : ∀ i, 0 < q i)
    (hw : ∀ i, 0 < w i) : cov q w (fun i => log (w i)) = 0 ↔ ∀ i j, w i = w j := by
  have h2 := cov_double_sum hsum w (fun i => log (w i))
  have hnn : ∀ i j, 0 ≤ q i * q j * ((w i - w j) * (log (w i) - log (w j))) := fun i j =>
    mul_nonneg (mul_nonneg (hq i).le (hq j).le) (term_log_nonneg (hw i) (hw j))
  constructor
  · intro h0 i j
    have hS : ∑ i, ∑ j, q i * q j * ((w i - w j) * (log (w i) - log (w j))) = 0 := by
      rw [← h2, h0, mul_zero]
    rw [Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)] at hS
    have hrow := hS i (Finset.mem_univ _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)] at hrow
    have hij := hrow j (Finset.mem_univ _)
    by_contra hne
    have := mul_pos (mul_pos (hq i) (hq j)) (term_log_pos (hw i) (hw j) hne)
    linarith
  · intro hc
    have hS : ∑ i, ∑ j, q i * q j * ((w i - w j) * (log (w i) - log (w j))) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rw [hc i j]; ring
    linarith

theorem drift_log_nonneg [Nonempty ι] {q w : ι → ℝ} (hsum : ∑ i, q i = 1)
    (hq : ∀ i, 0 < q i) (hw : ∀ i, 0 < w i) :
    mean (reweight q w) (fun i => log (w i)) - mean q (fun i => log (w i)) =
        cov q w (fun i => log (w i)) / mean q w ∧
      0 ≤ mean (reweight q w) (fun i => log (w i)) - mean q (fun i => log (w i)) := by
  have hW := mean_pos hq hw
  have hd := price_div hW.ne' (fun i => log (w i))
  refine ⟨hd, ?_⟩
  rw [hd]
  exact div_nonneg (cov_log_nonneg hsum (fun i => (hq i).le) hw) hW.le

theorem drift_log_eq_zero_iff [Nonempty ι] {q w : ι → ℝ} (hsum : ∑ i, q i = 1)
    (hq : ∀ i, 0 < q i) (hw : ∀ i, 0 < w i) :
    mean (reweight q w) (fun i => log (w i)) - mean q (fun i => log (w i)) = 0 ↔
      ∀ i j, w i = w j := by
  have hW := mean_pos hq hw
  rw [price_div hW.ne', div_eq_zero_iff, or_iff_left hW.ne', cov_log_eq_zero_iff hsum hq hw]

theorem boltz_drift_log_nonneg [Nonempty ι] {q g : ι → ℝ} (hsum : ∑ i, q i = 1)
    (hq : ∀ i, 0 < q i) (hg : ∀ i, 0 < g i) (β : ℝ) (E : ι → ℝ) :
    mean (reweight q (boltz g β E)) (fun i => log (g i) - β * E i)
        - mean q (fun i => log (g i) - β * E i) =
        cov q (boltz g β E) (fun i => log (g i) - β * E i) / mean q (boltz g β E) ∧
      0 ≤ mean (reweight q (boltz g β E)) (fun i => log (g i) - β * E i)
        - mean q (fun i => log (g i) - β * E i) := by
  have hL : (fun i => log (g i) - β * E i) = fun i => log (boltz g β E i) :=
    funext fun i => (log_boltz hg β E i).symm
  rw [hL]
  exact drift_log_nonneg hsum hq (boltz_pos hg β E)

theorem boltz_drift_log_eq_zero_iff [Nonempty ι] {q g : ι → ℝ} (hsum : ∑ i, q i = 1)
    (hq : ∀ i, 0 < q i) (hg : ∀ i, 0 < g i) (β : ℝ) (E : ι → ℝ) :
    mean (reweight q (boltz g β E)) (fun i => log (g i) - β * E i)
        - mean q (fun i => log (g i) - β * E i) = 0 ↔
      ∀ i j, boltz g β E i = boltz g β E j := by
  have hL : (fun i => log (g i) - β * E i) = fun i => log (boltz g β E i) :=
    funext fun i => (log_boltz hg β E i).symm
  rw [hL]
  exact drift_log_eq_zero_iff hsum hq (boltz_pos hg β E)

end PriceBoltzmannDrift
