import Mathlib

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace ZeroBias

/-- `kappa P₀ t = ∫_{(t,∞)} s P₀(ds)`: the note's κ. -/
def kappa (P₀ : Measure ℝ) (t : ℝ) : ℝ := ∫ s in Ioi t, s ∂P₀

/-- The transport weight `g(x,t) = x·1{0<t<x} − x·1{x≤t≤0}` of the note's Fubini proof. -/
def gWeight (x t : ℝ) : ℝ :=
  if 0 < t ∧ t < x then x else if x ≤ t ∧ t ≤ 0 then -x else 0

lemma gWeight_nonneg (x t : ℝ) : 0 ≤ gWeight x t := by
  unfold gWeight
  split_ifs with h1 h2
  · linarith [h1.1, h1.2]
  · linarith [h2.1, h2.2]
  · exact le_rfl

lemma gWeight_eq_pos {x : ℝ} (hx : 0 < x) (t : ℝ) :
    gWeight x t = (Ioo 0 x).indicator (fun _ => x) t := by
  unfold gWeight; simp only [indicator, mem_Ioo]
  have h2 : ¬ (x ≤ t ∧ t ≤ 0) := fun h => by linarith [h.1, h.2]
  by_cases h1 : 0 < t ∧ t < x <;> simp [h1, h2]

lemma gWeight_eq_neg {x : ℝ} (hx : x < 0) (t : ℝ) :
    gWeight x t = (Icc x 0).indicator (fun _ => -x) t := by
  unfold gWeight; simp only [indicator, mem_Icc]
  have h1 : ¬ (0 < t ∧ t < x) := fun h => by linarith [h.1, h.2]
  by_cases h2 : x ≤ t ∧ t ≤ 0 <;> simp [h1, h2]

lemma gWeight_zero (t : ℝ) : gWeight 0 t = 0 := by
  unfold gWeight; split_ifs <;> simp

lemma measurable_gWeight : Measurable (fun p : ℝ × ℝ => gWeight p.1 p.2) := by
  unfold gWeight
  refine Measurable.ite ?_ measurable_fst (Measurable.ite ?_ measurable_fst.neg measurable_const)
  · exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  · exact (measurableSet_le measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)

lemma abs_gWeight_le (x t : ℝ) : |gWeight x t| ≤ |x| := by
  unfold gWeight; split_ifs <;> simp

/-- Pointwise step of the note's proof: `x (f x − f 0) = ∫ f'(t) g(x,t) dt`. -/
lemma mul_sub_eq_integral_gWeight (f : ℝ → ℝ) (hf : Differentiable ℝ f) (L : ℝ)
    (hL : ∀ t, |deriv f t| ≤ L) (x : ℝ) :
    x * (f x - f 0) = ∫ t, deriv f t * gWeight x t := by
  have hmeas : Measurable (deriv f) := measurable_deriv f
  have hint : ∀ a b : ℝ, IntervalIntegrable (deriv f) volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := L)).mono_fun' hmeas.aestronglyMeasurable ?_
    exact ae_of_all _ fun t => by simpa [Real.norm_eq_abs] using hL t
  have hftc : ∀ a b : ℝ, ∫ t in a..b, deriv f t = f b - f a := fun a b =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => (hf t).hasDerivAt) (hint a b)
  rcases lt_trichotomy 0 x with hx | rfl | hx
  · simp_rw [gWeight_eq_pos hx]
    have : ∀ t, deriv f t * (Ioo 0 x).indicator (fun _ => x) t
        = (Ioo 0 x).indicator (fun t => x * deriv f t) t := by
      intro t; simp [indicator]; split_ifs <;> ring
    simp_rw [this]
    rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hx.le, intervalIntegral.integral_const_mul, hftc]
  · simp [gWeight_zero]
  · simp_rw [gWeight_eq_neg hx]
    have : ∀ t, deriv f t * (Icc x 0).indicator (fun _ => -x) t
        = (Icc x 0).indicator (fun t => -x * deriv f t) t := by
      intro t; simp [indicator]; split_ifs <;> ring
    simp_rw [this]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hx.le, intervalIntegral.integral_const_mul, hftc]
    ring

end ZeroBias

namespace ZeroBias

lemma integrable_gWeight (x : ℝ) : Integrable (gWeight x) volume := by
  rcases lt_trichotomy 0 x with hx | rfl | hx
  · have : gWeight x = (Ioo 0 x).indicator (fun _ => x) := funext (gWeight_eq_pos hx)
    rw [this]
    exact (integrableOn_const (C := x) (by simp)).integrable_indicator measurableSet_Ioo
  · have : gWeight 0 = fun _ => (0 : ℝ) := funext gWeight_zero
    rw [this]; exact integrable_zero _ _ _
  · have : gWeight x = (Icc x 0).indicator (fun _ => -x) := funext (gWeight_eq_neg hx)
    rw [this]
    exact (integrableOn_const (C := -x) (by simp)).integrable_indicator measurableSet_Icc

lemma integral_gWeight (x : ℝ) : ∫ t, gWeight x t = x ^ 2 := by
  rcases lt_trichotomy 0 x with hx | rfl | hx
  · simp_rw [gWeight_eq_pos hx]
    rw [integral_indicator_const _ measurableSet_Ioo]
    simp [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal hx.le, sq]
  · simp [gWeight_zero]
  · simp_rw [gWeight_eq_neg hx]
    rw [integral_indicator_const _ measurableSet_Icc]
    simp only [Measure.real, Real.volume_Icc, zero_sub, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (by linarith)]; ring

/-- `∫ g(x,t) P₀(dx) = κ(t)` for every `t` (uses `E X = 0`). -/
lemma integral_gWeight_eq_kappa (P₀ : Measure ℝ) [IsProbabilityMeasure P₀]
    (h1 : Integrable (fun x => x) P₀) (hmean : ∫ x, x ∂P₀ = 0) (t : ℝ) :
    ∫ x, gWeight x t ∂P₀ = kappa P₀ t := by
  unfold kappa
  rcases lt_or_ge 0 t with ht | ht
  · have : ∀ x, gWeight x t = (Ioi t).indicator (fun x => x) x := by
      intro x; unfold gWeight; simp only [indicator, mem_Ioi]
      have h2 : ¬ (x ≤ t ∧ t ≤ 0) := fun h => by linarith [h.2]
      by_cases h : t < x <;> simp [h, ht, h2]
    simp_rw [this]
    rw [integral_indicator measurableSet_Ioi]
  · have : ∀ x, gWeight x t = (Iic t).indicator (fun x => -x) x := by
      intro x; unfold gWeight; simp only [indicator, mem_Iic]
      have h1 : ¬ (0 < t ∧ t < x) := fun h => by linarith [h.1]
      by_cases h : x ≤ t <;> simp [h, ht, h1]
    simp_rw [this]
    rw [integral_indicator measurableSet_Iic]
    have hsplit := integral_add_compl (μ := P₀) (f := fun x => x) (s := Iic t) measurableSet_Iic h1
    rw [compl_Iic, hmean] at hsplit
    rw [integral_neg]; linarith

/-- Mean-value bound `|f x − f 0| ≤ L |x|` for bounded `deriv f`. -/
lemma abs_sub_le_of_deriv_bdd (f : ℝ → ℝ) (hf : Differentiable ℝ f) (L : ℝ)
    (hL : ∀ t, |deriv f t| ≤ L) (x : ℝ) : |f x - f 0| ≤ L * |x| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (C := L) (s := univ)
    (fun y _ => hf y) (fun y _ => by simpa [Real.norm_eq_abs] using hL y) convex_univ
    (mem_univ 0) (mem_univ x)
  simpa [Real.norm_eq_abs] using this

lemma integrable_mul_sub (P₀ : Measure ℝ) [IsProbabilityMeasure P₀] (h2 : MemLp id 2 P₀)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (L : ℝ) (hL : ∀ t, |deriv f t| ≤ L) :
    Integrable (fun x => x * (f x - f 0)) P₀ := by
  have hsq : Integrable (fun x => L * x ^ 2) P₀ := by
    simpa using h2.integrable_sq.const_mul L
  refine hsq.mono' ?_ (ae_of_all _ fun x => ?_)
  · exact (measurable_id.mul ((hf.continuous.measurable).sub measurable_const)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    calc |x| * |f x - f 0| ≤ |x| * (L * |x|) := by
          gcongr; exact abs_sub_le_of_deriv_bdd f hf L hL x
      _ = L * x ^ 2 := by rw [sq, ← abs_mul_abs_self x]; ring

lemma integrable_deriv_mul_gWeight_prod (P₀ : Measure ℝ) [IsProbabilityMeasure P₀]
    (h2 : MemLp id 2 P₀) (f : ℝ → ℝ) (hf : Differentiable ℝ f) (L : ℝ)
    (hL : ∀ t, |deriv f t| ≤ L) :
    Integrable (fun p : ℝ × ℝ => deriv f p.2 * gWeight p.1 p.2) (P₀.prod volume) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => deriv f p.2 * gWeight p.1 p.2) :=
    ((measurable_deriv f).comp measurable_snd).mul measurable_gWeight
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun x => ?_, ?_⟩
  · exact (integrable_gWeight x).bdd_mul (c := L) (measurable_deriv f).aestronglyMeasurable
      (ae_of_all _ fun t => by simpa [Real.norm_eq_abs] using hL t)
  · have hsq : Integrable (fun x => L * x ^ 2) P₀ := by
      simpa using h2.integrable_sq.const_mul L
    refine hsq.mono' (hmeas.aestronglyMeasurable.norm.integral_prod_right') (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
    calc ∫ t, ‖deriv f t * gWeight x t‖ ≤ ∫ t, L * gWeight x t := by
          refine integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _)
            ((integrable_gWeight x).const_mul L) (ae_of_all _ fun t => ?_)
          simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gWeight_nonneg x t)]
          exact mul_le_mul_of_nonneg_right (hL t) (gWeight_nonneg x t)
      _ = L * x ^ 2 := by rw [integral_const_mul, integral_gWeight]

/-- **Zero-bias identity, kernel form** (note §2 (B), "Zero-bias lemma", first equality):
for `X ~ P₀` with `E X = 0`, `E X² < ∞`, and `f` differentiable with bounded derivative,
`E[X f(X)] = ∫ f′(t) κ(t) dt`. -/
theorem integral_mul_eq_integral_deriv_mul_kappa (P₀ : Measure ℝ) [IsProbabilityMeasure P₀]
    (h2 : MemLp id 2 P₀) (hmean : ∫ x, x ∂P₀ = 0)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (L : ℝ) (hL : ∀ t, |deriv f t| ≤ L) :
    ∫ x, x * f x ∂P₀ = ∫ t, deriv f t * kappa P₀ t := by
  have h1 : Integrable (fun x => x) P₀ := by
    exact h2.integrable (by norm_num)
  have hF := integrable_deriv_mul_gWeight_prod P₀ h2 f hf L hL
  calc ∫ x, x * f x ∂P₀ = ∫ x, (x * (f x - f 0) + f 0 * x) ∂P₀ := by
        congr 1; ext x; ring
    _ = ∫ x, x * (f x - f 0) ∂P₀ := by
        rw [integral_add (integrable_mul_sub P₀ h2 f hf L hL) (h1.const_mul _),
          integral_const_mul, hmean, mul_zero, add_zero]
    _ = ∫ x, ∫ t, deriv f t * gWeight x t ∂volume ∂P₀ := by
        congr 1; ext x; exact mul_sub_eq_integral_gWeight f hf L hL x
    _ = ∫ p, deriv f p.2 * gWeight p.1 p.2 ∂(P₀.prod volume) := (integral_prod _ hF).symm
    _ = ∫ t, ∫ x, deriv f t * gWeight x t ∂P₀ := integral_prod_symm _ hF
    _ = ∫ t, deriv f t * kappa P₀ t := by
        congr 1; ext t
        rw [integral_const_mul, integral_gWeight_eq_kappa P₀ h1 hmean]

end ZeroBias

namespace ZeroBias

/-- `κ` is Borel measurable (as a parametric integral). -/
lemma measurable_kappa (P₀ : Measure ℝ) [IsProbabilityMeasure P₀] : Measurable (kappa P₀) := by
  have : kappa P₀ = fun t => ∫ x, {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => p.2) (t, x) ∂P₀ := by
    ext t; unfold kappa
    rw [← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [indicator, mem_Ioi]
  rw [this]
  exact (StronglyMeasurable.integral_prod_right'
    (measurable_snd.indicator (measurableSet_lt measurable_fst measurable_snd)).stronglyMeasurable).measurable

lemma kappa_nonneg (P₀ : Measure ℝ) [IsProbabilityMeasure P₀]
    (h1 : Integrable (fun x => x) P₀) (hmean : ∫ x, x ∂P₀ = 0) (t : ℝ) : 0 ≤ kappa P₀ t := by
  rw [← integral_gWeight_eq_kappa P₀ h1 hmean]
  exact integral_nonneg fun x => gWeight_nonneg x t

lemma integrable_kappa (P₀ : Measure ℝ) [IsProbabilityMeasure P₀] (h2 : MemLp id 2 P₀)
    (hmean : ∫ x, x ∂P₀ = 0) : Integrable (kappa P₀) volume := by
  have h1 : Integrable (fun x => x) P₀ := h2.integrable (by norm_num)
  have hF := integrable_deriv_mul_gWeight_prod P₀ h2 (fun x => x) differentiable_id 1
    (fun t => by simp)
  have := hF.integral_prod_right
  refine this.congr (ae_of_all _ fun t => ?_)
  simp only [deriv_id'', one_mul]
  exact integral_gWeight_eq_kappa P₀ h1 hmean t

/-- `∫ κ = σ²` (the `f(x) = x` case of the identity). -/
lemma integral_kappa (P₀ : Measure ℝ) [IsProbabilityMeasure P₀] (h2 : MemLp id 2 P₀)
    (hmean : ∫ x, x ∂P₀ = 0) : ∫ t, kappa P₀ t = ∫ x, x ^ 2 ∂P₀ := by
  have := integral_mul_eq_integral_deriv_mul_kappa P₀ h2 hmean (fun x => x) differentiable_id 1
    (fun t => by simp)
  simp only [deriv_id'', one_mul] at this
  rw [← this]; congr 1; ext x; ring

/-- The **zero-bias law** `P₀*` of the note: Lebesgue density `κ(t)/σ²`. -/
def zeroBias (P₀ : Measure ℝ) (σ2 : ℝ) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (kappa P₀ t / σ2))

lemma zeroBias_def (P₀ : Measure ℝ) (σ2 : ℝ) :
    zeroBias P₀ σ2 = volume.withDensity (fun t => ENNReal.ofReal (kappa P₀ t / σ2)) := rfl

/-- Integrals against `P₀*` are Lebesgue integrals against the density `κ/σ²`. -/
lemma integral_zeroBias (P₀ : Measure ℝ) [IsProbabilityMeasure P₀]
    (h1 : Integrable (fun x => x) P₀) (hmean : ∫ x, x ∂P₀ = 0) {σ2 : ℝ} (hσ : 0 < σ2)
    (g : ℝ → ℝ) : ∫ t, g t ∂(zeroBias P₀ σ2) = ∫ t, (kappa P₀ t / σ2) * g t := by
  rw [zeroBias_def, integral_withDensity_eq_integral_toReal_smul
    ((measurable_kappa P₀).div_const σ2).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1; ext t
  rw [ENNReal.toReal_ofReal (div_nonneg (kappa_nonneg P₀ h1 hmean t) hσ.le), smul_eq_mul]

/-- `P₀*` is a probability measure when `σ² = E X² ≠ 0`. -/
theorem isProbabilityMeasure_zeroBias (P₀ : Measure ℝ) [IsProbabilityMeasure P₀]
    (h2 : MemLp id 2 P₀) (hmean : ∫ x, x ∂P₀ = 0) {σ2 : ℝ} (hvar : ∫ x, x ^ 2 ∂P₀ = σ2)
    (hσ : σ2 ≠ 0) : IsProbabilityMeasure (zeroBias P₀ σ2) := by
  have h1 : Integrable (fun x => x) P₀ := h2.integrable (by norm_num)
  constructor
  rw [zeroBias_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((integrable_kappa P₀ h2 hmean).div_const σ2)
      (ae_of_all _ fun t => ?_)]
  · rw [integral_div, integral_kappa P₀ h2 hmean, hvar, div_self hσ, ENNReal.ofReal_one]
  · have hσpos : 0 < σ2 := by
      rcases lt_or_gt_of_ne hσ with h | h
      · exfalso; rw [← hvar] at h
        exact absurd h (not_lt.2 (integral_nonneg fun x => sq_nonneg x))
      · exact h
    exact div_nonneg (kappa_nonneg P₀ h1 hmean t) hσpos.le

/-- **Zero-bias identity** (note §1 (B) / §2 (B) "Zero-bias lemma", second equality):
`E[X f(X)] = σ² E[f′(X*)]`, `X* ~ P₀*`. -/
theorem integral_mul_eq_var_mul_integral_deriv_zeroBias (P₀ : Measure ℝ) [IsProbabilityMeasure P₀]
    (h2 : MemLp id 2 P₀) (hmean : ∫ x, x ∂P₀ = 0) {σ2 : ℝ} (hvar : ∫ x, x ^ 2 ∂P₀ = σ2)
    (hσ : σ2 ≠ 0) (f : ℝ → ℝ) (hf : Differentiable ℝ f) (L : ℝ) (hL : ∀ t, |deriv f t| ≤ L) :
    ∫ x, x * f x ∂P₀ = σ2 * ∫ t, deriv f t ∂(zeroBias P₀ σ2) := by
  have h1 : Integrable (fun x => x) P₀ := h2.integrable (by norm_num)
  have hσpos : 0 < σ2 := by
    rcases lt_or_gt_of_ne hσ with h | h
    · exfalso; rw [← hvar] at h
      exact absurd h (not_lt.2 (integral_nonneg fun x => sq_nonneg x))
    · exact h
  rw [integral_zeroBias P₀ h1 hmean hσpos, integral_mul_eq_integral_deriv_mul_kappa P₀ h2 hmean f hf L hL,
    ← integral_const_mul]
  congr 1; ext t; field_simp

end ZeroBias

namespace ZeroBias

section Gaussian

/-- For `P₀ = N(0, v)`: `κ(t) = v · p₀(t)` (note §2 (B), "if P₀ = N(0,σ²), κ = σ²p₀"). -/
lemma kappa_gaussianReal (v : ℝ≥0) (hv : v ≠ 0) (t : ℝ) :
    kappa (gaussianReal 0 v) t = v * gaussianPDFReal 0 v t := by
  have hvpos : (0:ℝ) < v := by positivity
  unfold kappa
  rw [gaussianReal_of_var_ne_zero 0 hv, restrict_withDensity measurableSet_Ioi,
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 v)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp_rw [toReal_gaussianPDF, smul_eq_mul]
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s => -(v:ℝ) * gaussianPDFReal 0 v s)
      (gaussianPDFReal 0 v s * s) s := by
    intro s
    simp only [gaussianPDFReal, sub_zero]
    have h1 : HasDerivAt (fun s : ℝ => -s ^ 2 / (2 * v)) (-(2 * s ^ 1 * 1) / (2 * v)) s :=
      ((hasDerivAt_id s).pow 2).neg.div_const _
    have h2 := ((h1.exp).const_mul (√(2 * Real.pi * v))⁻¹).const_mul (-(v:ℝ))
    convert h2 using 1
    field_simp
  have hint : IntegrableOn (fun s => gaussianPDFReal 0 v s * s) (Ioi t) volume := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable le_rfl
    rw [gaussianReal_of_var_ne_zero 0 hv, integrable_withDensity_iff (measurable_gaussianPDF 0 v)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)] at h
    refine (h.congr (ae_of_all _ fun s => ?_)).integrableOn
    simp [toReal_gaussianPDF, mul_comm]
  have htend : Tendsto (fun s => -(v:ℝ) * gaussianPDFReal 0 v s) atTop (𝓝 0) := by
    simp only [gaussianPDFReal, sub_zero]
    have h1 : Tendsto (fun s : ℝ => -s ^ 2 / (2 * v)) atTop atBot :=
      (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero)).atBot_div_const (by positivity)
    have h2 := ((Real.tendsto_exp_atBot.comp h1).const_mul (√(2 * Real.pi * v))⁻¹).const_mul (-(v:ℝ))
    simpa using h2
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun s _ => hderiv s) hint htend]
  ring

/-- The Gaussian is a fixed point of the zero-bias transform: `N(0,v)* = N(0,v)`
(note §1 (B): "P₀* = P₀ iff P₀ is Gaussian", the 'if' direction). -/
theorem zeroBias_gaussianReal (v : ℝ≥0) (hv : v ≠ 0) :
    zeroBias (gaussianReal 0 v) v = gaussianReal 0 v := by
  have hvpos : (0:ℝ) < v := by positivity
  have hk : ∀ t, ENNReal.ofReal (kappa (gaussianReal 0 v) t / v) = gaussianPDF 0 v t := by
    intro t
    rw [kappa_gaussianReal v hv t, gaussianPDF]
    congr 1; field_simp
  rw [zeroBias_def]
  simp_rw [hk]
  exact (gaussianReal_of_var_ne_zero 0 hv).symm

/-- **Gaussian Stein identity** (note §1 (B), jointly-Gaussian clause in 1-D; Stein 1981 Lemma 1):
for `X ~ N(0, v)` and `f` differentiable with bounded derivative, `E[X f(X)] = v E[f′(X)]`. -/
theorem stein_gaussianReal (v : ℝ≥0) (f : ℝ → ℝ) (hf : Differentiable ℝ f) (L : ℝ)
    (hL : ∀ t, |deriv f t| ≤ L) :
    ∫ x, x * f x ∂(gaussianReal 0 v) = v * ∫ x, deriv f x ∂(gaussianReal 0 v) := by
  by_cases hv : v = 0
  · subst hv; simp [gaussianReal_zero_var]
  · have hvar : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
      rw [← variance_of_integral_eq_zero (X := fun x => x) measurable_id.aemeasurable
        (by simp [integral_id_gaussianReal])]
      exact variance_fun_id_gaussianReal
    have := integral_mul_eq_var_mul_integral_deriv_zeroBias (gaussianReal 0 v)
      (memLp_id_gaussianReal 2) (by simp [integral_id_gaussianReal]) hvar
      (by exact_mod_cast hv) f hf L hL
    rwa [zeroBias_gaussianReal v hv] at this

end Gaussian

end ZeroBias

namespace ZeroBias

/-- **Conditional zero-bias identity on a product.** For `X ~ P₀` (mean 0, variance `σ²`)
independent of `Y ~ ν`, and `F(t, y)` differentiable in `t` with partial derivative `F'`
bounded uniformly in `(t, y)`:  `E[X F(X, Y)] = σ² E[F'(X*, Y)]` with `X* ~ P₀*` independent of `Y`.
This is the note's "fix η and the other coordinates of ε, apply the lemma in ε^α, integrate".
`hint` is the existence of the left-hand side (see FIDELITY: it is NOT automatic for arbitrary `ν`). -/
theorem integral_fst_mul_prod_eq_var_mul_integral_zeroBias_prod
    (P₀ : Measure ℝ) [IsProbabilityMeasure P₀] (h2 : MemLp id 2 P₀) (hmean : ∫ x, x ∂P₀ = 0)
    {σ2 : ℝ} (hvar : ∫ x, x ^ 2 ∂P₀ = σ2) (hσ : σ2 ≠ 0)
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    (F F' : ℝ × Y → ℝ) (hF' : ∀ y t, HasDerivAt (fun s => F (s, y)) (F' (t, y)) t)
    (hF'meas : Measurable F') (L : ℝ) (hL : ∀ p, |F' p| ≤ L)
    (hint : Integrable (fun p => p.1 * F p) (P₀.prod ν)) :
    ∫ p, p.1 * F p ∂(P₀.prod ν) = σ2 * ∫ p, F' p ∂((zeroBias P₀ σ2).prod ν) := by
  haveI := isProbabilityMeasure_zeroBias P₀ h2 hmean hvar hσ
  have hF'int : Integrable F' ((zeroBias P₀ σ2).prod ν) :=
    (integrable_const L).mono' hF'meas.aestronglyMeasurable
      (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hL p)
  rw [integral_prod_symm _ hint, integral_prod_symm _ hF'int, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  have hdiff : Differentiable ℝ (fun s => F (s, y)) := fun t => (hF' y t).differentiableAt
  have hderiv : ∀ t, deriv (fun s => F (s, y)) t = F' (t, y) := fun t => (hF' y t).deriv
  have := integral_mul_eq_var_mul_integral_deriv_zeroBias P₀ h2 hmean hvar hσ
    (fun s => F (s, y)) hdiff L (fun t => by rw [hderiv]; exact hL _)
  simp only [hderiv] at this
  exact this

end ZeroBias

namespace ZeroBias

section DirectDesign

/-- Dice space `D = (ℝᵈ)ⁿ` of the note: `x j β` is reader `j`'s coordinate `β`. -/
abbrev Dice (n d : ℕ) := Fin n → Fin d → ℝ

variable {n d m : ℕ}

/-- The diagonal `ι(θ) = (θ, …, θ) ∈ D`. -/
def iota (θ : Fin d → ℝ) : Dice n d := fun _ => θ

/-- `δ_j = r_j ε + η_j`: shared die `ε` with loadings `r`, private noise `η`. -/
def delta (r : Fin n → ℝ) (ε : Fin d → ℝ) (η : Dice n d) : Dice n d :=
  fun j β => r j * ε β + η j β

/-- The unit vector `e_{jα}` of dice space (reader `j`, coordinate `α`). -/
def unitVec (j : Fin n) (α : Fin d) : Dice n d := Pi.single j (Pi.single α 1)

/-- `∂_{x_j^α} R(x)`, the partial derivative of a reward in reader `j`'s coordinate `α`. -/
def partialD (R : Dice n d → ℝ) (j : Fin n) (α : Fin d) (x : Dice n d) : ℝ :=
  fderiv ℝ R x (unitVec j α)

/-- Law of the shared die `ε ∈ ℝᵈ`: independent coordinates of common law `P₀`. -/
abbrev diceLaw (P₀ : Measure ℝ) (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi fun _ => P₀

/-- Law of `ε^{*α}`: `ε` with coordinate `α` replaced by an independent draw from `P₀*`. -/
def tiltedLaw (P₀ : Measure ℝ) (σ2 : ℝ) (α : Fin d) : Measure (Fin d → ℝ) :=
  Measure.pi fun i => if i = α then zeroBias P₀ σ2 else P₀

/-- The direction `∂/∂ε^α` of `ι(θ) + δ`: `Σ_j r_j e_{jα}`. -/
def dirVec (r : Fin n → ℝ) (α : Fin d) : Dice n d := fun j β => r j * if β = α then 1 else 0

lemma dirVec_eq_sum (r : Fin n → ℝ) (α : Fin d) : dirVec r α = ∑ j, r j • unitVec j α := by
  ext j β
  simp only [dirVec, unitVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · by_cases h : β = α <;> simp [Pi.single_apply, h]
  · intro j' _ hj'; simp [hj'.symm]
  · intro h; exact absurd (Finset.mem_univ j) h

lemma continuous_iota_add_delta (θ : Fin d → ℝ) (r : Fin n → ℝ) :
    Continuous fun p : (Fin d → ℝ) × Dice n d => iota θ + delta r p.1 p.2 := by
  unfold iota delta; fun_prop

lemma abs_partial_le (R : Dice n d → ℝ) (M : ℝ) (hM : ∀ x, ‖fderiv ℝ R x‖ ≤ M) (x v : Dice n d) :
    |fderiv ℝ R x v| ≤ M * ‖v‖ := by
  rw [← Real.norm_eq_abs]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))

/-- Splitting coordinate `α` off the die: `(ℝ^{d+1}) × D ≃ ℝ × (ℝ^d × D)`. -/
def splitEquiv (n d : ℕ) (α : Fin (d+1)) :
    (Fin (d+1) → ℝ) × Dice n (d+1) ≃ᵐ ℝ × ((Fin d → ℝ) × Dice n (d+1)) :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) α).prodCongr (MeasurableEquiv.refl _)).trans
    MeasurableEquiv.prodAssoc

lemma splitEquiv_symm_apply (α : Fin (d+1)) (q : ℝ × ((Fin d → ℝ) × Dice n (d+1))) :
    (splitEquiv n d α).symm q = (Fin.insertNth α q.1 q.2.1, q.2.2) := rfl

lemma hasDerivAt_insertNth (α : Fin (d+1)) (ρ : Fin d → ℝ) (β : Fin (d+1)) (t : ℝ) :
    HasDerivAt (fun t => (Fin.insertNth α t ρ : Fin (d+1) → ℝ) β) (if β = α then 1 else 0) t := by
  rcases Fin.eq_self_or_eq_succAbove α β with h | ⟨j', rfl⟩
  · subst h; simp only [Fin.insertNth_apply_same, if_true]; exact hasDerivAt_id t
  · simp only [Fin.insertNth_apply_succAbove, Fin.succAbove_ne, if_false]
    exact hasDerivAt_const t _

lemma hasDerivAt_path (θ : Fin (d+1) → ℝ) (r : Fin n → ℝ) (α : Fin (d+1)) (ρ : Fin d → ℝ)
    (η : Dice n (d+1)) (t : ℝ) :
    HasDerivAt (fun t => iota θ + delta r (Fin.insertNth α t ρ) η) (dirVec r α) t := by
  rw [hasDerivAt_pi]; intro j
  rw [hasDerivAt_pi]; intro β
  simp only [iota, delta, dirVec, Pi.add_apply]
  exact (((hasDerivAt_insertNth α ρ β t).const_mul (r j)).add_const (η j β)).const_add (θ β)

instance (P₀ : Measure ℝ) [IsProbabilityMeasure P₀] : IsProbabilityMeasure (diceLaw P₀ d) := by
  unfold diceLaw; infer_instance

lemma isProbabilityMeasure_tiltedLaw (P₀ : Measure ℝ) [IsProbabilityMeasure P₀]
    (h2 : MemLp id 2 P₀) (hmean : ∫ x, x ∂P₀ = 0) {σ2 : ℝ} (hvar : ∫ x, x ^ 2 ∂P₀ = σ2)
    (hσ : σ2 ≠ 0) (α : Fin d) : IsProbabilityMeasure (tiltedLaw P₀ σ2 α) := by
  haveI := isProbabilityMeasure_zeroBias P₀ h2 hmean hvar hσ
  haveI : ∀ i : Fin d, IsProbabilityMeasure (if i = α then zeroBias P₀ σ2 else P₀) :=
    fun i => by split_ifs <;> infer_instance
  unfold tiltedLaw; infer_instance

/-- Theorem (B) for `d + 1` die coordinates (the general statement is `direct_design_update`). -/
theorem direct_design_update_succ (P₀ : Measure ℝ) [IsProbabilityMeasure P₀]
    (h2 : MemLp id 2 P₀) (hmean : ∫ x, x ∂P₀ = 0) {σ2 : ℝ} (hvar : ∫ x, x ^ 2 ∂P₀ = σ2)
    (hσ : σ2 ≠ 0) (Q : Measure (Dice n (d+1))) [IsProbabilityMeasure Q]
    (r : Fin n → ℝ) (c : Fin m → ℝ) (R : Fin m → Dice n (d+1) → ℝ)
    (hR : ∀ k, ContDiff ℝ 1 (R k)) (M : ℝ) (hM : ∀ k x, ‖fderiv ℝ (R k) x‖ ≤ M)
    (θ : Fin (d+1) → ℝ) (α : Fin (d+1))
    (hint : Integrable (fun p : (Fin (d+1) → ℝ) × Dice n (d+1) =>
      p.1 α * ∑ k, c k * R k (iota θ + delta r p.1 p.2)) ((diceLaw P₀ (d+1)).prod Q)) :
    ∫ p, p.1 α * ∑ k, c k * R k (iota θ + delta r p.1 p.2) ∂((diceLaw P₀ (d+1)).prod Q)
      = σ2 * ∑ j, ∑ k, r j * c k *
          ∫ p, partialD (R k) j α (iota θ + delta r p.1 p.2) ∂((tiltedLaw P₀ σ2 α).prod Q) := by
  haveI hzb := isProbabilityMeasure_zeroBias P₀ h2 hmean hvar hσ
  haveI := isProbabilityMeasure_tiltedLaw P₀ h2 hmean hvar hσ α
  set e := splitEquiv n d α with he
  set ν : Measure ((Fin d → ℝ) × Dice n (d+1)) := (diceLaw P₀ d).prod Q with hν
  -- the point `ι(θ) + δ` as a function of the split coordinates
  set X : ℝ × ((Fin d → ℝ) × Dice n (d+1)) → Dice n (d+1) :=
    fun q => iota θ + delta r (e.symm q).1 (e.symm q).2 with hX
  have hXeq : ∀ q, X q = iota θ + delta r (Fin.insertNth α q.1 q.2.1) q.2.2 := fun q => rfl
  have hXmeas : Measurable X :=
    (continuous_iota_add_delta θ r).measurable.comp e.symm.measurable
  set F : ℝ × ((Fin d → ℝ) × Dice n (d+1)) → ℝ := fun q => ∑ k, c k * R k (X q) with hF
  set F' : ℝ × ((Fin d → ℝ) × Dice n (d+1)) → ℝ :=
    fun q => ∑ k, c k * fderiv ℝ (R k) (X q) (dirVec r α) with hF'
  -- measure preservation
  have hpres : MeasurePreserving e ((diceLaw P₀ (d+1)).prod Q) (P₀.prod ν) :=
    ((measurePreserving_piFinSuccAbove (fun _ : Fin (d+1) => P₀) α).prod
      (MeasurePreserving.id Q)).trans (measurePreserving_prodAssoc _ _ _)
  have hpresT : MeasurePreserving e ((tiltedLaw P₀ σ2 α).prod Q) ((zeroBias P₀ σ2).prod ν) := by
    haveI : ∀ i : Fin (d+1), IsProbabilityMeasure (if i = α then zeroBias P₀ σ2 else P₀) :=
      fun i => by split_ifs <;> infer_instance
    have h1 := measurePreserving_piFinSuccAbove (fun i : Fin (d+1) => if i = α then zeroBias P₀ σ2 else P₀) α
    have hμ : (fun j : Fin d => if α.succAbove j = α then zeroBias P₀ σ2 else P₀) = fun _ => P₀ :=
      funext fun j => if_neg (Fin.succAbove_ne α j)
    simp only [if_true, hμ] at h1
    exact (h1.prod (MeasurePreserving.id Q)).trans (measurePreserving_prodAssoc _ _ _)
  -- derivative in the split-off coordinate
  have hderiv : ∀ y t, HasDerivAt (fun s => F (s, y)) (F' (t, y)) t := by
    intro y t
    simp only [hF, hF', hXeq]
    refine HasDerivAt.fun_sum fun k _ => ?_
    exact (((hR k).differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_path θ r α y.1 y.2 t)).const_mul (c k)
  have hF'meas : Measurable F' := by
    refine Finset.measurable_sum _ fun k _ => ?_
    exact ((measurable_fderiv_apply_const ℝ (R k) (dirVec r α)).comp hXmeas).const_mul _
  have hL : ∀ q, |F' q| ≤ ∑ k, |c k| * (M * ‖dirVec r α‖) := by
    intro q
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_partial_le (R k) M (hM k) _ _) (abs_nonneg _)
  -- transport the left-hand side
  have hGe : (fun q => (fun p : (Fin (d+1) → ℝ) × Dice n (d+1) =>
      p.1 α * ∑ k, c k * R k (iota θ + delta r p.1 p.2)) (e.symm q)) = fun q => q.1 * F q := by
    funext q
    have h1 : (e.symm q).1 = Fin.insertNth α q.1 q.2.1 := rfl
    have h2 : (e.symm q).2 = q.2.2 := rfl
    simp only [hF, hXeq, h1, h2, Fin.insertNth_apply_same]
  have hint' : Integrable (fun q => q.1 * F q) (P₀.prod ν) := by
    rw [← hGe]
    exact ((hpres.symm e).integrable_comp_emb e.symm.measurableEmbedding).2 hint
  have hLHS : ∫ p, p.1 α * ∑ k, c k * R k (iota θ + delta r p.1 p.2) ∂((diceLaw P₀ (d+1)).prod Q)
      = ∫ q, q.1 * F q ∂(P₀.prod ν) := by
    rw [← (hpres.symm e).integral_comp', hGe]
  -- the identity
  rw [hLHS, integral_fst_mul_prod_eq_var_mul_integral_zeroBias_prod P₀ h2 hmean hvar hσ ν F F'
    hderiv hF'meas _ hL hint']
  congr 1
  -- rewrite F' as the double sum of partials and transport back
  have hpint : ∀ (j : Fin n) (k : Fin m),
      Integrable (fun q => r j * c k * partialD (R k) j α (X q)) ((zeroBias P₀ σ2).prod ν) := by
    intro j k
    have hb : Integrable (fun q => partialD (R k) j α (X q)) ((zeroBias P₀ σ2).prod ν) := by
      refine (integrable_const (μ := (zeroBias P₀ σ2).prod ν) (M * ‖unitVec j α‖)).mono'
        (((measurable_fderiv_apply_const ℝ (R k) (unitVec j α)).comp hXmeas).aestronglyMeasurable)
        (ae_of_all _ fun q => ?_)
      simpa [Real.norm_eq_abs, partialD] using abs_partial_le (R k) M (hM k) (X q) (unitVec j α)
    exact hb.const_mul _
  have hFsum : F' = fun q => ∑ j, ∑ k, r j * c k * partialD (R k) j α (X q) := by
    funext q
    simp only [hF', partialD, dirVec_eq_sum, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hFsum, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hpint j k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => hpint j k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul,
    ← (hpresT.symm e).integral_comp' (fun p => partialD (R k) j α (iota θ + delta r p.1 p.2))]

/-- **Theorem (B), identification (note §1 (B) display; beyond_first_order.md Theorem C).**
Direct design: shared die `ε ∈ ℝᵈ` with i.i.d. mean-zero coordinates of law `P₀` and variance `σ²`,
private noise `η ~ Q` independent of `ε`, `δ_j = r_j ε + η_j`, `ĝ = ε Σ_k c_k R_k(ι(θ)+δ)`,
`R_k ∈ C¹` with `‖∇R_k‖ ≤ M`. Then for every coordinate `α`
`E[ĝ]^α = σ² Σ_{j,k} r_j c_k E[∂_{x_j^α} R_k(ι(θ) + δ^{*α})]`, where `δ^{*α} = r ε^{*α} + η` and
`ε^{*α} ~ tiltedLaw`. The hypothesis `hint` says `ĝ^α ∈ L¹`, i.e. that the left-hand side exists. -/
theorem direct_design_update (P₀ : Measure ℝ) [IsProbabilityMeasure P₀]
    (h2 : MemLp id 2 P₀) (hmean : ∫ x, x ∂P₀ = 0) {σ2 : ℝ} (hvar : ∫ x, x ^ 2 ∂P₀ = σ2)
    (hσ : σ2 ≠ 0) (Q : Measure (Dice n d)) [IsProbabilityMeasure Q]
    (r : Fin n → ℝ) (c : Fin m → ℝ) (R : Fin m → Dice n d → ℝ)
    (hR : ∀ k, ContDiff ℝ 1 (R k)) (M : ℝ) (hM : ∀ k x, ‖fderiv ℝ (R k) x‖ ≤ M)
    (θ : Fin d → ℝ) (α : Fin d)
    (hint : Integrable (fun p : (Fin d → ℝ) × Dice n d =>
      p.1 α * ∑ k, c k * R k (iota θ + delta r p.1 p.2)) ((diceLaw P₀ d).prod Q)) :
    ∫ p, p.1 α * ∑ k, c k * R k (iota θ + delta r p.1 p.2) ∂((diceLaw P₀ d).prod Q)
      = σ2 * ∑ j, ∑ k, r j * c k *
          ∫ p, partialD (R k) j α (iota θ + delta r p.1 p.2) ∂((tiltedLaw P₀ σ2 α).prod Q) := by
  cases d with
  | zero => exact α.elim0
  | succ d => exact direct_design_update_succ P₀ h2 hmean hvar hσ Q r c R hR M hM θ α hint

end DirectDesign

end ZeroBias
