import Mathlib

/-!
# Gene-culture two-layer pitchfork

Genetic layer: a biased pitchfork `r x - x ^ 3 + h = 0` with `r < 0` (past the symmetric point the
unbiased system would sit at `x = 0`); `h` is the genetic bias, `x` the cultural state.
Cultural layer: a conversion map `p = q + c (1 - q)` from a baseline frequency `q` to a frequency `p`
with conversion rate `c`.

PROVED:
* `bias_picks_branch_pos`: for `r < 0`, `h > 0` and `r x - x ^ 3 + h = 0`, we have `x > 0`.
* `bias_picks_branch_neg`: for `r < 0`, `h < 0` and a root `x`, we have `x < 0`.
* `bias_zero_root_zero`: for `r < 0`, `h = 0` and a root `x`, we have `x = 0`.
* `sign_root_eq_sign_bias`: for `r < 0` and a root `x`, `SignType.sign x = SignType.sign h`.
* `bias_gain_le`, `bias_gain_ge`: for `r < 0`, `h > 0` and a root `x`,
  `h / ((h / r) ^ 2 - r) ≤ x ≤ h / (-r)`.
* `bias_gain_le_neg`, `bias_gain_ge_neg`: for `r < 0`, `h < 0` and a root `x`,
  `h / (-r) ≤ x ≤ h / ((h / r) ^ 2 - r)` (the mirror image under `x ↦ -x`, `h ↦ -h`).
* `cubic_strictAnti`: for `r < 0` the map `x ↦ r x - x ^ 3 + h` is strictly decreasing.
* `cubic_existsUnique_root`: for `r < 0` the cubic `r x - x ^ 3 + h` has exactly one real root.
* `conversion_iff`: for `q < 1` (in particular `q ∈ [0, 1)`), `p = q + c (1 - q) ↔ c = (p - q) / (1 - q)`.
* `conversion_zero_iff`: for `q < 1` and `p = q + c (1 - q)`, `c = 0 ↔ p = q`.
* `conversion_mem_Icc`: for `q < 1` (in particular `q ∈ [0, 1)`), `c ∈ [0, 1]`, the converted frequency `p = q + c (1 - q)`
  lies in `[q, 1]`.
* `selection_destroys`: (restated from `LawfulCannotChoose`) if a fraction `q ≥ 0` is of the favoured
  type, its survival is `sL ≤ 1`, the total surviving fraction is `S > 0`, and the post-selection
  fraction is `p = q sL / S > 0`, then `S ≤ q / p`.
* `selection_destroys_tight`: the bound is attained: for `q > 0`, `p > 0`, `sL = 1` and `S = q / p`,
  one has `p = q sL / S`.
* `two_layer`: for `r < 0`, `h > 0` and a root `x`, both `0 < x ≤ h / (-r)` and, for any selection
  data as in `selection_destroys`, `S ≤ q / p`; the selection bound holds for every `h`.

INTERPRETED (not formalized):
* The genetic bias `h` only picks which cultural branch is taken (the sign of `x`) and sets a
  small displacement of size about `h / (-r)`; it is a cheap amplifier.
* The cost of reaching a given purity `p` by selection, `S ≤ q / p`, involves only `q` and `p` and
  not `h`: the bias picks the branch but does not pay for purification. In the Lean statement this
  is the syntactic fact that `selection_destroys` has no `h`, which `two_layer` records by
  quantifying over `h`.
-/

namespace GeneCulturePitchfork

theorem bias_picks_branch_pos (r h x : ℝ) (hr : r < 0) (hh : 0 < h)
    (he : r * x - x ^ 3 + h = 0) : 0 < x := by
  by_contra hx
  push Not at hx
  nlinarith [sq_nonneg x, mul_nonneg (neg_nonneg.mpr hx) (sq_nonneg x)]

theorem bias_picks_branch_neg (r h x : ℝ) (hr : r < 0) (hh : h < 0)
    (he : r * x - x ^ 3 + h = 0) : x < 0 := by
  have := bias_picks_branch_pos r (-h) (-x) hr (by linarith) (by nlinarith)
  linarith

theorem bias_zero_root_zero (r h x : ℝ) (hr : r < 0) (hh : h = 0)
    (he : r * x - x ^ 3 + h = 0) : x = 0 := by
  subst hh
  have h1 : x * (r - x ^ 2) = 0 := by linarith
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact h2
  · nlinarith [sq_nonneg x]

theorem sign_root_eq_sign_bias (r h x : ℝ) (hr : r < 0) (he : r * x - x ^ 3 + h = 0) :
    SignType.sign x = SignType.sign h := by
  rcases lt_trichotomy h 0 with hh | hh | hh
  · rw [sign_neg hh, sign_neg (bias_picks_branch_neg r h x hr hh he)]
  · rw [hh, bias_zero_root_zero r h x hr hh he]
  · rw [sign_pos hh, sign_pos (bias_picks_branch_pos r h x hr hh he)]

theorem bias_gain_le (r h x : ℝ) (hr : r < 0) (hh : 0 < h) (he : r * x - x ^ 3 + h = 0) :
    x ≤ h / (-r) := by
  have hx := bias_picks_branch_pos r h x hr hh he
  rw [le_div_iff₀ (by linarith)]
  nlinarith [pow_pos hx 3]

theorem bias_gain_ge (r h x : ℝ) (hr : r < 0) (hh : 0 < h) (he : r * x - x ^ 3 + h = 0) :
    h / ((h / r) ^ 2 - r) ≤ x := by
  have hx := bias_picks_branch_pos r h x hr hh he
  have hup := bias_gain_le r h x hr hh he
  have hx2 : x ^ 2 ≤ (h / r) ^ 2 := by
    have : h / (-r) = -(h / r) := by rw [div_neg]
    rw [this] at hup
    have h0 : 0 ≤ x := hx.le
    nlinarith [sq_nonneg (h / r)]
  have hden : 0 < (h / r) ^ 2 - r := by nlinarith [sq_nonneg (h / r)]
  rw [div_le_iff₀ hden]
  nlinarith [mul_le_mul_of_nonneg_left hx2 hx.le]

theorem bias_gain_le_neg (r h x : ℝ) (hr : r < 0) (hh : h < 0) (he : r * x - x ^ 3 + h = 0) :
    x ≤ h / ((h / r) ^ 2 - r) := by
  have := bias_gain_ge r (-h) (-x) hr (by linarith) (by nlinarith)
  have e : (-h) / (((-h) / r) ^ 2 - r) = -(h / ((h / r) ^ 2 - r)) := by
    have hs : ((-h) / r) ^ 2 = (h / r) ^ 2 := by ring
    rw [hs, neg_div]
  rw [e] at this
  linarith

theorem bias_gain_ge_neg (r h x : ℝ) (hr : r < 0) (hh : h < 0) (he : r * x - x ^ 3 + h = 0) :
    h / (-r) ≤ x := by
  have := bias_gain_le r (-h) (-x) hr (by linarith) (by nlinarith)
  rw [neg_div] at this
  linarith

theorem cubic_strictAnti (r h : ℝ) (hr : r < 0) :
    StrictAnti (fun x : ℝ => r * x - x ^ 3 + h) := by
  intro a b hab
  simp only
  have hq : 0 ≤ a ^ 2 + a * b + b ^ 2 := by nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]
  have hd : 0 < b - a := by linarith
  have key : (r * a - a ^ 3 + h) - (r * b - b ^ 3 + h)
      = (b - a) * (-r + (a ^ 2 + a * b + b ^ 2)) := by ring
  have : 0 < (b - a) * (-r + (a ^ 2 + a * b + b ^ 2)) := mul_pos hd (by linarith)
  linarith

theorem cubic_existsUnique_root (r h : ℝ) (hr : r < 0) :
    ∃! x : ℝ, r * x - x ^ 3 + h = 0 := by
  set f : ℝ → ℝ := fun x => r * x - x ^ 3 + h with hf
  set M : ℝ := |h| + 1 with hM
  have hM1 : 1 ≤ M := by have := abs_nonneg h; linarith
  have hM3 : M ≤ M ^ 3 := by nlinarith [mul_le_mul hM1 hM1 zero_le_one (by linarith)]
  have hb : f M ≤ 0 := by
    simp only [hf]
    nlinarith [le_abs_self h, neg_abs_le h]
  have ha : 0 ≤ f (-M) := by
    simp only [hf]
    nlinarith [le_abs_self h, neg_abs_le h]
  have hcont : ContinuousOn f (Set.Icc (-M) M) := by
    apply Continuous.continuousOn
    simp only [hf]
    fun_prop
  have hab : -M ≤ M := by linarith
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc' hab hcont ⟨hb, ha⟩
  refine ⟨x, hx, fun y hy => ?_⟩
  exact (cubic_strictAnti r h hr).injective (hy.trans hx.symm)

theorem conversion_iff (p q c : ℝ) (hq : q < 1) :
    p = q + c * (1 - q) ↔ c = (p - q) / (1 - q) := by
  have hne : (1 - q) ≠ 0 := by linarith
  constructor
  · intro h
    rw [eq_div_iff hne]
    linarith
  · intro h
    rw [h, div_mul_cancel₀ _ hne]
    ring

theorem conversion_zero_iff (p q c : ℝ) (hq : q < 1) (hp : p = q + c * (1 - q)) :
    c = 0 ↔ p = q := by
  have hpos : 0 < 1 - q := by linarith
  constructor
  · intro h
    rw [hp, h]
    ring
  · intro h
    have : c * (1 - q) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact h1
    · linarith

theorem conversion_mem_Icc (q c : ℝ) (hq1 : q < 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    q + c * (1 - q) ∈ Set.Icc q 1 := by
  have hpos : 0 ≤ 1 - q := by linarith
  constructor
  · nlinarith [mul_nonneg hc0 hpos]
  · nlinarith [mul_le_mul_of_nonneg_right hc1 hpos]

theorem selection_destroys (q sL S p : ℝ) (hq : 0 ≤ q) (hs : sL ≤ 1) (hS : 0 < S) (hp : 0 < p)
    (hpost : p = q * sL / S) : S ≤ q / p := by
  rw [le_div_iff₀ hp, hpost, mul_div_cancel₀ _ hS.ne']
  exact mul_le_of_le_one_right hq hs

theorem selection_destroys_tight (q p : ℝ) (hq : 0 < q) (hp : 0 < p) :
    p = q * 1 / (q / p) := by
  field_simp

theorem two_layer (r h x : ℝ) (hr : r < 0) (hh : 0 < h) (he : r * x - x ^ 3 + h = 0) :
    (0 < x ∧ x ≤ h / (-r)) ∧
      ∀ q sL S p : ℝ, 0 ≤ q → sL ≤ 1 → 0 < S → 0 < p → p = q * sL / S → S ≤ q / p :=
  ⟨⟨bias_picks_branch_pos r h x hr hh he, bias_gain_le r h x hr hh he⟩,
    fun q sL S p hq hs hS hp hpost => selection_destroys q sL S p hq hs hS hp hpost⟩

end GeneCulturePitchfork
