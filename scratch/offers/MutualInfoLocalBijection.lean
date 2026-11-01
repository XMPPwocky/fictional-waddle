import Mathlib

/-!
# Local relabelling and local processing of mutual information

Setting: finite types `X`, `Y`, a function `p : X × Y → ℝ` (a joint pmf when
`0 ≤ p` and `∑ p = 1`), marginals `margX p x = ∑ y, p (x, y)` and
`margY p y = ∑ x, p (x, y)`, and

  `mutualInfo p = ∑ z, p z * log (p z / (margX p z.1 * margY p z.2))`.

Convention: a term with `p z = 0` is `0 * log (...) = 0`, which holds
definitionally (`zero_mul`). When `p ≥ 0` and `p z > 0`, both marginals at
`z` are positive (`p z ≤ margX p z.1`, `p z ≤ margY p z.2`), so Lean's
`log 0 = 0` and `x / 0 = 0` conventions are never used on a nonzero term;
the definition agrees with the textbook one for every pmf.

The pushforward along `f : X → X'`, `g : Y → Y'` is
`push f g p (x', y') = ∑ {p (x, y) | f x = x', g y = y'}`.

PROVED
* `mutualInfo_eq_double_sum`: the definition equals the double sum
  `∑ x, ∑ y, p (x, y) * log (p (x, y) / (pX x * pY y))`.
* `log_sum_inequality`: for `a, b ≥ 0` on a finset with `b i = 0 → a i = 0`,
  `(∑ a) * log (∑ a / ∑ b) ≤ ∑ a i * log (a i / b i)`.
* `mutualInfo_nonneg` (statement (1)): for a pmf `p`, `0 ≤ mutualInfo p`.
* `mutualInfo_relabel` (statement (2)): for bijections `f : X ≃ X'`,
  `g : Y ≃ Y'` and `p' (x', y') = p (f.symm x', g.symm y')`,
  `mutualInfo p' = mutualInfo p`. No hypothesis on `p` is needed.
* `relabel_eq_push`: for bijections, `p'` coincides with the pushforward
  `push f g p`, so (2) is the bijective case of (3).
* `push_nonneg`, `push_sum`: the pushforward of a pmf is a pmf.
* `mutualInfo_push_le` (statement (3), data processing): for arbitrary
  `f : X → X'`, `g : Y → Y'` with `X'`, `Y'` finite and `p ≥ 0`,
  `mutualInfo (push f g p) ≤ mutualInfo p`. Proved fibrewise from the
  log-sum inequality.
* `mutualInfo_push_eq_of_injective` (equality clause of (3)): if `f` and `g`
  are injective then `mutualInfo (push f g p) = mutualInfo p`, for every `p`.
-/

set_option linter.unusedSectionVars false

namespace MutualInfoLocalBijection

open Finset Real

variable {X Y X' Y' : Type*} [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']

/-- Marginal on the first factor. -/
def margX (p : X × Y → ℝ) (x : X) : ℝ := ∑ y, p (x, y)

/-- Marginal on the second factor. -/
def margY (p : X × Y → ℝ) (y : Y) : ℝ := ∑ x, p (x, y)

/-- Mutual information of a joint weight function. -/
noncomputable def mutualInfo (p : X × Y → ℝ) : ℝ :=
  ∑ z : X × Y, p z * Real.log (p z / (margX p z.1 * margY p z.2))

theorem mutualInfo_eq_double_sum (p : X × Y → ℝ) :
    mutualInfo p =
      ∑ x, ∑ y, p (x, y) * Real.log (p (x, y) / (margX p x * margY p y)) :=
  Fintype.sum_prod_type _

/-- Relabelling by a pair of bijections. -/
def relabel (f : X ≃ X') (g : Y ≃ Y') (p : X × Y → ℝ) : X' × Y' → ℝ :=
  fun z' => p (f.symm z'.1, g.symm z'.2)

section push

variable [DecidableEq X'] [DecidableEq Y']

/-- The fibre of `z'` under the product map `f × g`. -/
def fiber (f : X → X') (g : Y → Y') (z' : X' × Y') : Finset (X × Y) :=
  univ.filter (fun z : X × Y => (f z.1, g z.2) = z')

/-- Pushforward of a weight function along the product map `f × g`. -/
def push (f : X → X') (g : Y → Y') (p : X × Y → ℝ) : X' × Y' → ℝ :=
  fun z' => ∑ z ∈ fiber f g z', p z

end push

lemma mul_log_le_aux {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * (log c - log (a / b)) ≤ b * c - a := by
  have h1 : log c - log (a / b) = log (c * b / a) := by
    rw [log_div ha.ne' hb.ne', log_div (by positivity) ha.ne', log_mul hc.ne' hb.ne']
    ring
  have h2 := Real.log_le_sub_one_of_pos (show 0 < c * b / a by positivity)
  rw [h1]
  calc a * log (c * b / a) ≤ a * (c * b / a - 1) := mul_le_mul_of_nonneg_left h2 ha.le
    _ = b * c - a := by field_simp

/-- The log-sum inequality on a finset. -/
theorem log_sum_inequality {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hab : ∀ i ∈ s, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤
      ∑ i ∈ s, a i * log (a i / b i) := by
  have hA0 : 0 ≤ ∑ i ∈ s, a i := sum_nonneg ha
  rcases hA0.eq_or_lt with h | hApos
  · have hz : ∀ i ∈ s, a i = 0 := (sum_eq_zero_iff_of_nonneg ha).1 h.symm
    rw [← h, zero_mul]
    apply le_of_eq
    symm
    apply sum_eq_zero
    intro i hi
    rw [hz i hi, zero_mul]
  · set A := ∑ i ∈ s, a i with hA
    set B := ∑ i ∈ s, b i with hB
    have hBpos : 0 < B := by
      obtain ⟨i, hi, hai⟩ : ∃ i ∈ s, 0 < a i := by
        by_contra hcon
        simp only [not_exists, not_and, not_lt] at hcon
        have : A ≤ 0 := sum_nonpos hcon
        linarith
      have hbi : 0 < b i :=
        lt_of_le_of_ne (hb i hi) (fun h0 => hai.ne' (hab i hi h0.symm))
      exact lt_of_lt_of_le hbi (single_le_sum hb hi)
    have hc : 0 < A / B := div_pos hApos hBpos
    have key : ∀ i ∈ s, a i * log (A / B) - a i * log (a i / b i) ≤
        b i * (A / B) - a i := by
      intro i hi
      rcases (ha i hi).eq_or_lt with h0 | hpos
      · rw [← h0]
        simp only [zero_mul, sub_self, sub_zero]
        exact mul_nonneg (hb i hi) hc.le
      · have hbi : 0 < b i :=
          lt_of_le_of_ne (hb i hi) (fun h0 => hpos.ne' (hab i hi h0.symm))
        have := mul_log_le_aux hpos hbi hc
        rw [mul_sub] at this
        linarith
    have hsum := sum_le_sum key
    rw [sum_sub_distrib, sum_sub_distrib, ← sum_mul, ← sum_mul] at hsum
    have hBA : B * (A / B) - A = 0 := by field_simp; ring
    linarith

lemma le_margX {p : X × Y → ℝ} (hp : ∀ z, 0 ≤ p z) (z : X × Y) : p z ≤ margX p z.1 :=
  single_le_sum (f := fun y => p (z.1, y)) (fun _ _ => hp _) (mem_univ z.2)

lemma le_margY {p : X × Y → ℝ} (hp : ∀ z, 0 ≤ p z) (z : X × Y) : p z ≤ margY p z.2 :=
  single_le_sum (f := fun x => p (x, z.2)) (fun _ _ => hp _) (mem_univ z.1)

lemma margX_nonneg {p : X × Y → ℝ} (hp : ∀ z, 0 ≤ p z) (x : X) : 0 ≤ margX p x :=
  sum_nonneg fun _ _ => hp _

lemma margY_nonneg {p : X × Y → ℝ} (hp : ∀ z, 0 ≤ p z) (y : Y) : 0 ≤ margY p y :=
  sum_nonneg fun _ _ => hp _

lemma prodMarg_nonneg {p : X × Y → ℝ} (hp : ∀ z, 0 ≤ p z) (z : X × Y) :
    0 ≤ margX p z.1 * margY p z.2 :=
  mul_nonneg (margX_nonneg hp _) (margY_nonneg hp _)

/-- Absolute continuity of `p` with respect to the product of its marginals. -/
lemma eq_zero_of_prodMarg_eq_zero {p : X × Y → ℝ} (hp : ∀ z, 0 ≤ p z) (z : X × Y)
    (h : margX p z.1 * margY p z.2 = 0) : p z = 0 := by
  rcases mul_eq_zero.1 h with h1 | h1
  · exact le_antisymm (h1 ▸ le_margX hp z) (hp z)
  · exact le_antisymm (h1 ▸ le_margY hp z) (hp z)

/-- Statement (1): mutual information of a pmf is nonnegative. -/
theorem mutualInfo_nonneg (p : X × Y → ℝ) (hp : ∀ z, 0 ≤ p z) (h1 : ∑ z, p z = 1) :
    0 ≤ mutualInfo p := by
  have hx : ∑ x, margX p x = 1 := by
    unfold margX
    rw [← Fintype.sum_prod_type]
    exact h1
  have hy : ∑ y, margY p y = 1 := by
    unfold margY
    rw [sum_comm, ← Fintype.sum_prod_type]
    exact h1
  have hq : ∑ z : X × Y, margX p z.1 * margY p z.2 = 1 := by
    simp only [Fintype.sum_prod_type]
    rw [← Fintype.sum_mul_sum, hx, hy, one_mul]
  have := log_sum_inequality univ p (fun z => margX p z.1 * margY p z.2)
    (fun z _ => hp z) (fun z _ => prodMarg_nonneg hp z)
    (fun z _ => eq_zero_of_prodMarg_eq_zero hp z)
  rw [h1, hq] at this
  simpa [mutualInfo] using this

/-- Statement (2): relabelling by bijections preserves mutual information. -/
theorem mutualInfo_relabel (f : X ≃ X') (g : Y ≃ Y') (p : X × Y → ℝ) :
    mutualInfo (relabel f g p) = mutualInfo p := by
  have hX : ∀ x', margX (relabel f g p) x' = margX p (f.symm x') := fun x' => by
    unfold margX relabel
    exact Equiv.sum_comp g.symm (fun y => p (f.symm x', y))
  have hY : ∀ y', margY (relabel f g p) y' = margY p (g.symm y') := fun y' => by
    unfold margY relabel
    exact Equiv.sum_comp f.symm (fun x => p (x, g.symm y'))
  unfold mutualInfo
  simp_rw [hX, hY]
  exact Equiv.sum_comp (f.prodCongr g).symm
    (fun z => p z * Real.log (p z / (margX p z.1 * margY p z.2)))

section push

variable [DecidableEq X'] [DecidableEq Y']

lemma fiber_mk (f : X → X') (g : Y → Y') (x' : X') (y' : Y') :
    fiber f g (x', y') =
      (univ.filter (fun x => f x = x')) ×ˢ (univ.filter (fun y => g y = y')) := by
  ext z
  simp [fiber, Prod.ext_iff]

theorem push_nonneg (f : X → X') (g : Y → Y') {p : X × Y → ℝ} (hp : ∀ z, 0 ≤ p z)
    (z' : X' × Y') : 0 ≤ push f g p z' :=
  sum_nonneg fun _ _ => hp _

theorem push_sum (f : X → X') (g : Y → Y') (p : X × Y → ℝ) :
    ∑ z', push f g p z' = ∑ z, p z :=
  sum_fiberwise univ (fun z : X × Y => (f z.1, g z.2)) p

lemma margX_push (f : X → X') (g : Y → Y') (p : X × Y → ℝ) (x' : X') :
    margX (push f g p) x' = ∑ x ∈ univ.filter (fun x => f x = x'), margX p x := by
  unfold margX push
  simp_rw [fiber_mk, sum_product]
  rw [sum_comm]
  exact sum_congr rfl fun x _ => sum_fiberwise univ g (fun y => p (x, y))

lemma margY_push (f : X → X') (g : Y → Y') (p : X × Y → ℝ) (y' : Y') :
    margY (push f g p) y' = ∑ y ∈ univ.filter (fun y => g y = y'), margY p y := by
  unfold margY push
  simp_rw [fiber_mk, sum_product_right]
  rw [sum_comm]
  exact sum_congr rfl fun y _ => sum_fiberwise univ f (fun x => p (x, y))

lemma sum_fiber_prodMarg (f : X → X') (g : Y → Y') (p : X × Y → ℝ) (z' : X' × Y') :
    ∑ z ∈ fiber f g z', margX p z.1 * margY p z.2 =
      margX (push f g p) z'.1 * margY (push f g p) z'.2 := by
  obtain ⟨x', y'⟩ := z'
  rw [fiber_mk, sum_product, margX_push, margY_push, sum_mul_sum]

lemma mutualInfo_fiberwise (f : X → X') (g : Y → Y') (p : X × Y → ℝ) :
    mutualInfo p = ∑ z', ∑ z ∈ fiber f g z',
      p z * Real.log (p z / (margX p z.1 * margY p z.2)) :=
  (sum_fiberwise univ (fun z : X × Y => (f z.1, g z.2)) _).symm

lemma mutualInfo_push_fiberwise (f : X → X') (g : Y → Y') (p : X × Y → ℝ) :
    mutualInfo (push f g p) = ∑ z', (∑ z ∈ fiber f g z', p z) *
      Real.log ((∑ z ∈ fiber f g z', p z) /
        (∑ z ∈ fiber f g z', margX p z.1 * margY p z.2)) := by
  unfold mutualInfo
  refine sum_congr rfl fun z' _ => ?_
  rw [sum_fiber_prodMarg]
  rfl

/-- Statement (3), data processing: local processing cannot increase mutual
information. -/
theorem mutualInfo_push_le (f : X → X') (g : Y → Y') (p : X × Y → ℝ)
    (hp : ∀ z, 0 ≤ p z) : mutualInfo (push f g p) ≤ mutualInfo p := by
  rw [mutualInfo_push_fiberwise, mutualInfo_fiberwise f g p]
  refine sum_le_sum fun z' _ => ?_
  exact log_sum_inequality _ p (fun z => margX p z.1 * margY p z.2)
    (fun z _ => hp z) (fun z _ => prodMarg_nonneg hp z)
    (fun z _ => eq_zero_of_prodMarg_eq_zero hp z)

lemma fiber_eq_singleton {f : X → X'} {g : Y → Y'} (hf : Function.Injective f)
    (hg : Function.Injective g) {z' : X' × Y'} {z : X × Y} (hz : z ∈ fiber f g z') :
    fiber f g z' = {z} := by
  refine eq_singleton_iff_unique_mem.2 ⟨hz, fun w hw => ?_⟩
  simp only [fiber, mem_filter, mem_univ, true_and] at hz hw
  have h := hw.trans hz.symm
  exact Prod.ext (hf (congrArg Prod.fst h)) (hg (congrArg Prod.snd h))

/-- Equality clause of (3): injective local maps preserve mutual information. -/
theorem mutualInfo_push_eq_of_injective (f : X → X') (g : Y → Y') (p : X × Y → ℝ)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    mutualInfo (push f g p) = mutualInfo p := by
  rw [mutualInfo_push_fiberwise, mutualInfo_fiberwise f g p]
  refine sum_congr rfl fun z' _ => ?_
  rcases (fiber f g z').eq_empty_or_nonempty with he | ⟨z, hz⟩
  · rw [he]
    simp only [sum_empty, zero_mul]
  · rw [fiber_eq_singleton hf hg hz]
    simp only [sum_singleton]

/-- For bijections the relabelled pmf is the pushforward. -/
theorem relabel_eq_push (f : X ≃ X') (g : Y ≃ Y') (p : X × Y → ℝ) :
    relabel f g p = push (⇑f) (⇑g) p := by
  funext z'
  have hz : (f.symm z'.1, g.symm z'.2) ∈ fiber (⇑f) (⇑g) z' := by
    simp [fiber]
  unfold push
  rw [fiber_eq_singleton f.injective g.injective hz, sum_singleton]
  rfl

end push

end MutualInfoLocalBijection
