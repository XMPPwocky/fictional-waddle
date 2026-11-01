import Mathlib

/-!
# Bridge6B: Nash bargaining along an r-chain of selves

Setting. `r ∈ (-1, 1)`, `θ = arccos r`, `k : ℕ`. An r-chain is a family
`v : Fin (k + 1) → E` of unit vectors with `r ≤ ⟪v i, v (i + 1)⟫` for consecutive indices.
Utilities are `u_i x = ⟪v i, x⟫` for `x` on the unit sphere, disagreement point `0`.
The Nash objective is `W v x = ∑ i, log ⟪v i, x⟫`, and the guaranteed value is
`bound θ k = ∑_{i=0}^{k} log cos ((i - k/2) θ)`.

PROVED (general real inner product space `E`, specialised to `ℝ^d = EuclideanSpace ℝ (Fin d)`,
`2 ≤ d`, in `main`):
* `exists_good_point`, `exists_feasible` (i, first half): if `k θ < π`, every r-chain has a unit
  `x` with `cos ((i - k/2) θ) ≤ ⟪v i, x⟫` for all `i`, hence `0 < ⟪v i, x⟫` for all `i`.
* `planar_infeasible` (i, second half): if `π ≤ k θ`, the planar chain
  `v i = cos (i θ) e₀ + sin (i θ) e₁` (an r-chain, `planar_isRChain`) has no `x` at all
  (unit or not) with `0 < ⟪v i, x⟫` for every `i`.
* `bound_le_nashW`, `bound_le_sSup` (ii, inequality): if `k θ < π`, every r-chain has a feasible
  `x` with `bound θ k ≤ W v x`, hence `bound θ k ≤ sSup (nashValues v)`.
* `planar_isGreatest`, `planar_sSup` (ii, equality): for the planar chain with `k θ < π`, the
  bisector `dir (k θ / 2)` is feasible with value exactly `bound θ k`, and every feasible
  `x` (even with `‖x‖ ≤ 1`) has `W ≤ bound θ k`; so `sSup (nashValues planar) = bound θ k`.
* `rescale` (iii): for arbitrary utilities `u i : X → ℝ` on a set `S` and `c i > 0`, rescaling
  `u i ↦ c i * u i` leaves the feasible set and the set of maximisers unchanged, shifts every
  objective value by `∑ log c i`, and shifts the least upper bound of the value set by
  `∑ log c i` (`rescale_sSup` for `sSup`). `nashValues_eq_valSet` identifies the inner-product
  case.
* Numbers at `r = 7/10` (`num_k1`, `num_k2`, `num_k3`, `num_k4`), with `G k = exp (bound / (k+1))`:
  `G 1 = cos (θ/2) = √(17/20)` (`= √0.85`, which is `≠ √(1 - 0.49)`), with
  `0.9219 < G 1 < 0.9220`; `G 2 = (49/100)^(1/3)`, `0.788 < G 2 < 0.789`;
  `bound θ 3 = log (289/2500)` with `289/2500 = 0.85 * 0.136`, `G 3 = (289/2500)^(1/4)`,
  `0.583 < G 3 < 0.584`, and `-2.16 < bound θ 3 < -2.15`; for `k = 4`, `π < 4 θ` and the planar
  r-chain at `r = 7/10` has no feasible point.

INTERPRETED:
* "unit sphere of ℝ^d" is `EuclideanSpace ℝ (Fin d)` with `‖·‖ = 1` hypotheses; the planar chain
  `(cos iθ, sin iθ)` is `cos (iθ) • single 0 1 + sin (iθ) • single 1 1` (coordinates checked in
  `planarRd_apply_zero/one/other`).
* `⟪v i, v (i+1)⟫ ≥ r` is indexed by `i : Fin k` via `castSucc`/`succ`.
* `sup_x ∑ log ⟪v i, x⟫` is the supremum over the feasible set
  `{x | ‖x‖ = 1 ∧ ∀ i, 0 < ⟪v i, x⟫}` (utilities strictly above the disagreement point), the set
  where every logarithm is of a positive number.
* The hypotheses `1 ≤ k` and `2 ≤ d` are only used where needed (`d` for the planar chain).
* Decimal approximations are stated as explicit rational bounds; `W ≈ -2.158` for `k = 3` is
  `bound θ 3 = log (289/2500) ∈ (-2.16, -2.15)`.
-/

namespace Bridge6B

open Real InnerProductGeometry
open scoped RealInnerProductSpace

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An r-chain of length `k + 1`: unit vectors with consecutive inner products at least `r`. -/
def IsRChain (r : ℝ) {k : ℕ} (v : Fin (k + 1) → E) : Prop :=
  (∀ i, ‖v i‖ = 1) ∧ ∀ i : Fin k, r ≤ ⟪v i.castSucc, v i.succ⟫

/-- `x` is a unit vector giving every utility `⟪v i, x⟫` strictly above the disagreement point. -/
def Feasible {k : ℕ} (v : Fin (k + 1) → E) (x : E) : Prop :=
  ‖x‖ = 1 ∧ ∀ i, 0 < ⟪v i, x⟫

/-- Nash welfare `∑ log u_i(x)`. -/
noncomputable def nashW {k : ℕ} (v : Fin (k + 1) → E) (x : E) : ℝ :=
  ∑ i, Real.log ⟪v i, x⟫

/-- Values of the Nash welfare over the feasible set. -/
def nashValues {k : ℕ} (v : Fin (k + 1) → E) : Set ℝ :=
  {W | ∃ x, Feasible v x ∧ nashW v x = W}

/-- The guaranteed welfare `∑_{i=0}^{k} log cos ((i - k/2) θ)`. -/
noncomputable def bound (θ : ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin (k + 1), Real.log (Real.cos ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ))

lemma angle_le_arccos_of_le {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {r : ℝ}
    (h : r ≤ ⟪a, b⟫) : angle a b ≤ arccos r := by
  unfold angle
  rw [ha, hb, mul_one, div_one]
  exact Real.arccos_le_arccos h

omit [InnerProductSpace ℝ E] in
lemma ne_zero_of_norm_one {a : E} (ha : ‖a‖ = 1) : a ≠ 0 := by
  intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha

lemma chain_angle_aux {r : ℝ} {k : ℕ} {v : Fin (k + 1) → E} (hv : IsRChain r v) :
    ∀ n i (h : i + n < k + 1),
      angle (v ⟨i, by omega⟩) (v ⟨i + n, h⟩) ≤ (n : ℝ) * arccos r := by
  intro n
  induction n with
  | zero =>
    intro i h
    have e : (⟨i + 0, h⟩ : Fin (k + 1)) = ⟨i, by omega⟩ := Fin.ext (by simp)
    rw [e, angle_self (ne_zero_of_norm_one (hv.1 _))]
    simp
  | succ n ih =>
    intro i h
    have h1 := ih i (by omega)
    have h2 : angle (v ⟨i + n, by omega⟩) (v ⟨i + (n + 1), h⟩) ≤ arccos r := by
      have := hv.2 ⟨i + n, by omega⟩
      have e1 : (Fin.castSucc (⟨i + n, by omega⟩ : Fin k)) = ⟨i + n, by omega⟩ := Fin.ext rfl
      have e2 : (Fin.succ (⟨i + n, by omega⟩ : Fin k)) = ⟨i + (n + 1), h⟩ :=
        Fin.ext (by simp only [Fin.val_succ]; omega)
      rw [e1, e2] at this
      exact angle_le_arccos_of_le (hv.1 _) (hv.1 _) this
    calc angle (v ⟨i, by omega⟩) (v ⟨i + (n + 1), h⟩)
        ≤ angle (v ⟨i, by omega⟩) (v ⟨i + n, by omega⟩)
          + angle (v ⟨i + n, by omega⟩) (v ⟨i + (n + 1), h⟩) := angle_le_angle_add_angle _ _ _
      _ ≤ (n : ℝ) * arccos r + arccos r := add_le_add h1 h2
      _ = ((n + 1 : ℕ) : ℝ) * arccos r := by push_cast; ring

/-- Spherical triangle inequality along the chain: `angle (v i) (v j) ≤ |i - j| θ`. -/
lemma chain_angle {r : ℝ} {k : ℕ} {v : Fin (k + 1) → E} (hv : IsRChain r v)
    (i j : Fin (k + 1)) :
    angle (v i) (v j) ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * arccos r := by
  rcases le_total (i : ℕ) (j : ℕ) with hij | hij
  · have := chain_angle_aux hv ((j : ℕ) - (i : ℕ)) i (by omega)
    have e : (⟨(i : ℕ) + ((j : ℕ) - (i : ℕ)), by omega⟩ : Fin (k + 1)) = j :=
      Fin.ext (by simp only; omega)
    have e' : (⟨(i : ℕ), by omega⟩ : Fin (k + 1)) = i := Fin.ext rfl
    rw [e, e'] at this
    have hc : |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| = (((j : ℕ) - (i : ℕ) : ℕ) : ℝ) := by
      rw [Nat.cast_sub hij, abs_sub_comm, abs_of_nonneg]
      exact sub_nonneg.2 (by exact_mod_cast hij)
    rw [hc]; exact this
  · have := chain_angle_aux hv ((i : ℕ) - (j : ℕ)) j (by omega)
    have e : (⟨(j : ℕ) + ((i : ℕ) - (j : ℕ)), by omega⟩ : Fin (k + 1)) = i :=
      Fin.ext (by simp only; omega)
    have e' : (⟨(j : ℕ), by omega⟩ : Fin (k + 1)) = j := Fin.ext rfl
    rw [e, e', angle_comm] at this
    have hc : |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| = (((i : ℕ) - (j : ℕ) : ℕ) : ℝ) := by
      rw [Nat.cast_sub hij, abs_of_nonneg]
      exact sub_nonneg.2 (by exact_mod_cast hij)
    rw [hc]; exact this

/-- The angle from `a` to `a + b` is at most half of `arccos r` when `r ≤ ⟪a, b⟫`. -/
lemma half_angle {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {r : ℝ} (hr1 : -1 < r)
    (hr2 : r ≤ 1) (h : r ≤ ⟪a, b⟫) : angle a (a + b) ≤ arccos r / 2 := by
  have hy2 : ‖a + b‖ ^ 2 = 2 + 2 * ⟪a, b⟫ := by rw [norm_add_sq_real, ha, hb]; ring
  have hypos : 0 < ‖a + b‖ := by nlinarith [norm_nonneg (a + b)]
  have hcos : Real.cos (angle a (a + b)) = (1 + ⟪a, b⟫) / ‖a + b‖ := by
    rw [cos_angle, inner_add_right, real_inner_self_eq_norm_sq, ha]; ring
  have hθ : Real.cos (arccos r / 2) = √((1 + r) / 2) := by
    rw [cos_half (by linarith [arccos_nonneg r, pi_pos]) (arccos_le_pi r),
      cos_arccos (by linarith) hr2]
  have key : Real.cos (arccos r / 2) ≤ Real.cos (angle a (a + b)) := by
    rw [hθ, hcos]
    have hnn : 0 ≤ (1 + ⟪a, b⟫) / ‖a + b‖ := div_nonneg (by linarith) hypos.le
    rw [← Real.sqrt_sq hnn]
    apply Real.sqrt_le_sqrt
    rw [div_pow, hy2, div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  exact (strictAntiOn_cos.le_iff_ge
    ⟨by linarith [arccos_nonneg r], by linarith [arccos_le_pi r, pi_pos]⟩
    ⟨angle_nonneg _ _, angle_le_pi _ _⟩).1 key

/-- Every r-chain has a unit "center" within angle `|i - k/2| θ` of every `v i`. -/
lemma exists_center {r : ℝ} (hr1 : -1 < r) (hr2 : r ≤ 1) {k : ℕ} {v : Fin (k + 1) → E}
    (hv : IsRChain r v) :
    ∃ x : E, ‖x‖ = 1 ∧
      ∀ i : Fin (k + 1), angle (v i) x ≤ |((i : ℕ) : ℝ) - (k : ℝ) / 2| * arccos r := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
  · subst hm
    refine ⟨v ⟨m, by omega⟩, hv.1 _, fun i => ?_⟩
    refine (chain_angle hv i ⟨m, by omega⟩).trans (le_of_eq ?_)
    congr 2
    push_cast; ring
  · subst hm
    have hab : r ≤ ⟪v ⟨m, by omega⟩, v ⟨m + 1, by omega⟩⟫ := hv.2 ⟨m, by omega⟩
    have hy2 : ‖v ⟨m, by omega⟩ + v ⟨m + 1, by omega⟩‖ ^ 2
        = 2 + 2 * ⟪v ⟨m, by omega⟩, v ⟨m + 1, by omega⟩⟫ := by
      rw [norm_add_sq_real, hv.1, hv.1]; ring
    have hypos : 0 < ‖v ⟨m, by omega⟩ + v ⟨m + 1, by omega⟩‖ := by
      nlinarith [norm_nonneg (v ⟨m, by omega⟩ + v ⟨m + 1, by omega⟩)]
    refine ⟨‖v ⟨m, by omega⟩ + v ⟨m + 1, by omega⟩‖⁻¹ • (v ⟨m, by omega⟩ + v ⟨m + 1, by omega⟩),
      ?_, fun i => ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hypos.ne']
    · rw [angle_smul_right_of_pos _ _ (inv_pos.2 hypos)]
      have hA := half_angle (hv.1 ⟨m, by omega⟩) (hv.1 ⟨m + 1, by omega⟩) hr1 hr2 hab
      have hB : angle (v ⟨m + 1, by omega⟩) (v ⟨m, by omega⟩ + v ⟨m + 1, by omega⟩)
          ≤ arccos r / 2 := by
        have := half_angle (hv.1 ⟨m + 1, by omega⟩) (hv.1 ⟨m, by omega⟩) hr1 hr2
          (by rwa [real_inner_comm])
        rwa [add_comm (v _) (v _)] at this
      have hθ := arccos_nonneg r
      rcases le_or_gt (i : ℕ) m with hi | hi
      · have hi' : ((i : ℕ) : ℝ) ≤ m := by exact_mod_cast hi
        have hc := chain_angle hv i ⟨m, by omega⟩
        simp only at hc
        calc angle (v i) (v ⟨m, by omega⟩ + v ⟨m + 1, by omega⟩)
            ≤ angle (v i) (v ⟨m, by omega⟩)
              + angle (v ⟨m, by omega⟩) (v ⟨m, by omega⟩ + v ⟨m + 1, by omega⟩) :=
                angle_le_angle_add_angle _ _ _
          _ ≤ |((i : ℕ) : ℝ) - (m : ℝ)| * arccos r + arccos r / 2 := add_le_add hc hA
          _ = |((i : ℕ) : ℝ) - ((2 * m + 1 : ℕ) : ℝ) / 2| * arccos r := by
              rw [abs_of_nonpos (by linarith), abs_of_nonpos (by push_cast; linarith)]
              push_cast; ring
      · have hi' : (m : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hi
        have hc := chain_angle hv i ⟨m + 1, by omega⟩
        simp only at hc
        calc angle (v i) (v ⟨m, by omega⟩ + v ⟨m + 1, by omega⟩)
            ≤ angle (v i) (v ⟨m + 1, by omega⟩)
              + angle (v ⟨m + 1, by omega⟩) (v ⟨m, by omega⟩ + v ⟨m + 1, by omega⟩) :=
                angle_le_angle_add_angle _ _ _
          _ ≤ |((i : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ)| * arccos r + arccos r / 2 := add_le_add hc hB
          _ = |((i : ℕ) : ℝ) - ((2 * m + 1 : ℕ) : ℝ) / 2| * arccos r := by
              rw [abs_of_nonneg (by push_cast; linarith), abs_of_nonneg (by push_cast; linarith)]
              push_cast; ring

lemma inner_ge_of_angle_le {a x : E} (ha : ‖a‖ = 1) (hx : ‖x‖ = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (htπ : t ≤ π) (h : angle a x ≤ t) : Real.cos t ≤ ⟪a, x⟫ := by
  have : ⟪a, x⟫ = Real.cos (angle a x) := by rw [cos_angle, ha, hx]; simp
  rw [this]
  exact (strictAntiOn_cos.le_iff_ge ⟨ht0, htπ⟩ ⟨angle_nonneg _ _, angle_le_pi _ _⟩).2 h

lemma cos_bound_pos {θ : ℝ} (hθ : 0 ≤ θ) {k : ℕ} (hk : (k : ℝ) * θ < π) (i : Fin (k + 1)) :
    0 < Real.cos ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ) := by
  apply Real.cos_pos_of_mem_Ioo
  have hi : ((i : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 i.2
  have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 := mul_nonneg hi0 hθ
  have h2 := mul_nonneg (sub_nonneg.2 hi) hθ
  constructor <;> nlinarith

/-- (i)/(ii): for `k θ < π` every r-chain has a unit `x` with
`cos ((i - k/2) θ) ≤ ⟪v i, x⟫`, and all these utilities are positive. -/
theorem exists_good_point {r : ℝ} (hr1 : -1 < r) (hr2 : r < 1) {k : ℕ}
    (hk : (k : ℝ) * arccos r < π) {v : Fin (k + 1) → E} (hv : IsRChain r v) :
    ∃ x, Feasible v x ∧
      ∀ i : Fin (k + 1), Real.cos ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * arccos r) ≤ ⟪v i, x⟫ := by
  obtain ⟨x, hx, hang⟩ := exists_center hr1 hr2.le hv
  have hθ := arccos_nonneg r
  have hbd : ∀ i : Fin (k + 1),
      Real.cos ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * arccos r) ≤ ⟪v i, x⟫ := by
    intro i
    have hi : ((i : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 i.2
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    have hab : |((i : ℕ) : ℝ) - (k : ℝ) / 2| ≤ (k : ℝ) / 2 :=
      abs_le.2 ⟨by linarith, by linarith⟩
    have habs : |((i : ℕ) : ℝ) - (k : ℝ) / 2| * arccos r ≤ π := by
      have := mul_le_mul_of_nonneg_right hab hθ
      nlinarith [pi_pos]
    have := inner_ge_of_angle_le (hv.1 i) hx (mul_nonneg (abs_nonneg _) hθ) habs (hang i)
    rwa [← abs_of_nonneg hθ, ← abs_mul, Real.cos_abs] at this
  exact ⟨x, ⟨hx, fun i => lt_of_lt_of_le (cos_bound_pos hθ hk i) (hbd i)⟩, hbd⟩

/-- (i), first half. -/
theorem exists_feasible {r : ℝ} (hr1 : -1 < r) (hr2 : r < 1) {k : ℕ}
    (hk : (k : ℝ) * arccos r < π) {v : Fin (k + 1) → E} (hv : IsRChain r v) :
    ∃ x, Feasible v x := by
  obtain ⟨x, hx, -⟩ := exists_good_point hr1 hr2 hk hv
  exact ⟨x, hx⟩

/-- (ii), inequality: a feasible point with welfare at least `bound θ k`. -/
theorem bound_le_nashW {r : ℝ} (hr1 : -1 < r) (hr2 : r < 1) {k : ℕ}
    (hk : (k : ℝ) * arccos r < π) {v : Fin (k + 1) → E} (hv : IsRChain r v) :
    ∃ x, Feasible v x ∧ bound (arccos r) k ≤ nashW v x := by
  obtain ⟨x, hx, hbd⟩ := exists_good_point hr1 hr2 hk hv
  refine ⟨x, hx, Finset.sum_le_sum fun i _ => ?_⟩
  exact Real.log_le_log (cos_bound_pos (arccos_nonneg r) hk i) (hbd i)

lemma nashValues_bddAbove {r : ℝ} {k : ℕ} {v : Fin (k + 1) → E} (hv : IsRChain r v) :
    BddAbove (nashValues v) := by
  refine ⟨0, ?_⟩
  rintro W ⟨x, ⟨hx, hpos⟩, rfl⟩
  refine Finset.sum_nonpos fun i _ => Real.log_nonpos (hpos i).le ?_
  have := real_inner_le_norm (v i) x
  rw [hv.1 i, hx] at this; linarith

/-- (ii), inequality, as a statement about the supremum. -/
theorem bound_le_sSup {r : ℝ} (hr1 : -1 < r) (hr2 : r < 1) {k : ℕ}
    (hk : (k : ℝ) * arccos r < π) {v : Fin (k + 1) → E} (hv : IsRChain r v) :
    bound (arccos r) k ≤ sSup (nashValues v) := by
  obtain ⟨x, hx, hb⟩ := bound_le_nashW hr1 hr2 hk hv
  exact hb.trans (le_csSup (nashValues_bddAbove hv) ⟨x, hx, rfl⟩)

/-! ### The planar equally spaced chain -/

/-- The unit direction at angle `φ` in the plane spanned by `e₀, e₁`. -/
noncomputable def dir (e₀ e₁ : E) (φ : ℝ) : E := Real.cos φ • e₀ + Real.sin φ • e₁

/-- The planar chain `v i = cos (i θ) e₀ + sin (i θ) e₁`. -/
noncomputable def planar (e₀ e₁ : E) (θ : ℝ) (k : ℕ) : Fin (k + 1) → E :=
  fun i => dir e₀ e₁ (((i : ℕ) : ℝ) * θ)

variable {e₀ e₁ : E}

lemma inner_dir_left (x : E) (φ : ℝ) :
    ⟪dir e₀ e₁ φ, x⟫ = Real.cos φ * ⟪e₀, x⟫ + Real.sin φ * ⟪e₁, x⟫ := by
  simp [dir, inner_add_left, real_inner_smul_left]

lemma inner_dir_dir (h0 : ‖e₀‖ = 1) (h1 : ‖e₁‖ = 1) (h01 : ⟪e₀, e₁⟫ = 0) (a b : ℝ) :
    ⟪dir e₀ e₁ a, dir e₀ e₁ b⟫ = Real.cos (a - b) := by
  have h10 : ⟪e₁, e₀⟫ = 0 := by rw [real_inner_comm]; exact h01
  rw [inner_dir_left]
  simp only [dir, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, h0, h1,
    h01, h10]
  rw [Real.cos_sub]; ring

lemma norm_dir (h0 : ‖e₀‖ = 1) (h1 : ‖e₁‖ = 1) (h01 : ⟪e₀, e₁⟫ = 0) (a : ℝ) :
    ‖dir e₀ e₁ a‖ = 1 := by
  have h := inner_dir_dir h0 h1 h01 a a
  rw [sub_self, Real.cos_zero, real_inner_self_eq_norm_sq] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

theorem planar_isRChain (h0 : ‖e₀‖ = 1) (h1 : ‖e₁‖ = 1) (h01 : ⟪e₀, e₁⟫ = 0) {r : ℝ}
    (hr1 : -1 ≤ r) (hr2 : r ≤ 1) (k : ℕ) : IsRChain r (planar e₀ e₁ (arccos r) k) := by
  refine ⟨fun i => norm_dir h0 h1 h01 _, fun i => ?_⟩
  simp only [planar, inner_dir_dir h0 h1 h01, Fin.val_castSucc, Fin.val_succ]
  push_cast
  rw [show ((i : ℕ) : ℝ) * arccos r - (((i : ℕ) : ℝ) + 1) * arccos r = -arccos r by ring,
    Real.cos_neg, cos_arccos hr1 hr2]

/-- (ii), equality case: the bisector is feasible and attains `bound θ k`. -/
theorem planar_bisector (h0 : ‖e₀‖ = 1) (h1 : ‖e₁‖ = 1) (h01 : ⟪e₀, e₁⟫ = 0) {θ : ℝ}
    (hθ : 0 ≤ θ) {k : ℕ} (hk : (k : ℝ) * θ < π) :
    Feasible (planar e₀ e₁ θ k) (dir e₀ e₁ ((k : ℝ) * θ / 2)) ∧
      nashW (planar e₀ e₁ θ k) (dir e₀ e₁ ((k : ℝ) * θ / 2)) = bound θ k := by
  have he : ∀ i : Fin (k + 1), ⟪planar e₀ e₁ θ k i, dir e₀ e₁ ((k : ℝ) * θ / 2)⟫
      = Real.cos ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ) := by
    intro i
    simp only [planar, inner_dir_dir h0 h1 h01]
    congr 1; ring
  refine ⟨⟨norm_dir h0 h1 h01 _, fun i => ?_⟩, ?_⟩
  · rw [he]; exact cos_bound_pos hθ hk i
  · simp only [nashW, bound, he]

lemma bessel2 (h0 : ‖e₀‖ = 1) (h1 : ‖e₁‖ = 1) (h01 : ⟪e₀, e₁⟫ = 0) (x : E) :
    ⟪e₀, x⟫ ^ 2 + ⟪e₁, x⟫ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h10 : ⟪e₁, e₀⟫ = 0 := by rw [real_inner_comm]; exact h01
  have h00 : ⟪e₀, e₀⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h0]; norm_num
  have h11 : ⟪e₁, e₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h1]; norm_num
  have hxx : ⟪x, x⟫ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  have := real_inner_self_nonneg (x := x - (⟪e₀, x⟫ • e₀ + ⟪e₁, x⟫ • e₁))
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, h00, h11, hxx, h01, h10,
    real_inner_comm e₀ x, real_inner_comm e₁ x] at this
  nlinarith

lemma pair_le {θ : ℝ} {k : ℕ} (i : ℕ) (hi : i ≤ k) (p q : ℝ) (hpq : p ^ 2 + q ^ 2 ≤ 1) :
    (Real.cos ((i : ℝ) * θ) * p + Real.sin ((i : ℝ) * θ) * q) *
      (Real.cos (((k - i : ℕ) : ℝ) * θ) * p + Real.sin (((k - i : ℕ) : ℝ) * θ) * q)
      ≤ Real.cos (((i : ℝ) - (k : ℝ) / 2) * θ) ^ 2 := by
  have e1 : (i : ℝ) * θ = (k : ℝ) * θ / 2 + ((i : ℝ) - (k : ℝ) / 2) * θ := by ring
  have e2 : ((k - i : ℕ) : ℝ) * θ = (k : ℝ) * θ / 2 - ((i : ℝ) - (k : ℝ) / 2) * θ := by
    rw [Nat.cast_sub hi]; ring
  rw [e1, e2, Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub]
  generalize (k : ℝ) * θ / 2 = c
  generalize ((i : ℝ) - (k : ℝ) / 2) * θ = α
  have hPQ : (Real.cos c * p + Real.sin c * q) ^ 2 + (-Real.sin c * p + Real.cos c * q) ^ 2
      = p ^ 2 + q ^ 2 := by
    linear_combination (p ^ 2 + q ^ 2) * Real.sin_sq_add_cos_sq c
  have hprod : (Real.cos c * Real.cos α - Real.sin c * Real.sin α) * p
        + (Real.sin c * Real.cos α + Real.cos c * Real.sin α) * q
      = Real.cos α * (Real.cos c * p + Real.sin c * q)
        + Real.sin α * (-Real.sin c * p + Real.cos c * q) := by ring
  have hprod' : (Real.cos c * Real.cos α + Real.sin c * Real.sin α) * p
        + (Real.sin c * Real.cos α - Real.cos c * Real.sin α) * q
      = Real.cos α * (Real.cos c * p + Real.sin c * q)
        - Real.sin α * (-Real.sin c * p + Real.cos c * q) := by ring
  rw [hprod, hprod']
  generalize Real.cos c * p + Real.sin c * q = P at hPQ ⊢
  generalize -Real.sin c * p + Real.cos c * q = Q at hPQ ⊢
  have hP : P ^ 2 ≤ 1 := by nlinarith [sq_nonneg Q]
  have := mul_le_mul_of_nonneg_left hP (sq_nonneg (Real.cos α))
  nlinarith [sq_nonneg (Real.sin α * Q)]

/-- (ii), equality case: no feasible point of the planar chain beats `bound θ k`
(here `x` need only satisfy `‖x‖ ≤ 1`; no hypothesis on `θ` or `k` is needed). -/
theorem planar_upper (h0 : ‖e₀‖ = 1) (h1 : ‖e₁‖ = 1) (h01 : ⟪e₀, e₁⟫ = 0) (θ : ℝ)
    (k : ℕ) (x : E) (hx : ‖x‖ ≤ 1)
    (hpos : ∀ i, 0 < ⟪planar e₀ e₁ θ k i, x⟫) :
    nashW (planar e₀ e₁ θ k) x ≤ bound θ k := by
  have hpq : ⟪e₀, x⟫ ^ 2 + ⟪e₁, x⟫ ^ 2 ≤ 1 := by
    have := bessel2 h0 h1 h01 x
    nlinarith [norm_nonneg x]
  have hu : ∀ i : Fin (k + 1), ⟪planar e₀ e₁ θ k i, x⟫
      = Real.cos (((i : ℕ) : ℝ) * θ) * ⟪e₀, x⟫ + Real.sin (((i : ℕ) : ℝ) * θ) * ⟪e₁, x⟫ :=
    fun i => inner_dir_left _ _
  have hrev : ∑ i : Fin (k + 1), Real.log ⟪planar e₀ e₁ θ k i.rev, x⟫
      = nashW (planar e₀ e₁ θ k) x :=
    Equiv.sum_comp Fin.revPerm (fun i => Real.log ⟪planar e₀ e₁ θ k i, x⟫)
  have hpair : ∀ i : Fin (k + 1),
      Real.log ⟪planar e₀ e₁ θ k i, x⟫ + Real.log ⟪planar e₀ e₁ θ k i.rev, x⟫
        ≤ 2 * Real.log (Real.cos ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ)) := by
    intro i
    rw [← Real.log_mul (hpos i).ne' (hpos _).ne']
    have h2 : 2 * Real.log (Real.cos ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ))
        = Real.log (Real.cos ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ) ^ 2) := by
      rw [Real.log_pow]; norm_num
    rw [h2]
    apply Real.log_le_log (mul_pos (hpos i) (hpos _))
    rw [hu, hu, Fin.val_rev]
    have : k + 1 - ((i : ℕ) + 1) = k - (i : ℕ) := by omega
    rw [this]
    exact pair_le (i : ℕ) (by omega) _ _ hpq
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpair i)
  rw [Finset.sum_add_distrib, hrev, ← Finset.mul_sum] at this
  unfold nashW at this ⊢
  unfold bound
  linarith

theorem planar_isGreatest (h0 : ‖e₀‖ = 1) (h1 : ‖e₁‖ = 1) (h01 : ⟪e₀, e₁⟫ = 0) {θ : ℝ}
    (hθ : 0 ≤ θ) {k : ℕ} (hk : (k : ℝ) * θ < π) :
    IsGreatest (nashValues (planar e₀ e₁ θ k)) (bound θ k) := by
  refine ⟨⟨_, (planar_bisector h0 h1 h01 hθ hk).1, (planar_bisector h0 h1 h01 hθ hk).2⟩, ?_⟩
  rintro W ⟨x, ⟨hx, hpos⟩, rfl⟩
  exact planar_upper h0 h1 h01 θ k x hx.le hpos

theorem planar_sSup (h0 : ‖e₀‖ = 1) (h1 : ‖e₁‖ = 1) (h01 : ⟪e₀, e₁⟫ = 0) {θ : ℝ}
    (hθ : 0 ≤ θ) {k : ℕ} (hk : (k : ℝ) * θ < π) :
    sSup (nashValues (planar e₀ e₁ θ k)) = bound θ k :=
  (planar_isGreatest h0 h1 h01 hθ hk).csSup_eq

/-- (i), second half: if `π ≤ k θ` (and `θ < π`), no `x` makes every planar utility positive. -/
theorem planar_infeasible {θ : ℝ} (hθπ : θ < π) {k : ℕ} (hk : π ≤ (k : ℝ) * θ) (x : E) :
    ¬ ∀ i, 0 < ⟪planar e₀ e₁ θ k i, x⟫ := by
  intro hpos
  set z : ℂ := ⟨⟪e₀, x⟫, ⟪e₁, x⟫⟩
  have hre : ‖z‖ * Real.cos (Complex.arg z) = ⟪e₀, x⟫ := Complex.norm_mul_cos_arg z
  have him : ‖z‖ * Real.sin (Complex.arg z) = ⟪e₁, x⟫ := Complex.norm_mul_sin_arg z
  have hc : ∀ i : Fin (k + 1), 0 < Real.cos (((i : ℕ) : ℝ) * θ - Complex.arg z) := by
    intro i
    have h := hpos i
    have hu : ⟪planar e₀ e₁ θ k i, x⟫
        = ‖z‖ * Real.cos (((i : ℕ) : ℝ) * θ - Complex.arg z) := by
      simp only [planar]
      rw [inner_dir_left, Real.cos_sub, ← hre, ← him]; ring
    rw [hu] at h
    exact pos_of_mul_pos_right h (norm_nonneg _)
  have hφ1 := Complex.neg_pi_lt_arg z
  have hφ2 := Complex.arg_le_pi z
  have hcφ : 0 < Real.cos (Complex.arg z) := by
    have := hc 0
    simpa using this
  have hφlt : Complex.arg z < π / 2 := by
    by_contra hcon; push Not at hcon
    have := Real.cos_nonpos_of_pi_div_two_le_of_le hcon (by linarith [pi_pos])
    linarith
  have hφgt : -(π / 2) < Complex.arg z := by
    by_contra hcon; push Not at hcon
    have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := -Complex.arg z) (by linarith)
      (by linarith [pi_pos])
    rw [Real.cos_neg] at this
    linarith
  have claim : ∀ n : ℕ, n ≤ k → (n : ℝ) * θ - Complex.arg z < π / 2 := by
    intro n
    induction n with
    | zero => intro _; simp; linarith
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := hc ⟨n + 1, by omega⟩
      simp only at h2
      by_contra hcon; push Not at hcon
      have := Real.cos_nonpos_of_pi_div_two_le_of_le hcon (by push_cast at h1 ⊢; linarith)
      linarith
  have := claim k le_rfl
  linarith

end General

/-! ### (iii) Rescaling utilities -/

section Rescale

variable {ι X : Type*} [Fintype ι]

/-- Points of `S` where every utility is strictly above the disagreement point `0`. -/
def feasSet (S : Set X) (u : ι → X → ℝ) : Set X := {x | x ∈ S ∧ ∀ i, 0 < u i x}

/-- Nash welfare for general utilities. -/
noncomputable def welfare (u : ι → X → ℝ) (x : X) : ℝ := ∑ i, Real.log (u i x)

/-- The set of feasible welfare values. -/
def valSet (S : Set X) (u : ι → X → ℝ) : Set ℝ := welfare u '' feasSet S u

/-- Rescaled utilities `c i * u i`. -/
def scale (c : ι → ℝ) (u : ι → X → ℝ) : ι → X → ℝ := fun i x => c i * u i x

theorem rescale (S : Set X) (u : ι → X → ℝ) (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    feasSet S (scale c u) = feasSet S u ∧
    (∀ x ∈ feasSet S u, welfare (scale c u) x = (∑ i, Real.log (c i)) + welfare u x) ∧
    (∀ x, (x ∈ feasSet S (scale c u) ∧
        ∀ y ∈ feasSet S (scale c u), welfare (scale c u) y ≤ welfare (scale c u) x) ↔
      (x ∈ feasSet S u ∧ ∀ y ∈ feasSet S u, welfare u y ≤ welfare u x)) ∧
    (∀ M, IsLUB (valSet S (scale c u)) ((∑ i, Real.log (c i)) + M) ↔
      IsLUB (valSet S u) M) := by
  have hF : feasSet S (scale c u) = feasSet S u := by
    ext x
    simp only [feasSet, scale, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hS, h⟩; exact ⟨hS, fun i => pos_of_mul_pos_right (h i) (hc i).le⟩
    · rintro ⟨hS, h⟩; exact ⟨hS, fun i => mul_pos (hc i) (h i)⟩
  have hW : ∀ x ∈ feasSet S u, welfare (scale c u) x = (∑ i, Real.log (c i)) + welfare u x := by
    intro x hx
    simp only [welfare, scale]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Real.log_mul (hc i).ne' (hx.2 i).ne'
  have hV : valSet S (scale c u) = OrderIso.addLeft (∑ i, Real.log (c i)) '' valSet S u := by
    ext w
    simp only [valSet, Set.mem_image, hF, OrderIso.addLeft_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨welfare u x, ⟨x, hx, rfl⟩, (hW x hx).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, hW x hx⟩
  refine ⟨hF, hW, fun x => ?_, fun M => ?_⟩
  · rw [hF]
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨hx, fun y hy => ?_⟩
      have := h y hy
      rw [hW y hy, hW x hx] at this; linarith
    · rintro ⟨hx, h⟩
      refine ⟨hx, fun y hy => ?_⟩
      rw [hW y hy, hW x hx]; linarith [h y hy]
  · rw [hV]
    exact (OrderIso.addLeft (∑ i, Real.log (c i))).isLUB_image'

theorem rescale_sSup (S : Set X) (u : ι → X → ℝ) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hne : (valSet S u).Nonempty) (hbdd : BddAbove (valSet S u)) :
    sSup (valSet S (scale c u)) = (∑ i, Real.log (c i)) + sSup (valSet S u) := by
  have h := ((rescale S u c hc).2.2.2 (sSup (valSet S u))).2 (isLUB_csSup hne hbdd)
  have hne' : (valSet S (scale c u)).Nonempty := by
    obtain ⟨w, x, hx, rfl⟩ := hne
    exact ⟨_, x, (rescale S u c hc).1 ▸ hx, rfl⟩
  exact h.csSup_eq hne'

end Rescale

section Identify

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner-product Nash problem is the general one with `S` the unit sphere. -/
theorem nashValues_eq_valSet {k : ℕ} (v : Fin (k + 1) → E) :
    nashValues v = valSet (Metric.sphere (0 : E) 1) (fun i x => ⟪v i, x⟫) := by
  ext W
  simp [nashValues, valSet, feasSet, Feasible, welfare, nashW, ]

/-- Rescaling `u_i ↦ c_i u_i` is the same as replacing `v i` by `c i • v i`. -/
theorem scale_eq_smul {k : ℕ} (v : Fin (k + 1) → E) (c : Fin (k + 1) → ℝ) :
    scale c (fun i x => ⟪v i, x⟫) = fun i x => ⟪c i • v i, x⟫ := by
  funext i x; simp [scale, real_inner_smul_left]

end Identify

/-! ### Specialisation to `ℝ^d` -/

section Rd

/-- First basis vector of `ℝ^d`. -/
noncomputable def eA (d : ℕ) (hd : 2 ≤ d) : EuclideanSpace ℝ (Fin d) :=
  EuclideanSpace.single ⟨0, by omega⟩ 1

/-- Second basis vector of `ℝ^d`. -/
noncomputable def eB (d : ℕ) (hd : 2 ≤ d) : EuclideanSpace ℝ (Fin d) :=
  EuclideanSpace.single ⟨1, by omega⟩ 1

lemma norm_eA (d : ℕ) (hd : 2 ≤ d) : ‖eA d hd‖ = 1 := by simp [eA]
lemma norm_eB (d : ℕ) (hd : 2 ≤ d) : ‖eB d hd‖ = 1 := by simp [eB]
lemma inner_eA_eB (d : ℕ) (hd : 2 ≤ d) : ⟪eA d hd, eB d hd⟫ = 0 := by
  simp [eA, eB, EuclideanSpace.inner_single_left, Fin.ext_iff]

/-- The planar chain `v i = (cos iθ, sin iθ, 0, …, 0)` in `ℝ^d`. -/
noncomputable def planarRd (d : ℕ) (hd : 2 ≤ d) (θ : ℝ) (k : ℕ) :
    Fin (k + 1) → EuclideanSpace ℝ (Fin d) :=
  planar (eA d hd) (eB d hd) θ k

lemma planarRd_apply_zero (d : ℕ) (hd : 2 ≤ d) (θ : ℝ) (k : ℕ) (i : Fin (k + 1)) :
    planarRd d hd θ k i ⟨0, by omega⟩ = Real.cos (((i : ℕ) : ℝ) * θ) := by
  simp [planarRd, planar, dir, eA, eB]

lemma planarRd_apply_one (d : ℕ) (hd : 2 ≤ d) (θ : ℝ) (k : ℕ) (i : Fin (k + 1)) :
    planarRd d hd θ k i ⟨1, by omega⟩ = Real.sin (((i : ℕ) : ℝ) * θ) := by
  simp [planarRd, planar, dir, eA, eB]

lemma planarRd_apply_other (d : ℕ) (hd : 2 ≤ d) (θ : ℝ) (k : ℕ) (i : Fin (k + 1))
    (j : Fin d) (hj : 2 ≤ (j : ℕ)) : planarRd d hd θ k i j = 0 := by
  have h0 : j ≠ ⟨0, by omega⟩ := fun h => by rw [h] at hj; simp at hj
  have h1 : j ≠ ⟨1, by omega⟩ := fun h => by rw [h] at hj; simp at hj
  simp [planarRd, planar, dir, eA, eB, h0, h1]

/-- The full statement in `ℝ^d`. -/
theorem main (d : ℕ) (hd : 2 ≤ d) (r : ℝ) (hr1 : -1 < r) (hr2 : r < 1) (k : ℕ) :
    -- (i) first half
    ((k : ℝ) * arccos r < π → ∀ v : Fin (k + 1) → EuclideanSpace ℝ (Fin d),
        IsRChain r v → ∃ x, Feasible v x) ∧
    -- (i) second half
    (π ≤ (k : ℝ) * arccos r → IsRChain r (planarRd d hd (arccos r) k) ∧
        ∀ x, ¬ ∀ i, 0 < ⟪planarRd d hd (arccos r) k i, x⟫) ∧
    -- (ii)
    ((k : ℝ) * arccos r < π →
        (∀ v : Fin (k + 1) → EuclideanSpace ℝ (Fin d), IsRChain r v →
          ∃ x, Feasible v x ∧ bound (arccos r) k ≤ nashW v x) ∧
        (∀ v : Fin (k + 1) → EuclideanSpace ℝ (Fin d), IsRChain r v →
          bound (arccos r) k ≤ sSup (nashValues v)) ∧
        IsRChain r (planarRd d hd (arccos r) k) ∧
        Feasible (planarRd d hd (arccos r) k) (dir (eA d hd) (eB d hd) ((k : ℝ) * arccos r / 2)) ∧
        nashW (planarRd d hd (arccos r) k) (dir (eA d hd) (eB d hd) ((k : ℝ) * arccos r / 2))
          = bound (arccos r) k ∧
        IsGreatest (nashValues (planarRd d hd (arccos r) k)) (bound (arccos r) k) ∧
        sSup (nashValues (planarRd d hd (arccos r) k)) = bound (arccos r) k) := by
  have h0 := norm_eA d hd
  have h1 := norm_eB d hd
  have h01 := inner_eA_eB d hd
  have hθ := arccos_nonneg r
  have hch := planar_isRChain h0 h1 h01 hr1.le hr2.le k
  refine ⟨fun hk v hv => exists_feasible hr1 hr2 hk hv, fun hk => ⟨hch, fun x =>
    planar_infeasible (Real.arccos_lt_pi.2 hr1) hk x⟩, fun hk => ⟨fun v hv =>
    bound_le_nashW hr1 hr2 hk hv, fun v hv => bound_le_sSup hr1 hr2 hk hv, hch,
    (planar_bisector h0 h1 h01 hθ hk).1, (planar_bisector h0 h1 h01 hθ hk).2,
    planar_isGreatest h0 h1 h01 hθ hk, planar_sSup h0 h1 h01 hθ hk⟩⟩

end Rd

/-! ### Numbers at `r = 7/10` -/

section Numbers

lemma bound_eq_log_prod {θ : ℝ} (hθ : 0 ≤ θ) {k : ℕ} (hk : (k : ℝ) * θ < π) :
    bound θ k = Real.log (∏ i : Fin (k + 1), Real.cos ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ)) := by
  unfold bound
  rw [Real.log_prod]
  intro i _; exact (cos_bound_pos hθ hk i).ne'

lemma exp_bound_eq {θ : ℝ} (hθ : 0 ≤ θ) {k : ℕ} (hk : (k : ℝ) * θ < π) :
    Real.exp (bound θ k / ((k : ℝ) + 1)) =
      (∏ i : Fin (k + 1), Real.cos ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ)) ^ (1 / ((k : ℝ) + 1)) := by
  have hpos : 0 < ∏ i : Fin (k + 1), Real.cos ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ) :=
    Finset.prod_pos fun i _ => cos_bound_pos hθ hk i
  rw [Real.rpow_def_of_pos hpos, bound_eq_log_prod hθ hk]
  congr 1; ring

lemma cos_half_seven : Real.cos (arccos (7 / 10 : ℝ) / 2) = √(17 / 20) := by
  rw [cos_half (by linarith [arccos_nonneg (7 / 10 : ℝ), pi_pos]) (arccos_le_pi _),
    cos_arccos (by norm_num) (by norm_num)]
  norm_num

lemma theta_lt_pi_div_three : arccos (7 / 10 : ℝ) < π / 3 := by
  have h := (strictAntiOn_cos.lt_iff_gt (a := π / 3) (b := arccos (7 / 10 : ℝ))
    ⟨by linarith [pi_pos], by linarith [pi_pos]⟩ ⟨arccos_nonneg _, arccos_le_pi _⟩)
  rw [Real.cos_pi_div_three, cos_arccos (by norm_num) (by norm_num)] at h
  exact h.1 (by norm_num)

lemma pi_div_four_lt_theta : π / 4 < arccos (7 / 10 : ℝ) := by
  have h := (strictAntiOn_cos.lt_iff_gt (a := arccos (7 / 10 : ℝ)) (b := π / 4)
    ⟨arccos_nonneg _, arccos_le_pi _⟩ ⟨by linarith [pi_pos], by linarith [pi_pos]⟩)
  rw [Real.cos_pi_div_four, cos_arccos (by norm_num) (by norm_num)] at h
  refine h.1 ?_
  have : (7 / 5 : ℝ) < √2 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  linarith

/-- `k = 1`: `exp (W/2) = cos (θ/2) = √0.85`, not `√(1 - 0.49)`; numerically `≈ 0.922`. -/
theorem num_k1 :
    ((1 : ℕ) : ℝ) * arccos (7 / 10 : ℝ) < π ∧
    Real.exp (bound (arccos (7 / 10)) 1 / ((1 : ℕ) + 1)) = Real.cos (arccos (7 / 10 : ℝ) / 2) ∧
    Real.cos (arccos (7 / 10 : ℝ) / 2) = √(85 / 100) ∧
    √(85 / 100 : ℝ) ≠ √(1 - 49 / 100) ∧
    (0.9219 : ℝ) < √(85 / 100) ∧ √(85 / 100 : ℝ) < 0.9220 := by
  have hk : ((1 : ℕ) : ℝ) * arccos (7 / 10 : ℝ) < π := by
    simpa using Real.arccos_lt_pi.2 (by norm_num : (-1 : ℝ) < 7 / 10)
  have hc := cos_half_seven
  have h17 : (17 / 20 : ℝ) = 85 / 100 := by norm_num
  refine ⟨hk, ?_, by rw [hc, h17], ?_, ?_, ?_⟩
  · rw [exp_bound_eq (arccos_nonneg _) hk, Fin.prod_univ_two]
    simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]
    rw [show ((0 : ℝ) - 1 / 2) * arccos (7 / 10) = -(arccos (7 / 10) / 2) by ring,
      show ((1 : ℝ) - 1 / 2) * arccos (7 / 10) = arccos (7 / 10) / 2 by ring, Real.cos_neg,
      ← sq, hc, Real.sq_sqrt (by norm_num), show (1 : ℝ) / (1 + 1) = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow]
  · rw [Ne, Real.sqrt_inj (by norm_num) (by norm_num)]; norm_num
  · exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

/-- `k = 2`: `exp (W/3) = 0.49^(1/3) ≈ 0.788`. -/
theorem num_k2 :
    ((2 : ℕ) : ℝ) * arccos (7 / 10 : ℝ) < π ∧
    bound (arccos (7 / 10)) 2 = Real.log (49 / 100) ∧
    Real.exp (bound (arccos (7 / 10)) 2 / ((2 : ℕ) + 1)) = (49 / 100 : ℝ) ^ ((1 : ℝ) / 3) ∧
    (0.788 : ℝ) < (49 / 100 : ℝ) ^ ((1 : ℝ) / 3) ∧ (49 / 100 : ℝ) ^ ((1 : ℝ) / 3) < 0.789 := by
  have hk : ((2 : ℕ) : ℝ) * arccos (7 / 10 : ℝ) < π := by
    have := theta_lt_pi_div_three; push_cast; linarith [pi_pos]
  have hprod : ∏ i : Fin (2 + 1), Real.cos ((((i : ℕ) : ℝ) - ((2 : ℕ) : ℝ) / 2) *
      arccos (7 / 10)) = 49 / 100 := by
    rw [Fin.prod_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat]
    rw [show ((0 : ℝ) - 2 / 2) * arccos (7 / 10) = -arccos (7 / 10) by ring,
      show ((1 : ℝ) - 2 / 2) * arccos (7 / 10) = 0 by ring,
      show ((2 : ℝ) - 2 / 2) * arccos (7 / 10) = arccos (7 / 10) by ring, Real.cos_neg,
      Real.cos_zero, cos_arccos (by norm_num) (by norm_num)]
    norm_num
  have hy : 0 < (49 / 100 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
  have hy3 : ((49 / 100 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 49 / 100 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  refine ⟨hk, by rw [bound_eq_log_prod (arccos_nonneg _) hk, hprod], ?_, ?_, ?_⟩
  · rw [exp_bound_eq (arccos_nonneg _) hk, hprod]; norm_num
  · by_contra h; push Not at h
    have := pow_le_pow_left₀ hy.le h 3
    rw [hy3] at this; norm_num at this
  · by_contra h; push Not at h
    have := pow_le_pow_left₀ (by norm_num) h 3
    rw [hy3] at this; norm_num at this

/-- `k = 3`: `W = log (0.85 * 0.136) ≈ -2.158` and `exp (W/4) = (0.85 * 0.136)^(1/4) ≈ 0.583`. -/
theorem num_k3 :
    ((3 : ℕ) : ℝ) * arccos (7 / 10 : ℝ) < π ∧
    (289 / 2500 : ℝ) = 0.85 * 0.136 ∧
    bound (arccos (7 / 10)) 3 = Real.log (289 / 2500) ∧
    Real.exp (bound (arccos (7 / 10)) 3 / ((3 : ℕ) + 1)) = (289 / 2500 : ℝ) ^ ((1 : ℝ) / 4) ∧
    (0.583 : ℝ) < (289 / 2500 : ℝ) ^ ((1 : ℝ) / 4) ∧
    (289 / 2500 : ℝ) ^ ((1 : ℝ) / 4) < 0.584 ∧
    (-2.16 : ℝ) < bound (arccos (7 / 10)) 3 ∧ bound (arccos (7 / 10)) 3 < -2.15 := by
  have hk : ((3 : ℕ) : ℝ) * arccos (7 / 10 : ℝ) < π := by
    have := theta_lt_pi_div_three; push_cast; linarith [pi_pos]
  have hc := cos_half_seven
  have hc2 : Real.cos (arccos (7 / 10 : ℝ) / 2) ^ 2 = 17 / 20 := by
    rw [hc, Real.sq_sqrt (by norm_num)]
  have hprod : ∏ i : Fin (3 + 1), Real.cos ((((i : ℕ) : ℝ) - ((3 : ℕ) : ℝ) / 2) *
      arccos (7 / 10)) = 289 / 2500 := by
    rw [Fin.prod_univ_four]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat]
    have e3 : ((3 : Fin (3 + 1)) : ℕ) = 3 := rfl
    rw [e3]
    push_cast
    rw [show ((0 : ℝ) - 3 / 2) * arccos (7 / 10) = -(3 * (arccos (7 / 10) / 2)) by ring,
      show ((1 : ℝ) - 3 / 2) * arccos (7 / 10) = -(arccos (7 / 10) / 2) by ring,
      show ((2 : ℝ) - 3 / 2) * arccos (7 / 10) = arccos (7 / 10) / 2 by ring,
      show ((3 : ℝ) - 3 / 2) * arccos (7 / 10) = 3 * (arccos (7 / 10) / 2) by ring,
      Real.cos_neg, Real.cos_neg, Real.cos_three_mul]
    generalize Real.cos (arccos (7 / 10 : ℝ) / 2) = c at hc2 ⊢
    have : (4 * c ^ 3 - 3 * c) * c * c * (4 * c ^ 3 - 3 * c)
        = (c ^ 2) ^ 2 * (4 * c ^ 2 - 3) ^ 2 := by ring
    rw [this, hc2]; norm_num
  have hy : 0 < (289 / 2500 : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hy4 : ((289 / 2500 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 289 / 2500 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hW : bound (arccos (7 / 10)) 3 = Real.log (289 / 2500) := by
    rw [bound_eq_log_prod (arccos_nonneg _) hk, hprod]
  have e1 : Real.log (289 / 2500) = -(3 * Real.log 2 + Real.log (2500 / 2312)) := by
    rw [show (289 / 2500 : ℝ) = ((2 : ℝ) ^ 3 * (2500 / 2312))⁻¹ by norm_num, Real.log_inv,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have e2 : Real.log (2500 / 2312) = Real.log (26 / 25) + Real.log (62500 / 60112) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l1 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2500 / 2312)
  have u1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 26 / 25)
  have u2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 62500 / 60112)
  have t1 := Real.log_two_gt_d9
  have t2 := Real.log_two_lt_d9
  norm_num at l1 u1 u2 t1 t2
  refine ⟨hk, by norm_num, hW, ?_, ?_, ?_, ?_, ?_⟩
  · rw [exp_bound_eq (arccos_nonneg _) hk, hprod]; norm_num
  · by_contra h; push Not at h
    have := pow_le_pow_left₀ hy.le h 4
    rw [hy4] at this; norm_num at this
  · by_contra h; push Not at h
    have := pow_le_pow_left₀ (by norm_num) h 4
    rw [hy4] at this; norm_num at this
  · rw [hW, e1, e2]; linarith
  · rw [hW, e1]; linarith

/-- `k = 4`: `π < 4 θ`, and the planar r-chain at `r = 7/10` admits no bargain. -/
theorem num_k4 (d : ℕ) (hd : 2 ≤ d) :
    π < ((4 : ℕ) : ℝ) * arccos (7 / 10 : ℝ) ∧
    IsRChain (7 / 10) (planarRd d hd (arccos (7 / 10)) 4) ∧
    ∀ x, ¬ ∀ i, 0 < ⟪planarRd d hd (arccos (7 / 10)) 4 i, x⟫ := by
  have h4 : π < ((4 : ℕ) : ℝ) * arccos (7 / 10 : ℝ) := by
    have := pi_div_four_lt_theta; push_cast; linarith
  exact ⟨h4, planar_isRChain (norm_eA d hd) (norm_eB d hd) (inner_eA_eB d hd)
    (by norm_num) (by norm_num) 4,
    fun x => planar_infeasible (Real.arccos_lt_pi.2 (by norm_num)) h4.le x⟩

end Numbers

end Bridge6B
