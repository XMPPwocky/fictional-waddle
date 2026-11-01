import Mathlib

/-!
# Bridge6A: Nash bargaining along an r-chain of selves

Setting.  `r ∈ (-1,1)`, `θ = arccos r`, `k ≥ 1`, ambient space `ℝ^d`
(`EuclideanSpace ℝ (Fin d)`).  An r-chain is `v : Fin (k+1) → ℝ^d` with every `v i` on the
unit sphere and `r ≤ ⟪v i, v (i+1)⟫` (`IsRChain`).  Utilities are `u_i(x) = ⟪v i, x⟫`
(`util v`), disagreement point `0`; a point is feasible when every utility is positive
(`Feasible`), and its Nash welfare is `∑ log u_i(x)` (`nash`).  `bestWelfare v` is the
supremum of the Nash welfare over feasible points of the unit sphere.  The planar chain
`planarChain n k θ i = (cos iθ, sin iθ, 0, …, 0)` lives in `ℝ^(n+2)` (this encodes `d ≥ 2`).
`worstBound k θ = ∑_{i=0}^{k} log cos((i - k/2) θ)`.

PROVED
* `chain_angle_le` : along an r-chain, `angle (v a) (v b) ≤ |a - b| · arccos r`.
* (i) `feasible_of_lt_pi` : if `k θ < π`, every r-chain has a feasible point on the sphere.
  `planar_not_feasible` : if `-1 < r < 1` and `π ≤ k θ`, the planar chain has no feasible
  point at all (on or off the sphere).  `planar_isRChain` : the planar chain is an r-chain.
* (ii) `exists_ge_worstBound` : if `k θ < π`, every r-chain has a feasible unit `x` with
  `worstBound k θ ≤ ∑ log ⟪v i, x⟫`, and `worstBound_le_bestWelfare` gives the same for the
  supremum.  `planar_bisector` : the bisector `planarVec (kθ/2)` is feasible with Nash welfare
  exactly `worstBound k θ`; `planar_nash_le` : no feasible unit `x` does better for the planar
  chain; hence `bestWelfare_planar` : `bestWelfare (planar chain) = worstBound k θ`, and
  `worst_case_exact` : `worstBound k θ` is the least value of `bestWelfare` over all r-chains in
  `ℝ^(n+2)`.
* (iii) `rescale` : for utilities on any type, `u_i ↦ c_i u_i` with `c_i > 0` preserves
  feasibility, shifts every feasible Nash value by `∑ log c_i`, and preserves the set of
  maximizers over any constraint set.
* Numbers at `r = 7/10` (`θ7 = arccos (7/10)`):
  `num_k1` : `cos(θ7/2) = √(17/20)`, `exp(W₁/2) = √(17/20)`, `0.921 < √(17/20) < 0.922`,
  and `√(17/20) ≠ √(1 - 0.49)`;
  `num_k2` : `exp(W₂/3) = 0.49^(1/3)` and `0.788 < 0.49^(1/3) < 0.789`;
  `num_k3` : `3θ7 < π`, `W₃ = log (0.85 · 0.136)`, `exp(W₃/4) = (0.85 · 0.136)^(1/4)`,
  `0.583 < (0.85 · 0.136)^(1/4) < 0.584`, and `-2.161 < W₃ < -2.154`;
  `num_k4` : `π < 4 θ7`, so the planar 7/10-chain with `k = 4` (an r-chain) has no feasible point.

INTERPRETED
* "v : Fin (k+1) → unit sphere" is encoded as vectors with `v i ∈ Metric.sphere 0 1`;
  "`v (i+1)`" ranges over `i : Fin k` via `castSucc`/`succ`.
* "sup_x ∑ log ⟪v i, x⟫" is the supremum over the feasible part of the unit sphere (where all
  utilities are positive, the only region where the Nash product is meaningful); the
  existential form is also proved.  Statement (i)/(ii) for general chains holds for every
  `k` and `r` with `k · arccos r < π`; the extra hypotheses `-1 < r < 1`, `k ≥ 1`, `d ≥ 2` are
  not needed there.  `d ≥ 2` is used only for the planar chain, as `d = n + 2`.
* The approximations `W ≈ -2.158` and `4θ ≈ 182.3°` are certified only as the bracket
  `-2.161 < W₃ < -2.154` and the inequality `π < 4θ`, respectively.
-/

namespace Bridge6A

open Real InnerProductGeometry Finset
open scoped RealInnerProductSpace

noncomputable section

/-- Nash welfare `∑ log u_i(x)` with disagreement point `0`. -/
def nash {X : Type*} {m : ℕ} (u : Fin m → X → ℝ) (x : X) : ℝ := ∑ i, Real.log (u i x)

/-- Every utility is strictly above the disagreement value `0`. -/
def Feasible {X : Type*} {m : ℕ} (u : Fin m → X → ℝ) (x : X) : Prop := ∀ i, 0 < u i x

/-- Linear utilities `u_i(x) = ⟪v i, x⟫`. -/
def util {d m : ℕ} (v : Fin m → EuclideanSpace ℝ (Fin d)) :
    Fin m → EuclideanSpace ℝ (Fin d) → ℝ :=
  fun i x => ⟪v i, x⟫

/-- An r-chain of unit vectors. -/
def IsRChain {d k : ℕ} (r : ℝ) (v : Fin (k + 1) → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ i, v i ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) ∧
    ∀ i : Fin k, r ≤ ⟪v i.castSucc, v i.succ⟫

/-- The unit vector `(cos t, sin t, 0, …, 0)`. -/
def planarVec {n : ℕ} (t : ℝ) : EuclideanSpace ℝ (Fin (n + 2)) :=
  EuclideanSpace.single 0 (cos t) + EuclideanSpace.single 1 (sin t)

/-- The planar equally spaced chain `v i = (cos iθ, sin iθ, 0, …)`. -/
def planarChain (n k : ℕ) (θ : ℝ) : Fin (k + 1) → EuclideanSpace ℝ (Fin (n + 2)) :=
  fun i => planarVec (((i : ℕ) : ℝ) * θ)

/-- `∑_{i=0}^{k} log cos((i - k/2) θ)`. -/
def worstBound (k : ℕ) (θ : ℝ) : ℝ :=
  ∑ i : Fin (k + 1), Real.log (cos ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ))

/-- Supremum of the Nash welfare over feasible points of the unit sphere. -/
def bestWelfare {d m : ℕ} (v : Fin m → EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup (nash (util v) '' {x | x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ∧
    Feasible (util v) x})

/-! ## Planar vectors -/

lemma planarVec_apply_zero {n : ℕ} (t : ℝ) : (planarVec (n := n) t) 0 = cos t := by
  simp [planarVec]

lemma planarVec_apply_one {n : ℕ} (t : ℝ) : (planarVec (n := n) t) 1 = sin t := by
  simp [planarVec]

lemma inner_planarVec {n : ℕ} (t : ℝ) (x : EuclideanSpace ℝ (Fin (n + 2))) :
    ⟪planarVec t, x⟫ = cos t * x 0 + sin t * x 1 := by
  simp [planarVec, inner_add_left, EuclideanSpace.inner_single_left]

lemma inner_planarVec_planarVec {n : ℕ} (s t : ℝ) :
    ⟪(planarVec (n := n) s), planarVec t⟫ = cos (s - t) := by
  rw [inner_planarVec, planarVec_apply_zero, planarVec_apply_one, cos_sub]

lemma norm_planarVec {n : ℕ} (t : ℝ) : ‖planarVec (n := n) t‖ = 1 := by
  have h : ‖planarVec (n := n) t‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_planarVec_planarVec, sub_self, cos_zero]
  have h0 := norm_nonneg (planarVec (n := n) t)
  nlinarith

/-! ## Angles along a chain -/

lemma angle_le_arccos {d : ℕ} {u w : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    {r : ℝ} (h : r ≤ ⟪u, w⟫) : angle u w ≤ arccos r := by
  unfold InnerProductGeometry.angle
  rw [hu, hw, mul_one, div_one]
  exact arccos_le_arccos h

lemma IsRChain.norm {d k : ℕ} {r : ℝ} {v : Fin (k + 1) → EuclideanSpace ℝ (Fin d)}
    (hv : IsRChain r v) (i : Fin (k + 1)) : ‖v i‖ = 1 :=
  mem_sphere_zero_iff_norm.1 (hv.1 i)

lemma chain_angle_aux {d k : ℕ} {r : ℝ} {v : Fin (k + 1) → EuclideanSpace ℝ (Fin d)}
    (hv : IsRChain r v) :
    ∀ m i (h : i + m ≤ k),
      angle (v ⟨i, by omega⟩) (v ⟨i + m, by omega⟩) ≤ (m : ℝ) * arccos r := by
  intro m
  induction m with
  | zero =>
    intro i h
    have hne : v ⟨i, by omega⟩ ≠ 0 := by
      intro h0; have := hv.norm ⟨i, by omega⟩; rw [h0, norm_zero] at this; norm_num at this
    simp [angle_self hne]
  | succ m ih =>
    intro i h
    have h1 := ih i (by omega)
    have e := hv.2 ⟨i + m, by omega⟩
    have hc : (⟨i + m, by omega⟩ : Fin k).castSucc = ⟨i + m, by omega⟩ := rfl
    have hs : (⟨i + m, by omega⟩ : Fin k).succ = ⟨i + (m + 1), by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [hc, hs] at e
    have h2 := angle_le_arccos (hv.norm _) (hv.norm _) e
    calc angle (v ⟨i, by omega⟩) (v ⟨i + (m + 1), by omega⟩)
        ≤ angle (v ⟨i, by omega⟩) (v ⟨i + m, by omega⟩)
          + angle (v ⟨i + m, by omega⟩) (v ⟨i + (m + 1), by omega⟩) :=
          angle_le_angle_add_angle _ _ _
      _ ≤ (m : ℝ) * arccos r + arccos r := add_le_add h1 h2
      _ = ((m + 1 : ℕ) : ℝ) * arccos r := by push_cast; ring

/-- Along an r-chain, `angle (v a) (v b) ≤ |a - b| · arccos r`. -/
theorem chain_angle_le {d k : ℕ} {r : ℝ} {v : Fin (k + 1) → EuclideanSpace ℝ (Fin d)}
    (hv : IsRChain r v) (a b : Fin (k + 1)) :
    angle (v a) (v b) ≤ |((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)| * arccos r := by
  rcases le_total (a : ℕ) (b : ℕ) with hab | hab
  · have h := chain_angle_aux hv ((b : ℕ) - a) a (by omega)
    have ea : (⟨(a : ℕ), by omega⟩ : Fin (k + 1)) = a := Fin.ext rfl
    have eb : (⟨(a : ℕ) + ((b : ℕ) - a), by omega⟩ : Fin (k + 1)) = b := Fin.ext (by simp; omega)
    rw [ea, eb] at h
    have hab' : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
    rw [abs_of_nonpos (by linarith)]
    calc _ ≤ _ := h
      _ = _ := by rw [Nat.cast_sub hab]; ring
  · have h := chain_angle_aux hv ((a : ℕ) - b) b (by omega)
    have eb : (⟨(b : ℕ), by omega⟩ : Fin (k + 1)) = b := Fin.ext rfl
    have ea : (⟨(b : ℕ) + ((a : ℕ) - b), by omega⟩ : Fin (k + 1)) = a := Fin.ext (by simp; omega)
    rw [ea, eb] at h
    have hab' : ((b : ℕ) : ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast hab
    rw [angle_comm, abs_of_nonneg (by linarith)]
    calc _ ≤ _ := h
      _ = _ := by rw [Nat.cast_sub hab]

/-- Half-angle bound for the midpoint direction of two unit vectors. -/
lemma angle_add_le_half {d : ℕ} {u w : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hs : u + w ≠ 0) : angle u (u + w) ≤ angle u w / 2 := by
  have hφ0 := angle_nonneg u w
  have hφπ := angle_le_pi u w
  have hc : ⟪u, w⟫ = cos (angle u w) := by
    rw [← cos_angle_mul_norm_mul_norm, hu, hw]; ring
  have hss : ‖u + w‖ ^ 2 = 2 * (1 + cos (angle u w)) := by
    rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu, hw, real_inner_comm u w, hc]
    ring
  have hn : 0 < ‖u + w‖ := norm_pos_iff.2 hs
  have ht : 0 < 1 + cos (angle u w) := by nlinarith
  have hin : ⟪u, u + w⟫ = 1 + cos (angle u w) := by
    rw [inner_add_right, real_inner_self_eq_norm_sq, hu, hc]; ring
  have hhalf : cos (angle u w / 2) = √((1 + cos (angle u w)) / 2) :=
    cos_half (by linarith [pi_pos]) hφπ
  have hval : angle u (u + w) = arccos ((1 + cos (angle u w)) / ‖u + w‖) := by
    rw [InnerProductGeometry.angle, hu, one_mul, hin]
  rw [hval]
  calc arccos ((1 + cos (angle u w)) / ‖u + w‖) ≤ arccos (cos (angle u w / 2)) := by
        apply arccos_le_arccos
        rw [hhalf, Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        rw [div_pow, hss]
        apply le_of_eq
        field_simp
    _ = angle u w / 2 := arccos_cos (by linarith) (by linarith [pi_pos])

/-! ## (ii) General chains: the midpoint of the middle edge -/

lemma abs_mid_le {k : ℕ} (i : Fin (k + 1)) :
    |((i : ℕ) : ℝ) - (k : ℝ) / 2| ≤ (k : ℝ) / 2 := by
  have h1 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : ((i : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 i.isLt
  rw [abs_le]; constructor <;> linarith

lemma cos_mid_pos {k : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (hk : (k : ℝ) * θ < π) (i : Fin (k + 1)) :
    0 < cos ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ) := by
  have h := abs_mid_le i
  have hb : |(((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ| < π / 2 := by
    rw [abs_mul, abs_of_nonneg hθ]
    calc _ ≤ (k : ℝ) / 2 * θ := mul_le_mul_of_nonneg_right h hθ
      _ < π / 2 := by linarith
  rw [abs_lt] at hb
  exact cos_pos_of_mem_Ioo ⟨by linarith [hb.1], hb.2⟩

/-- (ii) Every r-chain with `k θ < π` admits a feasible unit point whose Nash welfare is at least
`∑ log cos((i - k/2) θ)`; the point is the normalized midpoint of the middle edge. -/
theorem exists_ge_worstBound {d k : ℕ} {r : ℝ} {v : Fin (k + 1) → EuclideanSpace ℝ (Fin d)}
    (hv : IsRChain r v) (hk : (k : ℝ) * arccos r < π) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      Feasible (util v) x ∧ worstBound k (arccos r) ≤ nash (util v) x := by
  set θ := arccos r with hθdef
  have hθ0 : 0 ≤ θ := arccos_nonneg r
  obtain ⟨p, hp⟩ : ∃ p, p = k / 2 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = k - k / 2 := ⟨_, rfl⟩
  have hpq : p ≤ q := by omega
  have hsum : (p : ℝ) + q = k := by
    have : p + q = k := by omega
    exact_mod_cast this
  have hpk : p < k + 1 := by omega
  have hqk : q < k + 1 := by omega
  have hPn : ‖v ⟨p, hpk⟩‖ = 1 := hv.norm _
  have hQn : ‖v ⟨q, hqk⟩‖ = 1 := hv.norm _
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hPQ : angle (v ⟨p, hpk⟩) (v ⟨q, hqk⟩) ≤ ((q : ℝ) - p) * θ := by
    have h := chain_angle_le hv ⟨p, hpk⟩ ⟨q, hqk⟩
    simp only at h
    rwa [abs_sub_comm, abs_of_nonneg (by linarith)] at h
  have hqmp : ((q : ℝ) - p) * θ < π := by
    have : ((q : ℝ) - p) ≤ k := by
      have : (q : ℝ) ≤ k := by exact_mod_cast (show q ≤ k by omega)
      have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      linarith
    calc _ ≤ (k : ℝ) * θ := mul_le_mul_of_nonneg_right this hθ0
      _ < π := hk
  have hs : v ⟨p, hpk⟩ + v ⟨q, hqk⟩ ≠ 0 := by
    intro h
    have hQ : v ⟨q, hqk⟩ = -v ⟨p, hpk⟩ := eq_neg_of_add_eq_zero_right h
    have hP0 : v ⟨p, hpk⟩ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hPn; norm_num at hPn
    have h2 := angle_self_neg_of_nonzero hP0
    rw [← hQ] at h2
    linarith
  have hsn : 0 < ‖v ⟨p, hpk⟩ + v ⟨q, hqk⟩‖ := norm_pos_iff.2 hs
  set s := v ⟨p, hpk⟩ + v ⟨q, hqk⟩ with hsdef
  set x := ‖s‖⁻¹ • s with hxdef
  have hxn : ‖x‖ = 1 := by
    rw [hxdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hsn.ne']
  have hang : ∀ y, angle y x = angle y s := fun y =>
    angle_smul_right_of_pos y s (inv_pos.2 hsn)
  have hPs : angle (v ⟨p, hpk⟩) s ≤ ((q : ℝ) - p) * θ / 2 := by
    have := angle_add_le_half hPn hQn hs; linarith
  have hQs : angle (v ⟨q, hqk⟩) s ≤ ((q : ℝ) - p) * θ / 2 := by
    have h := angle_add_le_half hQn hPn (by rw [add_comm]; exact hs)
    rw [add_comm (v ⟨q, hqk⟩) (v ⟨p, hpk⟩), angle_comm (v ⟨q, hqk⟩) (v ⟨p, hpk⟩)] at h
    linarith
  have key : ∀ i : Fin (k + 1), angle (v i) x ≤ |((i : ℕ) : ℝ) - (k : ℝ) / 2| * θ := by
    intro i
    rw [hang]
    by_cases hi : (i : ℕ) ≤ p
    · have h1 := chain_angle_le hv i ⟨p, hpk⟩
      simp only at h1
      have hi' : ((i : ℕ) : ℝ) ≤ p := by exact_mod_cast hi
      have h2 : (2 : ℝ) * p ≤ k := by exact_mod_cast (show 2 * p ≤ k by omega)
      rw [abs_of_nonpos (by linarith)] at h1
      rw [abs_of_nonpos (by linarith)]
      calc angle (v i) s ≤ angle (v i) (v ⟨p, hpk⟩) + angle (v ⟨p, hpk⟩) s :=
            angle_le_angle_add_angle _ _ _
        _ ≤ -(((i : ℕ) : ℝ) - p) * θ + ((q : ℝ) - p) * θ / 2 := add_le_add h1 hPs
        _ = -(((i : ℕ) : ℝ) - k / 2) * θ := by rw [← hsum]; ring
    · have hi' : (q : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast (show q ≤ (i : ℕ) by omega)
      have h1 := chain_angle_le hv i ⟨q, hqk⟩
      simp only at h1
      have h2 : (k : ℝ) ≤ 2 * q := by exact_mod_cast (show k ≤ 2 * q by omega)
      rw [abs_of_nonneg (by linarith)] at h1
      rw [abs_of_nonneg (by linarith)]
      calc angle (v i) s ≤ angle (v i) (v ⟨q, hqk⟩) + angle (v ⟨q, hqk⟩) s :=
            angle_le_angle_add_angle _ _ _
        _ ≤ (((i : ℕ) : ℝ) - q) * θ + ((q : ℝ) - p) * θ / 2 := add_le_add h1 hQs
        _ = (((i : ℕ) : ℝ) - k / 2) * θ := by rw [← hsum]; ring
  have hinner : ∀ i, ⟪v i, x⟫ = cos (angle (v i) x) := by
    intro i; rw [← cos_angle_mul_norm_mul_norm, hv.norm i, hxn]; ring
  have hlow : ∀ i : Fin (k + 1), cos ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ) ≤ ⟪v i, x⟫ := by
    intro i
    rw [hinner]
    have hb : |((i : ℕ) : ℝ) - (k : ℝ) / 2| * θ ≤ π := by
      have := mul_le_mul_of_nonneg_right (abs_mid_le i) hθ0
      linarith [pi_pos]
    have h := cos_le_cos_of_nonneg_of_le_pi (angle_nonneg _ _) hb (key i)
    have e : |((i : ℕ) : ℝ) - (k : ℝ) / 2| * θ = |(((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ| := by
      rw [abs_mul, abs_of_nonneg hθ0]
    rwa [e, cos_abs] at h
  refine ⟨x, mem_sphere_zero_iff_norm.2 hxn,
    fun i => lt_of_lt_of_le (cos_mid_pos hθ0 hk i) (hlow i), ?_⟩
  exact Finset.sum_le_sum fun i _ => Real.log_le_log (cos_mid_pos hθ0 hk i) (hlow i)

/-- (i), first half: if `k θ < π`, every r-chain has a point of the sphere at which every
utility is positive. -/
theorem feasible_of_lt_pi {d k : ℕ} {r : ℝ} {v : Fin (k + 1) → EuclideanSpace ℝ (Fin d)}
    (hv : IsRChain r v) (hk : (k : ℝ) * arccos r < π) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1, Feasible (util v) x := by
  obtain ⟨x, hx, hf, _⟩ := exists_ge_worstBound hv hk
  exact ⟨x, hx, hf⟩

/-! ## The planar chain -/

/-- The planar equally spaced chain is an r-chain. -/
theorem planar_isRChain {n k : ℕ} {r : ℝ} (hr1 : -1 ≤ r) (hr2 : r ≤ 1) :
    IsRChain r (planarChain n k (arccos r)) := by
  refine ⟨fun i => mem_sphere_zero_iff_norm.2 (norm_planarVec _), fun i => ?_⟩
  simp only [planarChain, inner_planarVec_planarVec, Fin.val_castSucc, Fin.val_succ]
  push_cast
  rw [show ((i : ℕ) : ℝ) * arccos r - (((i : ℕ) : ℝ) + 1) * arccos r = -arccos r by ring,
    cos_neg, cos_arccos hr1 hr2]

/-- (i), second half: if `-1 < r < 1` and `π ≤ k θ`, the planar chain has no point at all
(on or off the sphere) at which every utility is positive. -/
theorem planar_not_feasible {n k : ℕ} {r : ℝ} (hr1 : -1 < r) (hr2 : r < 1)
    (hk : π ≤ (k : ℝ) * arccos r) :
    ¬ ∃ x : EuclideanSpace ℝ (Fin (n + 2)), Feasible (util (planarChain n k (arccos r))) x := by
  set θ := arccos r with hθdef
  have hθ0 : 0 < θ := arccos_pos.2 hr2
  have hθπ : θ < π := arccos_lt_pi.2 hr1
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hk; simp at hk; linarith [pi_pos]
    · exact h
  have hkc : (((k - 1 : ℕ) : ℝ) + 1) = k := by rw [Nat.cast_sub hk1]; simp
  have hex : ∃ m : ℕ, π ≤ ((m : ℝ) + 1) * θ := ⟨k - 1, by rw [hkc]; exact hk⟩
  classical
  obtain ⟨j, hjdef⟩ : ∃ j, j = Nat.find hex := ⟨_, rfl⟩
  have hj : π ≤ ((j : ℝ) + 1) * θ := by rw [hjdef]; exact Nat.find_spec hex
  have hjk : j ≤ k - 1 := by rw [hjdef]; exact Nat.find_min' hex (by rw [hkc]; exact hk)
  have hα : (j : ℝ) * θ < π := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0]; simp; exact pi_pos
    · have := Nat.find_min hex (show j - 1 < Nat.find hex by omega)
      push Not at this
      rwa [Nat.cast_sub h0, Nat.cast_one, sub_add_cancel] at this
  rintro ⟨x, hx⟩
  have h0 := hx 0
  have hja := hx ⟨j, by omega⟩
  have hjb := hx ⟨j + 1, by omega⟩
  simp only [util, planarChain, inner_planarVec, Fin.val_zero] at h0 hja hjb
  simp only [Nat.cast_zero, zero_mul, cos_zero, sin_zero, one_mul, zero_mul, add_zero] at h0
  push_cast at hjb
  have hβ : ((j : ℝ) + 1) * θ = (j : ℝ) * θ + θ := by ring
  rw [hβ] at hjb hj
  have hsθ : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hsα : 0 ≤ sin ((j : ℝ) * θ) :=
    sin_nonneg_of_nonneg_of_le_pi (by positivity) hα.le
  have hsβ : sin ((j : ℝ) * θ + θ) ≤ 0 := by
    have : 0 ≤ sin ((j : ℝ) * θ + θ - π) :=
      sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [sin_sub_pi] at this; linarith
  have iden : sin θ * x 0 + (-sin ((j : ℝ) * θ + θ)) *
      (cos ((j : ℝ) * θ) * x 0 + sin ((j : ℝ) * θ) * x 1)
      + sin ((j : ℝ) * θ) * (cos ((j : ℝ) * θ + θ) * x 0 + sin ((j : ℝ) * θ + θ) * x 1) = 0 := by
    rw [sin_add, cos_add]
    linear_combination (-(x 0 * sin θ)) * (sin_sq_add_cos_sq ((j : ℝ) * θ))
  nlinarith [mul_pos hsθ h0, mul_nonneg (neg_nonneg.2 hsβ) hja.le, mul_nonneg hsα hjb.le]

/-- The bisector `planarVec (kθ/2)` is a feasible unit point for the planar chain, with Nash
welfare exactly `worstBound k θ`. -/
theorem planar_bisector {n k : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (hk : (k : ℝ) * θ < π) :
    planarVec (n := n) ((k : ℝ) * θ / 2) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 ∧
    Feasible (util (planarChain n k θ)) (planarVec ((k : ℝ) * θ / 2)) ∧
    nash (util (planarChain n k θ)) (planarVec ((k : ℝ) * θ / 2)) = worstBound k θ := by
  have e : ∀ i : Fin (k + 1), util (planarChain n k θ) i (planarVec ((k : ℝ) * θ / 2))
      = cos ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ) := by
    intro i; simp only [util, planarChain, inner_planarVec_planarVec]; congr 1; ring
  refine ⟨mem_sphere_zero_iff_norm.2 (norm_planarVec _),
    fun i => by rw [e]; exact cos_mid_pos hθ hk i, ?_⟩
  exact Finset.sum_congr rfl fun i _ => by rw [e]

lemma pair_bound (a b A B : ℝ) :
    (a * cos A + b * sin A) * (a * cos B + b * sin B)
      ≤ (a ^ 2 + b ^ 2) * (1 + cos (A - B)) / 2 := by
  have h2 : 2 * (a ^ 2 * (1 - cos (A + B)) + b ^ 2 * (1 + cos (A + B))
      - 2 * a * b * sin (A + B))
      = (a * (1 - cos (A + B)) - b * sin (A + B)) ^ 2
        + (a * sin (A + B) - b * (1 + cos (A + B))) ^ 2 := by
    linear_combination (-(a ^ 2 + b ^ 2)) * (sin_sq_add_cos_sq (A + B))
  have hQ : 0 ≤ a ^ 2 * (1 - cos (A + B)) + b ^ 2 * (1 + cos (A + B))
      - 2 * a * b * sin (A + B) := by
    nlinarith [sq_nonneg (a * (1 - cos (A + B)) - b * sin (A + B)),
      sq_nonneg (a * sin (A + B) - b * (1 + cos (A + B)))]
  rw [cos_add, sin_add] at hQ
  rw [cos_sub]
  nlinarith [hQ]

/-- No feasible unit point beats the bisector for the planar chain. -/
theorem planar_nash_le {n k : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (hk : (k : ℝ) * θ < π)
    (x : EuclideanSpace ℝ (Fin (n + 2)))
    (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
    (hf : Feasible (util (planarChain n k θ)) x) :
    nash (util (planarChain n k θ)) x ≤ worstBound k θ := by
  set f : Fin (k + 1) → ℝ := fun i => util (planarChain n k θ) i x with hfdef
  set g : Fin (k + 1) → ℝ := fun i => cos ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ) with hgdef
  have hfpos : ∀ i, 0 < f i := hf
  have hgpos : ∀ i, 0 < g i := cos_mid_pos hθ hk
  have hab : x 0 ^ 2 + x 1 ^ 2 ≤ 1 := by
    have h := EuclideanSpace.real_norm_sq_eq x
    rw [mem_sphere_zero_iff_norm.1 hx, Fin.sum_univ_succ, Fin.sum_univ_succ] at h
    have : 0 ≤ ∑ i : Fin n, x i.succ.succ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    simp only [Fin.succ_zero_eq_one] at h
    nlinarith
  have hfi : ∀ i : Fin (k + 1),
      f i = x 0 * cos (((i : ℕ) : ℝ) * θ) + x 1 * sin (((i : ℕ) : ℝ) * θ) := by
    intro i; simp only [hfdef, util, planarChain, inner_planarVec]; ring
  have hpair : ∀ i : Fin (k + 1), f i * f (Fin.rev i) ≤ g i ^ 2 := by
    intro i
    have hrev : (((Fin.rev i : Fin (k + 1)) : ℕ) : ℝ) = (k : ℝ) - ((i : ℕ) : ℝ) := by
      rw [Fin.val_rev]
      have hi := i.isLt
      have : (k + 1) - ((i : ℕ) + 1) = k - (i : ℕ) := by omega
      rw [this, Nat.cast_sub (by omega)]
    rw [hfi, hfi, hrev]
    have h1 := pair_bound (x 0) (x 1) (((i : ℕ) : ℝ) * θ) (((k : ℝ) - ((i : ℕ) : ℝ)) * θ)
    have h2 : cos (((i : ℕ) : ℝ) * θ - ((k : ℝ) - ((i : ℕ) : ℝ)) * θ)
        = cos (2 * ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ)) := by congr 1; ring
    rw [h2] at h1
    have h3 : g i ^ 2 = 1 / 2 + cos (2 * ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ)) / 2 := cos_sq _
    have h4 := neg_one_le_cos (2 * ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ))
    rw [h3]
    nlinarith [mul_nonneg (sub_nonneg.2 hab)
      (show 0 ≤ 1 + cos (2 * ((((i : ℕ) : ℝ) - (k : ℝ) / 2) * θ)) by linarith)]
  have hsq : (∏ i, f i) ^ 2 ≤ (∏ i, g i) ^ 2 := by
    have e1 : (∏ i, f i) ^ 2 = ∏ i, (f i * f (Fin.rev i)) := by
      rw [sq, Finset.prod_mul_distrib]
      congr 1
      exact (Equiv.prod_comp Fin.revPerm f).symm
    rw [e1, ← Finset.prod_pow]
    exact Finset.prod_le_prod₀ (fun i _ => (mul_pos (hfpos i) (hfpos _)).le) (fun i _ => hpair i)
  have hF : 0 < ∏ i, f i := Finset.prod_pos fun i _ => hfpos i
  have hG : 0 < ∏ i, g i := Finset.prod_pos fun i _ => hgpos i
  have hle : ∏ i, f i ≤ ∏ i, g i := by nlinarith
  have e2 : nash (util (planarChain n k θ)) x = Real.log (∏ i, f i) := by
    rw [Real.log_prod (fun i _ => (hfpos i).ne')]; rfl
  have e3 : worstBound k θ = Real.log (∏ i, g i) := by
    rw [Real.log_prod (fun i _ => (hgpos i).ne')]; rfl
  rw [e2, e3]
  exact Real.log_le_log hF hle

/-! ## Supremum form and exact worst case -/

lemma nash_le_zero {d m : ℕ} {v : Fin m → EuclideanSpace ℝ (Fin d)} (hv : ∀ i, ‖v i‖ = 1)
    {x : EuclideanSpace ℝ (Fin d)} (hx : ‖x‖ = 1) (hf : Feasible (util v) x) :
    nash (util v) x ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  apply Real.log_nonpos (hf i).le
  have := real_inner_le_norm (v i) x
  rw [hv i, hx, one_mul] at this
  exact this

lemma bddAbove_nash {d m : ℕ} {v : Fin m → EuclideanSpace ℝ (Fin d)} (hv : ∀ i, ‖v i‖ = 1) :
    BddAbove (nash (util v) '' {x | x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ∧
      Feasible (util v) x}) :=
  ⟨0, by
    rintro _ ⟨x, ⟨hx, hf⟩, rfl⟩
    exact nash_le_zero hv (mem_sphere_zero_iff_norm.1 hx) hf⟩

/-- (ii), supremum form: `worstBound k θ ≤ sup_x ∑ log ⟪v i, x⟫` for every r-chain. -/
theorem worstBound_le_bestWelfare {d k : ℕ} {r : ℝ}
    {v : Fin (k + 1) → EuclideanSpace ℝ (Fin d)}
    (hv : IsRChain r v) (hk : (k : ℝ) * arccos r < π) :
    worstBound k (arccos r) ≤ bestWelfare v := by
  obtain ⟨x, hx, hf, hle⟩ := exists_ge_worstBound hv hk
  exact hle.trans (le_csSup (bddAbove_nash hv.norm) ⟨x, ⟨hx, hf⟩, rfl⟩)

/-- (ii), equality case: the planar chain's supremum is exactly `worstBound k θ`. -/
theorem bestWelfare_planar {n k : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (hk : (k : ℝ) * θ < π) :
    bestWelfare (planarChain n k θ) = worstBound k θ := by
  obtain ⟨h1, h2, h3⟩ := planar_bisector (n := n) hθ hk
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · exact ⟨_, planarVec ((k : ℝ) * θ / 2), ⟨h1, h2⟩, rfl⟩
    rintro _ ⟨x, ⟨hx, hf⟩, rfl⟩
    exact planar_nash_le hθ hk x hx hf
  · rw [← h3]
    exact le_csSup (bddAbove_nash (fun i => norm_planarVec _)) ⟨_, ⟨h1, h2⟩, rfl⟩

/-- Exact worst case: over all r-chains in `ℝ^(n+2)`, the least attainable supremal Nash
welfare is `worstBound k (arccos r)`. -/
theorem worst_case_exact {n k : ℕ} {r : ℝ} (hr1 : -1 ≤ r) (hr2 : r ≤ 1)
    (hk : (k : ℝ) * arccos r < π) :
    IsLeast {w | ∃ v : Fin (k + 1) → EuclideanSpace ℝ (Fin (n + 2)),
      IsRChain r v ∧ w = bestWelfare v} (worstBound k (arccos r)) :=
  ⟨⟨planarChain n k (arccos r), planar_isRChain hr1 hr2,
      (bestWelfare_planar (arccos_nonneg r) hk).symm⟩,
    by rintro _ ⟨v, hv, rfl⟩; exact worstBound_le_bestWelfare hv hk⟩

/-! ## (iii) Rescaling utilities -/

/-- (iii) Rescaling `u_i ↦ c_i u_i` with `c_i > 0` preserves feasibility, shifts each feasible
Nash value by `∑ log c_i`, and preserves maximizers over any constraint set `S`. -/
theorem rescale {X : Type*} {m : ℕ} (u : Fin m → X → ℝ) (c : Fin m → ℝ) (hc : ∀ i, 0 < c i) :
    (∀ x, Feasible (fun i y => c i * u i y) x ↔ Feasible u x) ∧
    (∀ x, Feasible u x →
      nash (fun i y => c i * u i y) x = nash u x + ∑ i, Real.log (c i)) ∧
    (∀ (S : Set X) (x : X), Feasible u x →
      ((∀ y ∈ S, Feasible u y → nash u y ≤ nash u x) ↔
       (∀ y ∈ S, Feasible (fun i y => c i * u i y) y →
          nash (fun i y => c i * u i y) y ≤ nash (fun i y => c i * u i y) x))) := by
  have hF : ∀ x, Feasible (fun i y => c i * u i y) x ↔ Feasible u x := by
    intro x
    refine forall_congr' fun i => ⟨fun h => ?_, fun h => mul_pos (hc i) h⟩
    by_contra h'
    push Not at h'
    have : c i * u i x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hc i).le h'
    exact absurd h (not_lt.2 this)
  have hN : ∀ x, Feasible u x →
      nash (fun i y => c i * u i y) x = nash u x + ∑ i, Real.log (c i) := by
    intro x hx
    unfold nash
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Real.log_mul (hc i).ne' (hx i).ne']; ring
  refine ⟨hF, hN, fun S x hx => ⟨fun h y hy hfy => ?_, fun h y hy hfy => ?_⟩⟩
  · rw [hN y ((hF y).1 hfy), hN x hx]
    linarith [h y hy ((hF y).1 hfy)]
  · have := h y hy ((hF y).2 hfy)
    rw [hN y hfy, hN x hx] at this
    linarith

/-! ## Numbers at r = 7/10 -/

/-- `θ7 = arccos (7/10)`. -/
abbrev θ7 : ℝ := arccos (7 / 10)

lemma cos_θ7 : cos θ7 = 7 / 10 := cos_arccos (by norm_num) (by norm_num)

lemma θ7_nonneg : 0 ≤ θ7 := arccos_nonneg _

lemma θ7_lt_pi_div_three : θ7 < π / 3 := by
  have h : arccos (1 / 2) = π / 3 := by
    rw [← cos_pi_div_three, arccos_cos (by linarith [pi_pos]) (by linarith [pi_pos])]
  rw [← h]
  exact arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)

lemma pi_div_four_lt_θ7 : π / 4 < θ7 := by
  rw [lt_iff_not_ge, arccos_le_pi_div_four]
  intro h
  have h2 : √2 ≤ 7 / 5 := by linarith
  have h3 : (2 : ℝ) ≤ (7 / 5) ^ 2 := by
    rw [Real.sqrt_le_left (by norm_num)] at h2; exact h2
  norm_num at h3

lemma cos_half_θ7 : cos (θ7 / 2) = √(17 / 20) := by
  rw [cos_half (by linarith [pi_pos, θ7_nonneg]) (arccos_le_pi _), cos_θ7]
  norm_num

lemma cos_half_θ7_pos : 0 < cos (θ7 / 2) := by
  rw [cos_half_θ7]; positivity

lemma cos_half_θ7_sq : cos (θ7 / 2) ^ 2 = 17 / 20 := by
  rw [cos_half_θ7, Real.sq_sqrt (by norm_num)]

lemma rpow_inv_bounds {x a b : ℝ} {m : ℕ} (hm : m ≠ 0) (hx : 0 ≤ x) (hb : 0 ≤ b)
    (h1 : a ^ m < x) (h2 : x < b ^ m) :
    a < x ^ ((1 : ℝ) / m) ∧ x ^ ((1 : ℝ) / m) < b := by
  have hy : (x ^ ((1 : ℝ) / m)) ^ m = x := by
    rw [one_div]; exact Real.rpow_inv_natCast_pow hx hm
  have hy0 : 0 ≤ x ^ ((1 : ℝ) / m) := Real.rpow_nonneg hx _
  constructor
  · by_contra h
    push Not at h
    have := pow_le_pow_left₀ hy0 h m
    rw [hy] at this; linarith
  · by_contra h
    push Not at h
    have := pow_le_pow_left₀ hb h m
    rw [hy] at this; linarith

/-- k = 1 at r = 7/10: `exp(W/2) = cos(θ/2) = √0.85 ≈ 0.922`, which differs from `√(1 - 0.49)`. -/
theorem num_k1 :
    cos (θ7 / 2) = √(17 / 20) ∧
    Real.exp (worstBound 1 θ7 / 2) = √(17 / 20) ∧
    (0.921 : ℝ) < √(17 / 20) ∧ √(17 / 20) < (0.922 : ℝ) ∧
    √(17 / 20) ≠ √(1 - 0.49) := by
  have hW : worstBound 1 θ7 = 2 * Real.log (cos (θ7 / 2)) := by
    unfold worstBound
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]
    rw [show ((0 : ℝ) - 1 / 2) * θ7 = -(θ7 / 2) by ring, cos_neg,
      show ((1 : ℝ) - 1 / 2) * θ7 = θ7 / 2 by ring]
    ring
  refine ⟨cos_half_θ7, ?_, ?_, ?_, ?_⟩
  · rw [hW, show 2 * Real.log (cos (θ7 / 2)) / 2 = Real.log (cos (θ7 / 2)) by ring,
      Real.exp_log cos_half_θ7_pos, cos_half_θ7]
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num
  · intro h
    have h' : (√(17 / 20 : ℝ)) ^ 2 = (√(1 - 0.49 : ℝ)) ^ 2 := by rw [h]
    rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)] at h'
    norm_num at h'

/-- k = 2 at r = 7/10: `exp(W/3) = 0.49^(1/3) ≈ 0.788`. -/
theorem num_k2 :
    2 * θ7 < π ∧
    Real.exp (worstBound 2 θ7 / 3) = (0.49 : ℝ) ^ ((1 : ℝ) / 3) ∧
    (0.788 : ℝ) < (0.49 : ℝ) ^ ((1 : ℝ) / 3) ∧ (0.49 : ℝ) ^ ((1 : ℝ) / 3) < 0.789 := by
  have hW : worstBound 2 θ7 = Real.log (0.49 : ℝ) := by
    unfold worstBound
    rw [Fin.sum_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat]
    rw [show ((0 : ℝ) - 2 / 2) * θ7 = -θ7 by ring, cos_neg,
      show ((1 : ℝ) - 2 / 2) * θ7 = 0 by ring, cos_zero, Real.log_one,
      show ((2 : ℝ) - 2 / 2) * θ7 = θ7 by ring, cos_θ7,
      show (0.49 : ℝ) = (7 / 10) ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  refine ⟨by linarith [θ7_lt_pi_div_three, pi_pos], ?_, ?_⟩
  · rw [hW, Real.rpow_def_of_pos (by norm_num)]; ring_nf
  · have := rpow_inv_bounds (x := 0.49) (a := 0.788) (b := 0.789) (m := 3) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa using this

lemma log_bracket : (-2.161 : ℝ) < Real.log (289 / 2500) ∧ Real.log (289 / 2500) < -2.154 := by
  have e : Real.log (289 / 2500) = Real.log (2312 / 2500) - 3 * Real.log 2 := by
    rw [show (289 / 2500 : ℝ) = (2312 / 2500) / 2 ^ 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have hu := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2312 / 2500 by norm_num)
  have hl := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2312 / 2500 by norm_num)
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  rw [e]
  constructor
  · norm_num at hl ⊢; linarith
  · norm_num at hu ⊢; linarith

/-- k = 3 at r = 7/10: `3θ < π`, `W = log(0.85 · 0.136)`, `exp(W/4) = (0.85 · 0.136)^(1/4)
≈ 0.583`, and `W ≈ -2.158` (bracketed in `(-2.161, -2.154)`). -/
theorem num_k3 :
    3 * θ7 < π ∧
    worstBound 3 θ7 = Real.log (0.85 * 0.136) ∧
    Real.exp (worstBound 3 θ7 / 4) = ((0.85 : ℝ) * 0.136) ^ ((1 : ℝ) / 4) ∧
    (0.583 : ℝ) < ((0.85 : ℝ) * 0.136) ^ ((1 : ℝ) / 4) ∧
    ((0.85 : ℝ) * 0.136) ^ ((1 : ℝ) / 4) < 0.584 ∧
    (-2.161 : ℝ) < worstBound 3 θ7 ∧ worstBound 3 θ7 < -2.154 := by
  set c := cos (θ7 / 2) with hc
  have hc0 : 0 < c := cos_half_θ7_pos
  have hc2 : c ^ 2 = 17 / 20 := cos_half_θ7_sq
  have h3 : cos (3 * (θ7 / 2)) = c * (4 * c ^ 2 - 3) := by rw [cos_three_mul]; ring
  have h3' : cos (3 * (θ7 / 2)) = c * (2 / 5) := by rw [h3, hc2]; norm_num
  have h3pos : 0 < cos (3 * (θ7 / 2)) := by rw [h3']; positivity
  have hW : worstBound 3 θ7 = Real.log (0.85 * 0.136) := by
    unfold worstBound
    rw [Fin.sum_univ_four]
    have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, e3, Nat.cast_zero,
      Nat.cast_one, Nat.cast_ofNat]
    rw [show ((0 : ℝ) - 3 / 2) * θ7 = -(3 * (θ7 / 2)) by ring, cos_neg,
      show ((1 : ℝ) - 3 / 2) * θ7 = -(θ7 / 2) by ring, cos_neg,
      show ((2 : ℝ) - 3 / 2) * θ7 = θ7 / 2 by ring,
      show ((3 : ℝ) - 3 / 2) * θ7 = 3 * (θ7 / 2) by ring, ← hc,
      ← Real.log_mul h3pos.ne' hc0.ne', ← Real.log_mul (by positivity) hc0.ne',
      ← Real.log_mul (by positivity) h3pos.ne', h3']
    congr 1
    calc c * (2 / 5) * c * c * (c * (2 / 5)) = (c ^ 2) ^ 2 * (4 / 25) := by ring
      _ = _ := by rw [hc2]; norm_num
  have hbr := log_bracket
  have e289 : (0.85 : ℝ) * 0.136 = 289 / 2500 := by norm_num
  refine ⟨by linarith [θ7_lt_pi_div_three], hW, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hW, Real.rpow_def_of_pos (by norm_num)]; ring_nf
  · have := rpow_inv_bounds (x := (0.85 : ℝ) * 0.136) (a := 0.583) (b := 0.584) (m := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa using this.1
  · have := rpow_inv_bounds (x := (0.85 : ℝ) * 0.136) (a := 0.583) (b := 0.584) (m := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa using this.2
  · rw [hW, e289]; exact hbr.1
  · rw [hW, e289]; exact hbr.2

/-- k = 4 at r = 7/10: `4θ > π`, and the planar 7/10-chain (an r-chain) has no feasible point,
so no bargain is guaranteed. -/
theorem num_k4 (n : ℕ) :
    π < 4 * θ7 ∧ IsRChain (7 / 10) (planarChain n 4 θ7) ∧
    ¬ ∃ x : EuclideanSpace ℝ (Fin (n + 2)), Feasible (util (planarChain n 4 θ7)) x := by
  have h := pi_div_four_lt_θ7
  have h4 : π < 4 * θ7 := by linarith
  refine ⟨h4, planar_isRChain (by norm_num) (by norm_num), ?_⟩
  exact planar_not_feasible (by norm_num) (by norm_num) (by push_cast; linarith)

end

end Bridge6A
