import Mathlib

/-!
# F3 — Depth beyond compute as refinement 

What an observer can compute from data `D` is modelled as a deterministic coarsening `c : D → K`.
A joint `p : X → D → ℝ` (strictly positive, finite types) is pushed forward to `push p c : X → K → ℝ`.

PROVED (Lean, natural logs, finite types, strictly positive joint `p`; normalisation only where stated):
(1) `chain_rule`: `I(X;D) = I(X;c(D)) + I(X;D|c(D))`.
(2) `data_processing_coarsen`: `I(X;c(D)) ≤ I(X;D)`; `CMI_nonneg`.
(3) `refinement_mono`: `c' = h ∘ c → I(X;c'(D)) ≤ I(X;c(D))`; `edge_nonneg`.
Extras: `edge_eq_sum` (explicit edge formula), `edge_eq_CMI_drop` (edge = drop in residual conditional
information), `edge_le_MI`, `blind_knows_nothing` (a constant computer extracts zero).
Added in adversarial review (second agent):
`edge_pos_iff` (going up): under `c' = h ∘ c`, `0 < edge` iff the pushed posteriors differ somewhere,
i.e. the edge vanishes exactly when `c'(D)` is sufficient for `X` relative to `c(D)`.
`strict_edge_example` (non-vacuity): a concrete positive normalised joint on `Bool × Bool` where the
identity computer has a strictly positive edge over the constant computer.
REVIEW NOTES: the 9 original statements are unchanged. New declarations (`pEx`, `edge_pos_iff`,
`strict_edge_example`) are appended at the end of both files; `comparison_mass` is a proofs-file-only
helper (it restates the `hsum` step of `edge_nonneg`). Most theorems do not assume `∑ p = 1`; for a
non-normalised `p`, `MI` is not the Shannon quantity (it shifts by `-(∑p) log(∑p)`), but the
identities and inequalities still hold, and with `∑ p = 1` they are the standard ones.

INTERPRETED (not proved, not formalised): reading `c` as "what an observer can compute", `h ∘ c` as a
weaker computer, and the edge `I(X;c(D)) - I(X;c'(D)) ≥ 0` as information present in the data but
extractable only with more compute. Nothing here models computational cost, time bounds, or
learnability; "computer" is only a deterministic function of the data, and the order is factorisation.
Note: the zero-pattern of `push p c` (empty fibres) is handled with Lean's `0 * log _ = 0`; positivity
is assumed only of the fine joint `p`.
PROOFS FILE: statements identical to `F3_depth_refinement.statements.lean`; helper lemmas added above them.
-/

open Finset Real

set_option linter.unusedSectionVars false

namespace F3DepthRefinement

variable {X D K L : Type*} [Fintype X] [Fintype D] [Fintype K] [Fintype L]

noncomputable def margX (p : X → D → ℝ) (x : X) : ℝ := ∑ d, p x d
noncomputable def margY (p : X → D → ℝ) (d : D) : ℝ := ∑ x, p x d
noncomputable def MI (p : X → D → ℝ) : ℝ :=
  ∑ x, ∑ d, p x d * log (p x d / (margX p x * margY p d))

/-- Joint of `X` and the computed summary `c(D)`. -/
noncomputable def push [DecidableEq K] (p : X → D → ℝ) (c : D → K) (x : X) (k : K) : ℝ :=
  ∑ d ∈ univ with c d = k, p x d

/-- `I(X; D | c(D))`. -/
noncomputable def CMI [DecidableEq K] (p : X → D → ℝ) (c : D → K) : ℝ :=
  ∑ x, ∑ d, p x d * log (p x d * margY (push p c) (c d) / (push p c x (c d) * margY p d))

/-- The edge of computer `c` over computer `c'`. -/
noncomputable def edge [DecidableEq K] [DecidableEq L] (p : X → D → ℝ) (c : D → K) (c' : D → L) : ℝ :=
  MI (push p c) - MI (push p c')

/-! ## Helper lemmas (copied pattern from `scratch/KellyInformation.lean`) -/

theorem gibbs {ι : Type*} [Fintype ι] (p b : ι → ℝ) (hp : ∀ i, 0 < p i) (hb : ∀ i, 0 < b i)
    (hp1 : ∑ i, p i = 1) (hb1 : ∑ i, b i ≤ 1) :
    ∑ i, p i * log (b i) ≤ ∑ i, p i * log (p i) := by
  have key : ∀ i, p i * log (b i) - p i * log (p i) ≤ b i - p i := by
    intro i
    have h := log_le_sub_one_of_pos (div_pos (hb i) (hp i))
    rw [log_div (hb i).ne' (hp i).ne'] at h
    have h2 : p i * (log (b i) - log (p i)) ≤ p i * (b i / p i - 1) :=
      mul_le_mul_of_nonneg_left h (hp i).le
    have e : p i * (b i / p i - 1) = b i - p i := by
      have hp0 := (hp i).ne'
      field_simp
    linarith [h2, e, show p i * (log (b i) - log (p i)) = p i * log (b i) - p i * log (p i) by ring]
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at this
  linarith

theorem log_sum {ι : Type*} [Fintype ι] (a b : ι → ℝ) [Nonempty ι] (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) :
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

lemma margX_pos [Nonempty D] (p : X → D → ℝ) (hp : ∀ x d, 0 < p x d) (x : X) : 0 < margX p x :=
  Finset.sum_pos (fun d _ => hp x d) Finset.univ_nonempty

lemma margY_pos [Nonempty X] (p : X → D → ℝ) (hp : ∀ x d, 0 < p x d) (d : D) : 0 < margY p d :=
  Finset.sum_pos (fun x _ => hp x d) Finset.univ_nonempty

/-- Regrouping a sum over `D` by the fibres of `c`. -/
lemma fiber_sum [DecidableEq K] (c : D → K) (f : D → ℝ) (g : K → ℝ) :
    ∑ d, f d * g (c d) = ∑ k, (∑ d ∈ univ with c d = k, f d) * g k := by
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise univ c (fun d => f d * g (c d))]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro d hd
  rw [(Finset.mem_filter.1 hd).2]

lemma margX_push [DecidableEq K] (p : X → D → ℝ) (c : D → K) (x : X) :
    margX (push p c) x = margX p x := by
  unfold margX push; exact Finset.sum_fiberwise univ c (p x)

lemma margY_push [DecidableEq K] (p : X → D → ℝ) (c : D → K) (k : K) :
    margY (push p c) k = ∑ d ∈ univ with c d = k, margY p d := by
  unfold margY push; exact Finset.sum_comm

lemma push_pos [DecidableEq K] (p : X → D → ℝ) (hp : ∀ x d, 0 < p x d) (c : D → K) (x : X) (d : D) :
    0 < push p c x (c d) := by
  unfold push
  exact Finset.sum_pos (fun d' _ => hp x d') ⟨d, by simp⟩

lemma margY_push_pos [DecidableEq K] [Nonempty X] (p : X → D → ℝ) (hp : ∀ x d, 0 < p x d)
    (c : D → K) (d : D) : 0 < margY (push p c) (c d) :=
  Finset.sum_pos (fun x _ => push_pos p hp c x d) Finset.univ_nonempty

/-- `I(X; c(D))` written as a sum over the fine data `D`. No positivity needed. -/
lemma MI_push_eq [DecidableEq K] (p : X → D → ℝ) (c : D → K) :
    MI (push p c) = ∑ x, ∑ d, p x d *
      log (push p c x (c d) / (margX p x * margY (push p c) (c d))) := by
  unfold MI
  apply Finset.sum_congr rfl; intro x _
  have := fiber_sum c (p x) (fun k => log (push p c x k / (margX p x * margY (push p c) k)))
  rw [this]
  apply Finset.sum_congr rfl; intro k _
  rw [margX_push]; rfl

/-- **(1) Chain rule with a function.** PROVED: for strictly positive `p` and any `c`,
`I(X;D) = I(X;c(D)) + I(X;D|c(D))`. Normalisation `∑ p = 1` is not needed (the identity is termwise). -/
theorem chain_rule [DecidableEq K] [Nonempty X] [Nonempty D] (p : X → D → ℝ) (hp : ∀ x d, 0 < p x d)
    (c : D → K) : MI p = MI (push p c) + CMI p c := by
  have hx := margX_pos p hp
  have hy := margY_pos p hp
  rw [MI_push_eq]
  unfold MI CMI
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro x _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro d _
  have hP := push_pos p hp c x d
  have hK := margY_push_pos p hp c d
  have h1 := hp x d
  have h2 := hx x
  have h3 := hy d
  rw [← mul_add, ← log_mul (by positivity) (by positivity)]
  congr 2
  field_simp

/-- **Edge formula.** PROVED: for any two computers `c, c'` (no factorisation needed),
`I(X;c(D)) - I(X;c'(D)) = ∑ₓ,d p(x,d) log[ p(x,c d) p(c' d) / (p(x,c' d) p(c d)) ]`. -/
theorem edge_eq_sum [DecidableEq K] [DecidableEq L] [Nonempty X] [Nonempty D] (p : X → D → ℝ)
    (hp : ∀ x d, 0 < p x d) (c : D → K) (c' : D → L) :
    edge p c c' = ∑ x, ∑ d, p x d *
      log (push p c x (c d) * margY (push p c') (c' d) / (push p c' x (c' d) * margY (push p c) (c d))) := by
  unfold edge
  rw [MI_push_eq p c, MI_push_eq p c', ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro x _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro d _
  have hP := push_pos p hp c x d
  have hK := margY_push_pos p hp c d
  have hP' := push_pos p hp c' x d
  have hK' := margY_push_pos p hp c' d
  have h2 := margX_pos p hp x
  rw [← mul_sub, ← log_div (by positivity) (by positivity)]
  congr 2
  field_simp

/-- **(3') The edge is nonnegative.** PROVED: if `c' = h ∘ c` then `edge p c c' ≥ 0`
(log-sum inequality against a comparison measure of the same total mass). -/
theorem edge_nonneg [DecidableEq K] [DecidableEq L] [Nonempty X] [Nonempty D] (p : X → D → ℝ)
    (hp : ∀ x d, 0 < p x d) (c : D → K) (c' : D → L) (h : K → L) (hfac : ∀ d, c' d = h (c d)) :
    0 ≤ edge p c c' := by
  rw [edge_eq_sum p hp c c']
  -- the comparison measure `b` on `X × D`
  set b : X × D → ℝ := fun q => p q.1 q.2 * push p c' q.1 (c' q.2) * margY (push p c) (c q.2) /
    (push p c q.1 (c q.2) * margY (push p c') (c' q.2)) with hbdef
  have hb : ∀ q, 0 < b q := by
    intro q
    have := hp q.1 q.2
    have := push_pos p hp c q.1 q.2
    have := push_pos p hp c' q.1 q.2
    have := margY_push_pos p hp c q.2
    have := margY_push_pos p hp c' q.2
    simp only [hbdef]
    positivity
  have ls := log_sum (fun q : X × D => p q.1 q.2) b (fun q => hp q.1 q.2) hb
  -- total mass of `b` equals total mass of `p`
  have hsum : ∑ q, b q = ∑ q : X × D, p q.1 q.2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [hbdef, hfac]
    have step1 : ∀ x, ∑ d, p x d * push p c' x (h (c d)) * margY (push p c) (c d) /
        (push p c x (c d) * margY (push p c') (h (c d))) =
        ∑ k, push p c x k * (push p c' x (h k) * margY (push p c) k /
          (push p c x k * margY (push p c') (h k))) := by
      intro x
      refine Eq.trans ?_ (fiber_sum c (p x) (fun k => push p c' x (h k) * margY (push p c) k /
          (push p c x k * margY (push p c') (h k))))
      apply Finset.sum_congr rfl; intro d _; ring
    simp_rw [step1]
    rw [Finset.sum_comm]
    have step2 : ∀ k, ∑ x, push p c x k * (push p c' x (h k) * margY (push p c) k /
        (push p c x k * margY (push p c') (h k))) = margY (push p c) k := by
      intro k
      by_cases hk : ∃ d, c d = k
      · obtain ⟨d0, rfl⟩ := hk
        have hK := margY_push_pos p hp c d0
        have hK' := margY_push_pos p hp c' d0
        rw [hfac d0] at hK'
        have e : ∀ x, push p c x (c d0) * (push p c' x (h (c d0)) * margY (push p c) (c d0) /
            (push p c x (c d0) * margY (push p c') (h (c d0)))) =
            push p c' x (h (c d0)) * (margY (push p c) (c d0) / margY (push p c') (h (c d0))) := by
          intro x
          have := push_pos p hp c x d0
          field_simp
        simp_rw [e]
        rw [← Finset.sum_mul]
        change margY (push p c') (h (c d0)) * _ = _
        field_simp
      · push Not at hk
        have h0 : ∀ x, push p c x k = 0 := by
          intro x
          unfold push
          rw [Finset.sum_eq_zero]
          intro d hd
          exact absurd (Finset.mem_filter.1 hd).2 (hk d)
        have hK0 : margY (push p c) k = 0 := by
          unfold margY; simp [h0]
        simp [h0, hK0]
    simp_rw [step2]
    simp_rw [margY_push]
    rw [Finset.sum_fiberwise univ c (fun d => margY p d)]
    unfold margY
    rw [Finset.sum_comm]
  rw [hsum, div_self (Finset.sum_pos (fun q _ => hp q.1 q.2) Finset.univ_nonempty).ne', log_one,
    mul_zero, Fintype.sum_prod_type] at ls
  refine ls.trans (le_of_eq ?_)
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro d _
  have := hp x d
  have := push_pos p hp c x d
  have := push_pos p hp c' x d
  have := margY_push_pos p hp c d
  have := margY_push_pos p hp c' d
  simp only [hbdef]
  congr 2
  field_simp

/-- **(3) A better computer never knows less.** PROVED: if `c'` factors through `c`
(`c' d = h (c d)`), then `I(X; c'(D)) ≤ I(X; c(D))`.
INTERPRETED (not proved): `c'` is a weaker computer, since anything it computes is computable from `c`'s output. -/
theorem refinement_mono [DecidableEq K] [DecidableEq L] [Nonempty X] [Nonempty D] (p : X → D → ℝ)
    (hp : ∀ x d, 0 < p x d) (c : D → K) (c' : D → L) (h : K → L) (hfac : ∀ d, c' d = h (c d)) :
    MI (push p c') ≤ MI (push p c) := by
  have := edge_nonneg p hp c c' h hfac
  unfold edge at this
  linarith

/-- **(2) Data processing for a deterministic coarsening.** PROVED: `I(X; c(D)) ≤ I(X; D)`,
as the special case `c := id`, `h := c` of (3) plus `push p id = p`. -/
theorem data_processing_coarsen [DecidableEq K] [Nonempty X] [Nonempty D] (p : X → D → ℝ)
    (hp : ∀ x d, 0 < p x d) (c : D → K) : MI (push p c) ≤ MI p := by
  classical
  have hid : push p (id : D → D) = p := by
    funext x d
    unfold push
    rw [Finset.sum_filter]
    simp
  have := refinement_mono p hp id c c (fun d => rfl)
  rwa [hid] at this

/-- PROVED: `I(X; D | c(D)) ≥ 0` (from (1) and (2)). -/
theorem CMI_nonneg [DecidableEq K] [Nonempty X] [Nonempty D] (p : X → D → ℝ)
    (hp : ∀ x d, 0 < p x d) (c : D → K) : 0 ≤ CMI p c := by
  linarith [chain_rule p hp c, data_processing_coarsen p hp c]

/-- PROVED: the edge of `c` over `c'` is exactly the drop in residual conditional information,
`edge p c c' = I(X;D|c'(D)) - I(X;D|c(D))` (two applications of (1); holds for any `c, c'`).
INTERPRETED: the stronger computer's edge is information present in `D` that `c'` leaves unextracted and `c` extracts. -/
theorem edge_eq_CMI_drop [DecidableEq K] [DecidableEq L] [Nonempty X] [Nonempty D] (p : X → D → ℝ)
    (hp : ∀ x d, 0 < p x d) (c : D → K) (c' : D → L) :
    edge p c c' = CMI p c' - CMI p c := by
  unfold edge
  linarith [chain_rule p hp c, chain_rule p hp c']

/-- PROVED: `edge p c c' ≤ I(X;D) - I(X;c'(D))`: no computer's edge exceeds what the raw data holds beyond `c'`. -/
theorem edge_le_MI [DecidableEq K] [DecidableEq L] [Nonempty X] [Nonempty D] (p : X → D → ℝ)
    (hp : ∀ x d, 0 < p x d) (c : D → K) (c' : D → L) :
    edge p c c' ≤ MI p - MI (push p c') := by
  unfold edge
  linarith [data_processing_coarsen p hp c]

/-- PROVED: a constant computer (bottom of the refinement order) extracts zero information,
for a normalised positive joint. Combined with (3): `edge p c (const) = I(X; c(D))`. -/
theorem blind_knows_nothing [DecidableEq K] [Nonempty X] [Nonempty D] (p : X → D → ℝ)
    (hp : ∀ x d, 0 < p x d) (hp1 : ∑ x, ∑ d, p x d = 1) (k₀ : K) :
    MI (push p (fun _ => k₀)) = 0 := by
  have hpush : ∀ x k, push p (fun _ => k₀) x k = if k₀ = k then margX p x else 0 := by
    intro x k
    unfold push margX
    by_cases hk : k₀ = k <;> simp [hk]
  have hK : margY (push p (fun _ => k₀)) k₀ = 1 := by
    unfold margY
    simp_rw [hpush]
    simpa [margX] using hp1
  unfold MI
  apply Finset.sum_eq_zero; intro x _
  apply Finset.sum_eq_zero; intro k _
  by_cases hk : k₀ = k
  · subst hk
    rw [hK, margX_push, hpush]
    simp only [↓reduceIte]
    rw [mul_one, div_self (margX_pos p hp x).ne', log_one, mul_zero]
  · rw [hpush]
    simp [hk]

/-! ## Added by the adversarial second agent: strict edge characterisation -/

/-- Helper (proofs file only): the comparison measure `p · r` used in `edge_nonneg` has the same
total mass as `p`. Same argument as `hsum` inside `edge_nonneg`, restated as a lemma. -/
lemma comparison_mass [DecidableEq K] [DecidableEq L] [Nonempty X] [Nonempty D] (p : X → D → ℝ)
    (hp : ∀ x d, 0 < p x d) (c : D → K) (c' : D → L) (h : K → L) (hfac : ∀ d, c' d = h (c d)) :
    ∑ x, ∑ d, p x d * (push p c' x (c' d) * margY (push p c) (c d) /
      (push p c x (c d) * margY (push p c') (c' d))) = ∑ x, ∑ d, p x d := by
  simp only [hfac]
  have step1 : ∀ x, ∑ d, p x d * (push p c' x (h (c d)) * margY (push p c) (c d) /
      (push p c x (c d) * margY (push p c') (h (c d)))) =
      ∑ k, push p c x k * (push p c' x (h k) * margY (push p c) k /
        (push p c x k * margY (push p c') (h k))) := fun x =>
    fiber_sum c (p x) (fun k => push p c' x (h k) * margY (push p c) k /
        (push p c x k * margY (push p c') (h k)))
  simp_rw [step1]
  rw [Finset.sum_comm]
  have step2 : ∀ k, ∑ x, push p c x k * (push p c' x (h k) * margY (push p c) k /
      (push p c x k * margY (push p c') (h k))) = margY (push p c) k := by
    intro k
    by_cases hk : ∃ d, c d = k
    · obtain ⟨d0, rfl⟩ := hk
      have hK := margY_push_pos p hp c d0
      have hK' := margY_push_pos p hp c' d0
      rw [hfac d0] at hK'
      have e : ∀ x, push p c x (c d0) * (push p c' x (h (c d0)) * margY (push p c) (c d0) /
          (push p c x (c d0) * margY (push p c') (h (c d0)))) =
          push p c' x (h (c d0)) * (margY (push p c) (c d0) / margY (push p c') (h (c d0))) := by
        intro x
        have := push_pos p hp c x d0
        field_simp
      simp_rw [e]
      rw [← Finset.sum_mul]
      change margY (push p c') (h (c d0)) * _ = _
      field_simp
    · push Not at hk
      have h0 : ∀ x, push p c x k = 0 := by
        intro x
        unfold push
        rw [Finset.sum_eq_zero]
        intro d hd
        exact absurd (Finset.mem_filter.1 hd).2 (hk d)
      have hK0 : margY (push p c) k = 0 := by
        unfold margY; simp [h0]
      simp [h0, hK0]
  simp_rw [step2]
  simp_rw [margY_push]
  rw [Finset.sum_fiberwise univ c (fun d => margY p d)]
  unfold margY
  rw [Finset.sum_comm]

/-- **Going up: when is the edge strict?** PROVED: if `c' = h ∘ c`, then the stronger computer has a
strictly positive edge, `0 < I(X;c(D)) - I(X;c'(D))`, iff for some `(x,d)` the two cross-products differ:
`p(x, c d) · P_{c'}(c' d) ≠ p(x, c' d) · P_c(c d)` (pushed joints / pushed `D`-marginals). For a normalised
joint this says that the posteriors differ somewhere: `P(X=x | c(D)=c d) ≠ P(X=x | c'(D)=c' d)`.
Equivalently (contrapositive): the edge is zero iff `c'(D)` is already a sufficient statistic of `c(D)`
for `X`. Proof: the strict form of `log t ≤ t - 1` (`Real.log_lt_sub_one_of_pos`) against the
comparison measure of `comparison_mass`.
INTERPRETED (not proved): extra compute buys something exactly when the coarse summary loses
some of the dependence between `X` and the fine summary. -/
theorem edge_pos_iff [DecidableEq K] [DecidableEq L] [Nonempty X] [Nonempty D] (p : X → D → ℝ)
    (hp : ∀ x d, 0 < p x d) (c : D → K) (c' : D → L) (h : K → L) (hfac : ∀ d, c' d = h (c d)) :
    0 < edge p c c' ↔ ∃ x d, push p c x (c d) * margY (push p c') (c' d) ≠
      push p c' x (c' d) * margY (push p c) (c d) := by
  set r : X → D → ℝ := fun x d => push p c' x (c' d) * margY (push p c) (c d) /
      (push p c x (c d) * margY (push p c') (c' d)) with hr
  have hrpos : ∀ x d, 0 < r x d := by
    intro x d
    have := push_pos p hp c x d
    have := push_pos p hp c' x d
    have := margY_push_pos p hp c d
    have := margY_push_pos p hp c' d
    simp only [hr]
    positivity
  have hE : edge p c c' = ∑ x, ∑ d, p x d * (- log (r x d)) := by
    rw [edge_eq_sum p hp c c']
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro d _
    rw [← log_inv]
    congr 2
    simp only [hr]
    rw [inv_div]
  have hmass : ∑ x, ∑ d, p x d * r x d = ∑ x, ∑ d, p x d := comparison_mass p hp c c' h hfac
  have hr1 : ∀ x d, r x d = 1 ↔ push p c x (c d) * margY (push p c') (c' d) =
      push p c' x (c' d) * margY (push p c) (c d) := by
    intro x d
    have := push_pos p hp c x d
    have := margY_push_pos p hp c' d
    simp only [hr]
    rw [div_eq_one_iff_eq (by positivity), eq_comm]
  have hterm : ∀ x d, p x d - p x d * r x d ≤ p x d * (- log (r x d)) := by
    intro x d
    have h1 := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (hrpos x d)) (hp x d).le
    nlinarith
  constructor
  · intro hpos
    by_contra hno
    push Not at hno
    have h0 : edge p c c' = 0 := by
      rw [hE]
      apply Finset.sum_eq_zero; intro x _
      apply Finset.sum_eq_zero; intro d _
      rw [(hr1 x d).2 (hno x d), log_one]
      ring
    linarith
  · rintro ⟨x0, d0, hne⟩
    have hne' : r x0 d0 ≠ 1 := fun e => hne ((hr1 x0 d0).1 e)
    have hstrict : p x0 d0 - p x0 d0 * r x0 d0 < p x0 d0 * (- log (r x0 d0)) := by
      have h1 := mul_lt_mul_of_pos_left (log_lt_sub_one_of_pos (hrpos x0 d0) hne') (hp x0 d0)
      nlinarith
    have hlt : ∑ q : X × D, (p q.1 q.2 - p q.1 q.2 * r q.1 q.2) <
        ∑ q : X × D, p q.1 q.2 * (- log (r q.1 q.2)) :=
      Finset.sum_lt_sum (fun q _ => hterm q.1 q.2) ⟨(x0, d0), Finset.mem_univ _, hstrict⟩
    simp only [Fintype.sum_prod_type, Finset.sum_sub_distrib] at hlt
    rw [hE]
    linarith

/-- Concrete joint used for the non-vacuity example: `X = D = Bool`, `p(x,d) = 2/5` on the
diagonal and `1/10` off it (strictly positive, total mass 1). -/
noncomputable def pEx (x d : Bool) : ℝ := if x = d then 2 / 5 else 1 / 10

/-- **Non-vacuity / strict edge example.** PROVED: for the concrete joint `pEx`, the identity
computer has a strictly positive edge over the blind (constant) computer, and every hypothesis of the
main theorems is satisfiable here (`pEx` is strictly positive, normalised). Not stated separately:
by `blind_knows_nothing` this edge is `I(X; id(D)) = I(X; D)`, so here `I(X; D) > 0`. -/
theorem strict_edge_example :
    (∀ x d, 0 < pEx x d) ∧ (∑ x, ∑ d, pEx x d = 1) ∧
      0 < edge pEx (id : Bool → Bool) (fun _ : Bool => ()) := by
  have hp : ∀ x d, 0 < pEx x d := by
    intro x d; unfold pEx; split_ifs <;> norm_num
  refine ⟨hp, ?_, ?_⟩
  · simp [pEx]; norm_num
  · rw [edge_pos_iff pEx hp id (fun _ : Bool => ()) (fun _ => ()) (fun _ => rfl)]
    refine ⟨true, true, ?_⟩
    simp [push, margY, pEx, Finset.filter_eq']
    norm_num

end F3DepthRefinement
