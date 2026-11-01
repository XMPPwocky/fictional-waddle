import Mathlib

/-!
# F2: private randomness predicts nothing, but protects (proofs)

Setting. Finite types `X` (outcome), `D` (data), `R` (private randomness). A joint "distribution" is any
`p : X → D → R → ℝ`; marginals are plain finite sums. The independent case is `joint q u x d r = q x d * u r`
(R independent of (X, D)).

Part A (prediction). Defined quantities:
* `condMI p` = `I(X; R | D) = Σ p(x,d,r) log( p(x,d,r) p(d) / (p(x,d) p(d,r)) )` (natural log, Lean's
  `log`/division conventions; zero-mass terms contribute `0`).
* `growthDR p o` = Kelly growth of the proportional bettor who sees `(D, R)`: bets `p(x | d, r)`.
* `growthD p o` = Kelly growth of the proportional bettor who sees only `D`: bets `p(x | d)`.
* `growth p o b` = growth of an ARBITRARY `(D, R)`-measurable betting strategy `b d r x`.

Proved claims (all proved in this file; statements identical to `F2_private_randomness.statements.lean`;
no statement of the first prover was changed. Added here only: A6 below (also stated in the statements
file), helper lemmas `condMI_term`, `sum_condProd`, `marg_pos`, `condMI_eq_sum_gap`, `condMI_nonneg`, and
a final `Examples` section with concrete instances showing the hypotheses are satisfiable and that A6's
"only if" direction has content: a dependent `pDep` with `growthD < growthDR`, and a `Fin 3` front-running
instance where the deterministic policy nets `1/2` and the uniform one nets `5/6`):
* `condMI_joint_eq_zero`: if `p = joint q u` and `Σ u = 1`, then `I(X;R|D) = 0`. No positivity needed.
* `growthDR_joint_eq_growthD`: under the same hypotheses, the proportional bettor who also sees `R`
  grows at exactly the rate of the one who sees only `D`. No positivity needed.
* `growthDR_sub_growthD` (general case, any strictly positive `p`): the gap between the two proportional
  bettors is EXACTLY `I(X;R|D)`; so the independent case is the zero of a general identity.
* `growth_le_growthD_of_joint`: for strictly positive `q, u, o` with `Σ u = 1`, EVERY `(D,R)`-strategy
  `b` (positive, `Σ_x b d r x ≤ 1`) grows at most `growthD`; and `growthD` is attained by the
  `D`-only strategy `p(x | d)` (`growth_condD_eq_growthD`). So the supremum over strategies that see `R`
  equals the supremum over strategies that do not.
* `growthDR_eq_growthD_iff` (A6, added by the second agent; going up to the iff): for strictly positive
  `p` and `o`, `growthDR = growthD` IFF `p(x,d,r) p(d) = p(x,d) p(d,r)` for all `x,d,r` (i.e.
  `R ⟂ X | D`). Proved via `condMI_nonneg` and the strict Gibbs inequality (`condMI_term`). So
  conditional independence is exactly the condition under which `R` is worthless to the proportional
  bettor; A2 is its "if" half (A2 also holds without positivity).

Part B (protection; self-contained). `scratch/edge/E3_front_running.lean` now exists with proofs, but
`scratch/` is not a `lean_lib` in `lakefile.toml`, so it cannot be `import`ed; the definitions `gross`,
`stolenMax`, `net` below are verbatim copies of `FrontRunning.gross/stolenMax/net` there. Our
`net_point_mass` needs only `0 ≤ e astar` (E3's needs `∀ a, 0 ≤ e a`), so it is slightly stronger. A trader samples action `a ~ p` on a
finite nonempty `A`; action `a` has edge `e a`. An adversary who knows `p` but NOT the sample picks one
guess `b`; on a match it steals fraction `lam` of the edge, so its best catch is `stolenMax p e =
max_b p b * e b` and the trader nets `net lam p e = gross p e - lam * stolenMax p e`.
* `net_point_mass`: deterministic policy on `astar` (with `e astar ≥ 0`) nets `(1 - lam) * e astar`:
  loss `lam * e astar`.
* `net_uniform`, `loss_uniform`: uniform over a `k`-element set `S` of equally good actions (edge `E ≥ 0`)
  nets `E * (1 - lam / k)`: loss `lam * E / k`.
* `mixing_protects`: for `astar ∈ S`, both policies have gross `E` and the mixed loss is exactly the
  deterministic loss divided by `k`.
* `informed_catch_le`, `informed_catch_id`: an adversary who SEES the sample (any guess rule
  `g : A → A`) catches at most `gross`, and `g = id` catches all of it; so against an informed adversary
  the uniform policy loses `lam * E`, the same as the deterministic one (`informed_loss_uniform`).
  Privacy of the sample is what does the protecting.

Not proved: that `I(X;R|D) = 0` alone forces conditional independence for joints with zeros (A6 assumes
strict positivity); optimality of the uniform policy among all mixed policies (E3 does the 2-action case).

Interpreted (NOT proved): that Kelly log-growth and "sees R" = "may condition its bet on R" capture
"predicts" (the model is the Cover-Thomas horse race: wealth multiplies by `b x * o x`, unbet mass is
lost, not held as cash, so `Σ b < 1` is merely dominated); that the single-guess, risk-neutral front-runner models adversarial exploitation; the reading
"randomness predicts nothing but protects" as a slogan joining Part A (R carries zero information about X
given D) with Part B (R carries maximal relevant information about the trader's own action, which is why
hiding it from the adversary matters).
-/

open Finset Real

set_option linter.unusedSectionVars false

namespace PrivateRandomness

section PartA

variable {X D R : Type*} [Fintype X] [Fintype D] [Fintype R]

/-- The independent joint `p(x,d,r) = q(x,d) * u(r)`. -/
def joint (q : X → D → ℝ) (u : R → ℝ) : X → D → R → ℝ := fun x d r => q x d * u r

/-- Marginal `p(x,d)`. -/
noncomputable def mXD (p : X → D → R → ℝ) (x : X) (d : D) : ℝ := ∑ r, p x d r
/-- Marginal `p(d,r)`. -/
noncomputable def mDR (p : X → D → R → ℝ) (d : D) (r : R) : ℝ := ∑ x, p x d r
/-- Marginal `p(d)`. -/
noncomputable def mD (p : X → D → R → ℝ) (d : D) : ℝ := ∑ x, ∑ r, p x d r

/-- Conditional mutual information `I(X; R | D)`. -/
noncomputable def condMI (p : X → D → R → ℝ) : ℝ :=
  ∑ x, ∑ d, ∑ r, p x d r * log (p x d r * mD p d / (mXD p x d * mDR p d r))

/-- Growth (expected log wealth) of a `(D,R)`-strategy `b d r x` at odds `o x`. -/
noncomputable def growth (p : X → D → R → ℝ) (o : X → ℝ) (b : D → R → X → ℝ) : ℝ :=
  ∑ x, ∑ d, ∑ r, p x d r * log (b d r x * o x)

/-- Kelly growth of the proportional bettor who sees `(D, R)`: bets `p(x | d, r)`. -/
noncomputable def growthDR (p : X → D → R → ℝ) (o : X → ℝ) : ℝ :=
  ∑ x, ∑ d, ∑ r, p x d r * log (p x d r / mDR p d r * o x)

/-- Kelly growth of the proportional bettor who sees only `D`: bets `p(x | d)`. -/
noncomputable def growthD (p : X → D → R → ℝ) (o : X → ℝ) : ℝ :=
  ∑ x, ∑ d, ∑ r, p x d r * log (mXD p x d / mD p d * o x)


/-! ### Helper lemmas (Part A) -/

theorem mXD_joint (q : X → D → ℝ) (u : R → ℝ) (hu1 : ∑ r, u r = 1) (x : X) (d : D) :
    mXD (joint q u) x d = q x d := by
  simp [mXD, joint, ← Finset.mul_sum, hu1]

theorem mDR_joint (q : X → D → ℝ) (u : R → ℝ) (d : D) (r : R) :
    mDR (joint q u) d r = (∑ x, q x d) * u r := by
  simp [mDR, joint, Finset.sum_mul]

theorem mD_joint (q : X → D → ℝ) (u : R → ℝ) (hu1 : ∑ r, u r = 1) (d : D) :
    mD (joint q u) d = ∑ x, q x d := by
  simp [mD, joint, ← Finset.mul_sum, hu1]

/-- Weighted Gibbs / Kelly: with positive weights `c`, the best positive sub-probability bet is `c / Σ c`. -/
theorem gibbs_weighted (c b o : X → ℝ) (hc : ∀ x, 0 < c x) (hb : ∀ x, 0 < b x)
    (hb1 : ∑ x, b x ≤ 1) (ho : ∀ x, 0 < o x) :
    ∑ x, c x * log (b x * o x) ≤ ∑ x, c x * log (c x / (∑ x', c x') * o x) := by
  set C := ∑ x', c x' with hCdef
  have hCx : ∀ x, 0 < C := fun x =>
    lt_of_lt_of_le (hc x) (Finset.single_le_sum (fun i _ => (hc i).le) (Finset.mem_univ x))
  have hterm : ∀ x, c x * log (b x * o x) - c x * log (c x / C * o x) ≤ b x * C - c x := by
    intro x
    have hC := hCx x
    have hcx := hc x
    have hbx := hb x
    have hox := ho x
    have e1 : c x * log (b x * o x) - c x * log (c x / C * o x) = c x * log (b x * C / c x) := by
      rw [Real.log_mul hbx.ne' hox.ne', Real.log_mul (by positivity) hox.ne',
        Real.log_div hcx.ne' hC.ne', Real.log_div (by positivity) hcx.ne',
        Real.log_mul hbx.ne' hC.ne']
      ring
    rw [e1]
    have := Real.log_le_sub_one_of_pos (show 0 < b x * C / c x by positivity)
    calc c x * log (b x * C / c x) ≤ c x * (b x * C / c x - 1) :=
          mul_le_mul_of_nonneg_left this hcx.le
      _ = b x * C - c x := by field_simp
  have hsum : ∑ x, c x * log (b x * o x) - ∑ x, c x * log (c x / C * o x) ≤
      ∑ x, (b x * C - c x) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun x _ => hterm x
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => (hc i).le
  have : ∑ x, (b x * C - c x) = C * (∑ x, b x) - C := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hCdef]; ring
  rw [this] at hsum
  nlinarith

/-- **A1.** Independent private randomness carries no information about `X` given `D`. -/
theorem condMI_joint_eq_zero (q : X → D → ℝ) (u : R → ℝ) (hu1 : ∑ r, u r = 1) :
    condMI (joint q u) = 0 := by
  unfold condMI
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun r _ => ?_
  rw [mD_joint q u hu1, mXD_joint q u hu1, mDR_joint]
  simp only [joint]
  by_cases h : q x d * u r = 0
  · rw [h, zero_mul]
  · have hq : q x d ≠ 0 := left_ne_zero_of_mul h
    have hu : u r ≠ 0 := right_ne_zero_of_mul h
    by_cases hQ : (∑ x', q x' d) = 0
    · simp [hQ]
    · have : q x d * u r * (∑ x', q x' d) / (q x d * ((∑ x', q x' d) * u r)) = 1 := by
        field_simp
      rw [this, Real.log_one, mul_zero]

/-- **A2.** Seeing independent `R` does not change the proportional (Kelly) bettor's growth. -/
theorem growthDR_joint_eq_growthD (q : X → D → ℝ) (u : R → ℝ) (o : X → ℝ) (hu1 : ∑ r, u r = 1) :
    growthDR (joint q u) o = growthD (joint q u) o := by
  unfold growthDR growthD
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun r _ => ?_
  rw [mD_joint q u hu1, mXD_joint q u hu1, mDR_joint]
  simp only [joint]
  by_cases hu : u r = 0
  · simp [hu]
  · rw [mul_div_mul_right _ _ hu]

/-- **A3 (general case).** For any strictly positive joint, the extra growth from also seeing `R` is
exactly `I(X; R | D)`. -/
theorem growthDR_sub_growthD (p : X → D → R → ℝ) (o : X → ℝ) (hp : ∀ x d r, 0 < p x d r)
    (ho : ∀ x, 0 < o x) :
    growthDR p o - growthD p o = condMI p := by
  unfold growthDR growthD condMI
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h1 : 0 < p x d r := hp x d r
  have h2 : 0 < mDR p d r := Finset.sum_pos (fun x _ => hp x d r) ⟨x, Finset.mem_univ _⟩
  have h3 : 0 < mXD p x d := Finset.sum_pos (fun r _ => hp x d r) ⟨r, Finset.mem_univ _⟩
  have h4 : 0 < mD p d := Finset.sum_pos (fun x _ => Finset.sum_pos (fun r _ => hp x d r)
    ⟨r, Finset.mem_univ _⟩) ⟨x, Finset.mem_univ _⟩
  have h5 : 0 < o x := ho x
  rw [← mul_sub]
  congr 1
  rw [Real.log_mul (by positivity) h5.ne', Real.log_mul (by positivity) h5.ne',
    Real.log_div h1.ne' h2.ne', Real.log_div h3.ne' h4.ne',
    Real.log_div (by positivity) (by positivity), Real.log_mul h1.ne' h4.ne',
    Real.log_mul h3.ne' h2.ne']
  ring

/-- **A4.** The `D`-only proportional strategy `p(x | d)` attains `growthD` (definitional). -/
theorem growth_condD_eq_growthD (p : X → D → R → ℝ) (o : X → ℝ) :
    growth p o (fun d _ x => mXD p x d / mD p d) = growthD p o := by
  rfl

/-- **A5.** Under independence, NO strategy that may look at `R` beats `growthD`. -/
theorem growth_le_growthD_of_joint (q : X → D → ℝ) (u : R → ℝ) (o : X → ℝ)
    (hq : ∀ x d, 0 < q x d) (hu : ∀ r, 0 < u r) (hu1 : ∑ r, u r = 1) (ho : ∀ x, 0 < o x)
    (b : D → R → X → ℝ) (hb : ∀ d r x, 0 < b d r x) (hb1 : ∀ d r, ∑ x, b d r x ≤ 1) :
    growth (joint q u) o b ≤ growthD (joint q u) o := by
  have hL : growth (joint q u) o b =
      ∑ d, ∑ r, u r * ∑ x, q x d * log (b d r x * o x) := by
    unfold growth joint
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hRR : growthD (joint q u) o =
      ∑ d, ∑ r, u r * ∑ x, q x d * log (q x d / (∑ x', q x' d) * o x) := by
    unfold growthD
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mD_joint q u hu1, mXD_joint q u hu1]
    simp only [joint]
    ring
  rw [hL, hRR]
  refine Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun r _ => ?_
  exact mul_le_mul_of_nonneg_left
    (gibbs_weighted (fun x => q x d) (b d r) o (fun x => hq x d) (hb d r) (hb1 d r) ho)
    (hu r).le


/-- Per-term Gibbs bound with its equality case. -/
theorem condMI_term (a m1 m2 m : ℝ) (ha : 0 < a) (h1 : 0 < m1) (h2 : 0 < m2) (hm : 0 < m) :
    0 ≤ a * log (a * m / (m1 * m2)) - a + m1 * m2 / m ∧
    (a * log (a * m / (m1 * m2)) - a + m1 * m2 / m = 0 → a * m = m1 * m2) := by
  set s := m1 * m2 / m / a with hs
  have hspos : 0 < s := by positivity
  have hlog : log (a * m / (m1 * m2)) = - log s := by
    rw [show a * m / (m1 * m2) = s⁻¹ by rw [hs]; field_simp, Real.log_inv]
  have hc : m1 * m2 / m = a * s := by rw [hs]; field_simp
  have key : a * log (a * m / (m1 * m2)) - a + m1 * m2 / m = a * (s - 1 - log s) := by
    rw [hlog, hc]; ring
  rw [key]
  refine ⟨mul_nonneg ha.le (by linarith [Real.log_le_sub_one_of_pos hspos]), fun h0 => ?_⟩
  have h3 : s - 1 - log s = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h ha.ne'
    · exact h
  have hs1 : s = 1 := by
    by_contra hne
    linarith [Real.log_lt_sub_one_of_pos hspos hne]
  rw [hs] at hs1
  field_simp at hs1
  linarith

/-- Total mass of the conditional-product reference `p(x,d) p(d,r) / p(d)` equals that of `p`. -/
theorem sum_condProd (p : X → D → R → ℝ) (hp : ∀ x d r, 0 < p x d r) :
    ∑ x, ∑ d, ∑ r, mXD p x d * mDR p d r / mD p d = ∑ x, ∑ d, ∑ r, p x d r := by
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => ?_
  rcases isEmpty_or_nonempty R with hR | ⟨⟨r0⟩⟩
  · simp
  have h4 : 0 < mD p d := Finset.sum_pos (fun x _ => Finset.sum_pos (fun r _ => hp x d r)
    ⟨r0, Finset.mem_univ _⟩) ⟨x, Finset.mem_univ _⟩
  have hsum : ∑ r, mDR p d r = mD p d := by
    unfold mDR mD; rw [Finset.sum_comm]
  rw [← Finset.sum_div, ← Finset.mul_sum, hsum, mul_div_assoc, div_self h4.ne', mul_one]
  rfl

/-- Marginals of a strictly positive joint are strictly positive. -/
theorem marg_pos (p : X → D → R → ℝ) (hp : ∀ x d r, 0 < p x d r) (x : X) (d : D) (r : R) :
    0 < mXD p x d ∧ 0 < mDR p d r ∧ 0 < mD p d :=
  ⟨Finset.sum_pos (fun r _ => hp x d r) ⟨r, Finset.mem_univ _⟩,
   Finset.sum_pos (fun x _ => hp x d r) ⟨x, Finset.mem_univ _⟩,
   Finset.sum_pos (fun x _ => Finset.sum_pos (fun r _ => hp x d r) ⟨r, Finset.mem_univ _⟩)
     ⟨x, Finset.mem_univ _⟩⟩

/-- `I(X;R|D)` as a sum of the nonnegative Gibbs gaps of `condMI_term`. -/
theorem condMI_eq_sum_gap (p : X → D → R → ℝ) (hp : ∀ x d r, 0 < p x d r) :
    condMI p = ∑ x, ∑ d, ∑ r, (p x d r * log (p x d r * mD p d / (mXD p x d * mDR p d r))
      - p x d r + mXD p x d * mDR p d r / mD p d) := by
  unfold condMI
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_condProd p hp]
  ring

/-- `I(X;R|D) ≥ 0` for a strictly positive joint (Gibbs). -/
theorem condMI_nonneg (p : X → D → R → ℝ) (hp : ∀ x d r, 0 < p x d r) : 0 ≤ condMI p := by
  rw [condMI_eq_sum_gap p hp]
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun r _ => ?_
  obtain ⟨h1, h2, h3⟩ := marg_pos p hp x d r
  exact (condMI_term _ _ _ _ (hp x d r) h1 h2 h3).1

/-- **A6 (new; going up: the iff).** For a strictly positive joint and positive odds, seeing `R`
leaves the proportional bettor's growth unchanged IFF `R ⟂ X | D`, i.e.
`p(x,d,r) p(d) = p(x,d) p(d,r)` everywhere. So A2 is not just a sufficient condition: independence of
the private randomness (given `D`) is EXACTLY the condition under which it is worthless to the
proportional bettor. (Converse direction uses `I ≥ 0` with equality only at conditional independence.) -/
theorem growthDR_eq_growthD_iff (p : X → D → R → ℝ) (o : X → ℝ) (hp : ∀ x d r, 0 < p x d r)
    (ho : ∀ x, 0 < o x) :
    growthDR p o = growthD p o ↔ ∀ x d r, p x d r * mD p d = mXD p x d * mDR p d r := by
  rw [← sub_eq_zero, growthDR_sub_growthD p o hp ho]
  have hgap : ∀ x d r, 0 ≤ p x d r * log (p x d r * mD p d / (mXD p x d * mDR p d r))
      - p x d r + mXD p x d * mDR p d r / mD p d := fun x d r => by
    obtain ⟨h1, h2, h3⟩ := marg_pos p hp x d r
    exact (condMI_term _ _ _ _ (hp x d r) h1 h2 h3).1
  constructor
  · intro h0 x d r
    rw [condMI_eq_sum_gap p hp] at h0
    have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Finset.sum_nonneg fun d _ =>
      Finset.sum_nonneg fun r _ => hgap x d r)).mp h0 x (Finset.mem_univ x)
    have hd := (Finset.sum_eq_zero_iff_of_nonneg (fun d _ =>
      Finset.sum_nonneg fun r _ => hgap x d r)).mp hx d (Finset.mem_univ d)
    have hr := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => hgap x d r)).mp hd r (Finset.mem_univ r)
    obtain ⟨h1, h2, h3⟩ := marg_pos p hp x d r
    exact (condMI_term _ _ _ _ (hp x d r) h1 h2 h3).2 hr
  · intro h
    unfold condMI
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun r _ => ?_
    obtain ⟨h1, h2, h3⟩ := marg_pos p hp x d r
    rw [h x d r, div_self (by positivity), Real.log_one, mul_zero]

end PartA

section PartB

variable {A : Type*} [Fintype A] [Nonempty A]

/-- Gross expected edge `Σ_a p a * e a`. -/
noncomputable def gross (p e : A → ℝ) : ℝ := ∑ a, p a * e a

/-- The policy-knowing adversary's best single-guess catch `max_b p b * e b`. -/
noncomputable def stolenMax (p e : A → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun b => p b * e b)

/-- Net expected edge against the policy-knowing adversary. -/
noncomputable def net (lam : ℝ) (p e : A → ℝ) : ℝ := gross p e - lam * stolenMax p e

/-- Uniform policy on a finset `S`. -/
noncomputable def unif [DecidableEq A] (S : Finset A) : A → ℝ :=
  fun a => if a ∈ S then (1 : ℝ) / S.card else 0

/-- Point-mass (deterministic) policy on `astar`. -/
def point [DecidableEq A] (astar : A) : A → ℝ := fun a => if a = astar then 1 else 0

/-- Catch of an adversary who SEES the sample `a` and guesses `g a`. -/
noncomputable def informedCatch [DecidableEq A] (p e : A → ℝ) (g : A → A) : ℝ :=
  ∑ a, p a * (if g a = a then e a else 0)


/-! ### Helper lemmas (Part B) -/

theorem gross_point [DecidableEq A] (e : A → ℝ) (astar : A) : gross (point astar) e = e astar := by
  simp [gross, point]

theorem stolenMax_point [DecidableEq A] (e : A → ℝ) (astar : A) (he : 0 ≤ e astar) :
    stolenMax (point astar) e = e astar := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun b _ => ?_
    by_cases h : b = astar
    · subst h; simp [point]
    · simp [point, h, he]
  · calc e astar = point astar astar * e astar := by simp [point]
      _ ≤ _ := Finset.le_sup' (s := Finset.univ) (fun b => point astar b * e b) (Finset.mem_univ astar)

theorem gross_unif [DecidableEq A] (e : A → ℝ) (S : Finset A) (hS : S.Nonempty)
    (E : ℝ) (heS : ∀ a ∈ S, e a = E) : gross (unif S) e = E := by
  have hk : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  unfold gross unif
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_congr rfl
    (fun a ha => by rw [heS a ha] : ∀ a ∈ S, 1 / (S.card : ℝ) * e a = 1 / S.card * E)]
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem stolenMax_unif [DecidableEq A] (e : A → ℝ) (S : Finset A) (hS : S.Nonempty)
    (E : ℝ) (hE : 0 ≤ E) (heS : ∀ a ∈ S, e a = E) : stolenMax (unif S) e = E / S.card := by
  obtain ⟨a0, ha0⟩ := hS
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun b _ => ?_
    by_cases h : b ∈ S
    · simp [unif, h, heS b h, div_eq_inv_mul]
    · simp only [unif, h, ite_false, zero_mul]; positivity
  · have := Finset.le_sup' (s := Finset.univ) (fun b => unif S b * e b) (Finset.mem_univ a0)
    simp only [unif, ha0, ite_true, heS a0 ha0] at this
    unfold stolenMax
    calc E / S.card = 1 / S.card * E := by ring
      _ ≤ _ := this

/-- **B1.** Deterministic policy: net `(1 - lam) * e astar`. -/
theorem net_point_mass [DecidableEq A] (lam : ℝ) (e : A → ℝ) (astar : A) (he : 0 ≤ e astar) :
    net lam (point astar) e = (1 - lam) * e astar := by
  unfold net
  rw [gross_point, stolenMax_point e astar he]
  ring

/-- **B2.** Uniform over `k = #S` equally good actions: the adversary steals only `lam * E / k`. -/
theorem loss_uniform [DecidableEq A] (lam : ℝ) (e : A → ℝ) (S : Finset A) (hS : S.Nonempty)
    (E : ℝ) (hE : 0 ≤ E) (heS : ∀ a ∈ S, e a = E) :
    gross (unif S) e - net lam (unif S) e = lam * E / S.card := by
  unfold net
  rw [stolenMax_unif e S hS E hE heS]
  ring

/-- **B3.** Uniform over `k = #S` equally good actions: net `E * (1 - lam / k)`. -/
theorem net_uniform [DecidableEq A] (lam : ℝ) (e : A → ℝ) (S : Finset A) (hS : S.Nonempty)
    (E : ℝ) (hE : 0 ≤ E) (heS : ∀ a ∈ S, e a = E) :
    net lam (unif S) e = E * (1 - lam / S.card) := by
  unfold net
  rw [stolenMax_unif e S hS E hE heS, gross_unif e S hS E heS]
  ring

/-- **B4.** Mixing protects: same gross `E`, and the mixed loss is the deterministic loss over `k`. -/
theorem mixing_protects [DecidableEq A] (lam : ℝ) (e : A → ℝ) (S : Finset A) (astar : A)
    (hastar : astar ∈ S) (E : ℝ) (hE : 0 ≤ E) (heS : ∀ a ∈ S, e a = E) :
    gross (unif S) e = E ∧ gross (point astar) e = E ∧
    gross (point astar) e - net lam (point astar) e = lam * E ∧
    gross (unif S) e - net lam (unif S) e =
      (gross (point astar) e - net lam (point astar) e) / S.card := by
  have hS : S.Nonempty := ⟨astar, hastar⟩
  have hpE : e astar = E := heS astar hastar
  refine ⟨gross_unif e S hS E heS, by rw [gross_point, hpE], ?_, ?_⟩
  · unfold net
    rw [stolenMax_point e astar (hpE ▸ hE), hpE]
    ring
  · unfold net
    rw [stolenMax_point e astar (hpE ▸ hE), hpE, stolenMax_unif e S hS E hE heS]
    ring

/-- **B5.** An adversary who sees the sample catches at most the gross edge (for `p, e ≥ 0`). -/
theorem informed_catch_le [DecidableEq A] (p e : A → ℝ) (hp : ∀ a, 0 ≤ p a) (he : ∀ a, 0 ≤ e a) (g : A → A) :
    informedCatch p e g ≤ gross p e := by
  unfold informedCatch gross
  refine Finset.sum_le_sum fun a _ => ?_
  split_ifs
  · exact le_rfl
  · rw [mul_zero]; exact mul_nonneg (hp a) (he a)

/-- **B6.** ... and guessing the seen sample catches all of it. -/
theorem informed_catch_id [DecidableEq A] (p e : A → ℝ) : informedCatch p e id = gross p e := by
  simp [informedCatch, gross]

/-- **B7.** Against the informed adversary, the uniform policy loses `lam * E`, the same as the
deterministic one: protection needs the sample to be private. -/
theorem informed_loss_uniform [DecidableEq A] (lam : ℝ) (e : A → ℝ) (S : Finset A) (hS : S.Nonempty)
    (E : ℝ) (heS : ∀ a ∈ S, e a = E) :
    lam * informedCatch (unif S) e id = lam * E := by
  rw [informed_catch_id, gross_unif e S hS E heS]

end PartB

/-! ### Concrete examples (non-vacuity) -/

section Examples

/-- Example `q`: `X` correlated with `D` (both `Bool`). -/
noncomputable def qEx : Bool → Bool → ℝ := fun x d => if x = d then 2/5 else 1/10
/-- Example private coin: biased, `P(true) = 3/10`. -/
noncomputable def uEx : Bool → ℝ := fun r => if r then 3/10 else 7/10

theorem qEx_pos : ∀ x d, 0 < qEx x d := by intro x d; unfold qEx; split_ifs <;> norm_num
theorem uEx_pos : ∀ r, 0 < uEx r := by intro r; unfold uEx; split_ifs <;> norm_num
theorem uEx_sum : ∑ r, uEx r = 1 := by simp [uEx]; norm_num

/-- A1 on the example: the biased private coin carries no information about `X` given `D`. -/
example : condMI (joint qEx uEx) = 0 := condMI_joint_eq_zero qEx uEx uEx_sum

/-- A5 on the example (hypotheses satisfiable, at even odds `2`): any `(D,R)`-strategy is capped. -/
example (b : Bool → Bool → Bool → ℝ) (hb : ∀ d r x, 0 < b d r x) (hb1 : ∀ d r, ∑ x, b d r x ≤ 1) :
    growth (joint qEx uEx) (fun _ => 2) b ≤ growthD (joint qEx uEx) (fun _ => 2) :=
  growth_le_growthD_of_joint qEx uEx _ qEx_pos uEx_pos uEx_sum (fun _ => by norm_num) b hb hb1

/-- A dependent joint (`D = Unit`): `X` and `R` agree with probability `4/5`. -/
noncomputable def pDep : Bool → Unit → Bool → ℝ := fun x _ r => if x = r then 2/5 else 1/10

theorem pDep_pos : ∀ x d r, 0 < pDep x d r := by intro x d r; unfold pDep; split_ifs <;> norm_num

/-- A6 is non-vacuous in the other direction: when `R` is NOT independent, seeing it strictly helps
(`growthDR > growthD`, gap `= I(X;R|D) > 0`). -/
example (o : Bool → ℝ) (ho : ∀ x, 0 < o x) : growthD pDep o < growthDR pDep o := by
  have hne : growthDR pDep o ≠ growthD pDep o := by
    rw [Ne, growthDR_eq_growthD_iff pDep o pDep_pos ho]
    intro h
    have := h true () true
    simp [pDep, mD, mXD, mDR] at this
    norm_num at this
  have h0 : 0 ≤ growthDR pDep o - growthD pDep o := by
    rw [growthDR_sub_growthD pDep o pDep_pos ho]; exact condMI_nonneg pDep pDep_pos
  exact lt_of_le_of_ne (by linarith) (Ne.symm hne)

/-- Part B on `Fin 3`, `lam = 1/2`, all edges `1`: deterministic nets `1/2`, uniform nets `5/6`. -/
example : net (1/2) (point (0 : Fin 3)) (fun _ : Fin 3 => (1 : ℝ)) = 1/2 ∧
    net (1/2) (unif (Finset.univ : Finset (Fin 3))) (fun _ : Fin 3 => (1 : ℝ)) = 5/6 := by
  refine ⟨?_, ?_⟩
  · rw [net_point_mass (1/2 : ℝ) (fun _ : Fin 3 => (1 : ℝ)) 0 (zero_le_one' ℝ)]; norm_num
  · rw [net_uniform (1/2 : ℝ) (fun _ : Fin 3 => (1 : ℝ)) Finset.univ Finset.univ_nonempty 1
      (zero_le_one' ℝ) (fun _ _ => rfl)]
    simp; norm_num

end Examples

end PrivateRandomness
