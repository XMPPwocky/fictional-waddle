import Mathlib

/-!
# E4: logical-time head start and the conditional edge

**What is proved here (pure mathematics, no physics):**

* (1) *Head start.* For a computation of depth `d` run at speeds `cA` (fast, A) and `cB` (slow, B),
  `headStart d cA cB := d / cB - d / cA`. It is `≥ 0` when `d ≥ 0` and `0 < cB ≤ cA`
  (strictly positive when `d > 0`, `cB < cA`), it is linear in `d`, it is monotone (strictly, for
  `d > 0`) increasing in `cA` on `cA > 0`, and it is bounded above by `d / cB`.
* (2) *Conditional edge.* For a strictly positive (not necessarily normalised) joint weight
  `p x y z` on finite types (outcome `X`, A's extra information `Y`, shared information `Z`), with
  conditional mutual information `condMI p` defined by explicit finite sums, the Kelly growth rate of
  a bettor who sees `(Y, Z)` minus that of a bettor who sees only `Z` equals `condMI p`; each Kelly
  bet is optimal among all strategies measurable in its information; hence `condMI p ≥ 0`, and no
  strategy of B gets within less than `condMI p` of A's optimal growth.
* (3) *No edge.* If `p` is supported on the graph of a function `f : Z → Y` (so `Y = f(Z)` a.s.:
  B can compute everything A knows), then `condMI p = 0` and the two Kelly growth rates coincide.
  This part needs no positivity (and cannot have it: a positive `p` on a graph forces `|Y| = 1`); it
  uses Mathlib's conventions `x / 0 = 0`, `log 0 = 0`, which make `0 * log(…) = 0` automatic.
* (4) *Going up: zero edge iff conditional independence.* For strictly positive `p`,
  `condMI p = 0 ↔ ∀ x y z, p x y z * pZ p z = pXZ p x z * pYZ p y z` (`condMI_eq_zero_iff`).
  This is the right converse-strength version of (3) in the positive regime, where (3)'s graph
  hypothesis is unavailable. Proof: pointwise `p − q ≤ p log(p/q)` against the product law
  `q = p(x,z)p(y,z)/p(z)`, strict where `p ≠ q`, and `∑ q = ∑ p`.
* *Non-vacuity.* `headStart 6 3 2 = 1`; a normalised noisy copy (`Y = X` w.p. 4/5, `Z` trivial)
  satisfies every positivity hypothesis and has strictly positive Kelly edge at any positive odds
  (`noisyCopy_edge_pos`); (3) is instantiated with a two-element `Y := Z`.

**What is interpretation (not proved):** that `d / c` models the physical time to reach logical
depth `d`, that the head start is "converted" into an informational edge `Y` the slower party lacks
at decision time, and that the Kelly growth rate is the right currency for "edge". In (3), the bets `kellyA`,
`kellyB` are still the posterior bets, but Kelly *optimality* is only proved under positivity (2). The Lean only
checks the arithmetic and the information identities above. Logs are natural.
-/

open Finset Real

namespace EdgeHeadStart

/-! ## (1) Head start in physical time -/

/-- Physical-time head start of A (speed `cA`) over B (speed `cB`) at logical depth `d`. -/
noncomputable def headStart (d cA cB : ℝ) : ℝ := d / cB - d / cA

/-- **Proved.** The head start is nonnegative for `d ≥ 0` and `0 < cB ≤ cA`. -/
theorem headStart_nonneg {d cA cB : ℝ} (hd : 0 ≤ d) (hB : 0 < cB) (hBA : cB ≤ cA) :
    0 ≤ headStart d cA cB := by
  unfold headStart
  have : d / cA ≤ d / cB := div_le_div_of_nonneg_left hd hB hBA
  linarith

/-- **Proved.** Strictly positive head start for `d > 0` and `0 < cB < cA`. -/
theorem headStart_pos {d cA cB : ℝ} (hd : 0 < d) (hB : 0 < cB) (hBA : cB < cA) :
    0 < headStart d cA cB := by
  unfold headStart
  have : d / cA < d / cB := div_lt_div_of_pos_left hd hB hBA
  linarith

/-- **Proved.** Linear in depth: `headStart d = d · (1/cB − 1/cA)` (no hypotheses needed). -/
theorem headStart_eq_mul (d cA cB : ℝ) : headStart d cA cB = d * (1 / cB - 1 / cA) := by
  unfold headStart; ring

/-- **Proved.** Linear in depth, as an additivity/homogeneity statement. -/
theorem headStart_linear (a d d' cA cB : ℝ) :
    headStart (a * d + d') cA cB = a * headStart d cA cB + headStart d' cA cB := by
  simp only [headStart_eq_mul]; ring

/-- **Proved.** Monotone increasing in the fast speed `cA` (for `d ≥ 0`, `0 < cA ≤ cA'`). -/
theorem headStart_mono_cA {d cA cA' cB : ℝ} (hd : 0 ≤ d) (hA : 0 < cA) (hAA : cA ≤ cA') :
    headStart d cA cB ≤ headStart d cA' cB := by
  unfold headStart
  have : d / cA' ≤ d / cA := div_le_div_of_nonneg_left hd hA hAA
  linarith

/-- **Proved.** Strictly increasing in `cA` on `(0, ∞)` when `d > 0`. -/
theorem headStart_strictMonoOn_cA {d cB : ℝ} (hd : 0 < d) :
    StrictMonoOn (fun c => headStart d c cB) (Set.Ioi 0) := by
  intro a ha b _ hab
  simp only [headStart]
  have : d / b < d / a := div_lt_div_of_pos_left hd ha hab
  linarith

/-- **Proved.** The head start never exceeds B's own run time `d / cB` (for `d ≥ 0`, `cA > 0`). -/
theorem headStart_le {d cA cB : ℝ} (hd : 0 ≤ d) (hA : 0 < cA) : headStart d cA cB ≤ d / cB := by
  unfold headStart
  have : 0 ≤ d / cA := div_nonneg hd hA.le
  linarith

/-! ## (2) Conditional edge = conditional mutual information -/

variable {ι X Y Z : Type*} [Fintype ι] [Fintype X] [Fintype Y] [Fintype Z]

set_option linter.unusedSectionVars false

/-- Marginal weight of `Z`. -/
noncomputable def pZ (p : X → Y → Z → ℝ) (z : Z) : ℝ := ∑ x, ∑ y, p x y z
/-- Marginal weight of `(X, Z)`. -/
noncomputable def pXZ (p : X → Y → Z → ℝ) (x : X) (z : Z) : ℝ := ∑ y, p x y z
/-- Marginal weight of `(Y, Z)`. -/
noncomputable def pYZ (p : X → Y → Z → ℝ) (y : Y) (z : Z) : ℝ := ∑ x, p x y z

/-- Conditional mutual information `I(X; Y | Z)`, by explicit finite sums. -/
noncomputable def condMI (p : X → Y → Z → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, p x y z * log (p x y z * pZ p z / (pXZ p x z * pYZ p y z))

/-- Expected log growth, at odds `o`, of a bettor who sees `(y, z)` and bets fractions `b y z x`. -/
noncomputable def growthYZ (p : X → Y → Z → ℝ) (o : X → ℝ) (b : Y → Z → X → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, p x y z * log (b y z x * o x)

/-- Expected log growth, at odds `o`, of a bettor who sees only `z` and bets fractions `b z x`. -/
noncomputable def growthZ (p : X → Y → Z → ℝ) (o : X → ℝ) (b : Z → X → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, p x y z * log (b z x * o x)

/-- A's Kelly bet: the posterior `p(x | y, z)`. -/
noncomputable def kellyA (p : X → Y → Z → ℝ) (y : Y) (z : Z) (x : X) : ℝ := p x y z / pYZ p y z
/-- B's Kelly bet: the posterior `p(x | z)`. -/
noncomputable def kellyB (p : X → Y → Z → ℝ) (z : Z) (x : X) : ℝ := pXZ p x z / pZ p z

lemma pXZ_pos {p : X → Y → Z → ℝ} (hp : ∀ x y z, 0 < p x y z) (x : X) (y : Y) (z : Z) :
    0 < pXZ p x z :=
  lt_of_lt_of_le (hp x y z)
    (Finset.single_le_sum (f := fun y' => p x y' z) (fun y' _ => (hp x y' z).le) (Finset.mem_univ y))

lemma pYZ_pos {p : X → Y → Z → ℝ} (hp : ∀ x y z, 0 < p x y z) (x : X) (y : Y) (z : Z) :
    0 < pYZ p y z :=
  lt_of_lt_of_le (hp x y z)
    (Finset.single_le_sum (f := fun x' => p x' y z) (fun x' _ => (hp x' y z).le) (Finset.mem_univ x))

lemma pZ_pos {p : X → Y → Z → ℝ} (hp : ∀ x y z, 0 < p x y z) (x : X) (y : Y) (z : Z) :
    0 < pZ p z :=
  lt_of_lt_of_le (pXZ_pos hp x y z)
    (Finset.single_le_sum (f := fun x' => pXZ p x' z)
      (fun x' _ => (pXZ_pos hp x' y z).le) (Finset.mem_univ x))

/-- Gibbs' inequality, unnormalised, with odds: for positive weights `a`, the bet `a / ∑ a` beats
every positive bet `b` with `∑ b ≤ 1`. -/
lemma gibbs_odds (a b o : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (ho : ∀ i, 0 < o i)
    (hb1 : ∑ i, b i ≤ 1) :
    ∑ i, a i * log (b i * o i) ≤ ∑ i, a i * log (a i / (∑ j, a j) * o i) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  set S := ∑ j, a j with hS
  have hS0 : 0 < S := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have key : ∀ i, a i * log (b i * o i) - a i * log (a i / S * o i) ≤ S * b i - a i := by
    intro i
    have hq : 0 < a i / S := div_pos (ha i) hS0
    have h := log_le_sub_one_of_pos (div_pos (hb i) hq)
    rw [log_div (hb i).ne' hq.ne'] at h
    have e : a i * log (b i * o i) - a i * log (a i / S * o i) = a i * (log (b i) - log (a i / S)) := by
      rw [log_mul (hb i).ne' (ho i).ne', log_mul hq.ne' (ho i).ne']; ring
    have h2 : a i * (log (b i) - log (a i / S)) ≤ a i * (b i / (a i / S) - 1) :=
      mul_le_mul_of_nonneg_left h (ha i).le
    have e2 : a i * (b i / (a i / S) - 1) = S * b i - a i := by
      have := (ha i).ne'; have := hS0.ne'; field_simp
    linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hS] at hsum
  have : S * ∑ i, b i ≤ S := by nlinarith
  linarith

/-- Reorder `∑ x ∑ y ∑ z` to `∑ y ∑ z ∑ x`. -/
lemma sum_xyz_to_yzx (F : X → Y → Z → ℝ) : ∑ x, ∑ y, ∑ z, F x y z = ∑ y, ∑ z, ∑ x, F x y z := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]

/-- Reorder `∑ x ∑ y ∑ z` to `∑ z ∑ x ∑ y`. -/
lemma sum_xyz_to_zxy (F : X → Y → Z → ℝ) : ∑ x, ∑ y, ∑ z, F x y z = ∑ z, ∑ x, ∑ y, F x y z := by
  have : ∀ x, ∑ y, ∑ z, F x y z = ∑ z, ∑ y, F x y z := fun x => Finset.sum_comm
  simp_rw [this]
  rw [Finset.sum_comm]

/-- **Proved (Kelly for A).** Among all positive strategies `b y z ·` with `∑ₓ b y z x ≤ 1` for every
observation `(y, z)`, the posterior bet `kellyA p` maximises expected log growth. -/
theorem kellyA_optimal (p : X → Y → Z → ℝ) (o : X → ℝ) (b : Y → Z → X → ℝ)
    (hp : ∀ x y z, 0 < p x y z) (ho : ∀ x, 0 < o x) (hb : ∀ y z x, 0 < b y z x)
    (hb1 : ∀ y z, ∑ x, b y z x ≤ 1) :
    growthYZ p o b ≤ growthYZ p o (kellyA p) := by
  unfold growthYZ kellyA
  rw [sum_xyz_to_yzx, sum_xyz_to_yzx (fun x y z => p x y z * log (p x y z / pYZ p y z * o x))]
  refine Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun z _ => ?_))
  exact gibbs_odds (fun x => p x y z) (fun x => b y z x) o (fun x => hp x y z) (fun x => hb y z x) ho
    (hb1 y z)

/-- **Proved (Kelly for B).** Among all positive strategies `b z ·` with `∑ₓ b z x ≤ 1` for every
observation `z`, the posterior bet `kellyB p` maximises expected log growth. -/
theorem kellyB_optimal (p : X → Y → Z → ℝ) (o : X → ℝ) (b : Z → X → ℝ)
    (hp : ∀ x y z, 0 < p x y z) (ho : ∀ x, 0 < o x) (hb : ∀ z x, 0 < b z x)
    (hb1 : ∀ z, ∑ x, b z x ≤ 1) :
    growthZ p o b ≤ growthZ p o (kellyB p) := by
  have hcollapse : ∀ c : Z → X → ℝ, growthZ p o c = ∑ z, ∑ x, pXZ p x z * log (c z x * o x) := by
    intro c
    unfold growthZ
    rw [sum_xyz_to_zxy]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro x _
    rw [pXZ, Finset.sum_mul]
  rw [hcollapse, hcollapse]
  refine Finset.sum_le_sum (fun z _ => ?_)
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y0⟩⟩
  · simp [pXZ]
  have := gibbs_odds (fun x => pXZ p x z) (fun x => b z x) o (fun x => pXZ_pos hp x y0 z)
    (fun x => hb z x) ho (hb1 z)
  simpa [kellyB, pZ, pXZ] using this

/-- **Proved (the conditional edge).** The Kelly growth rate with `(Y, Z)` minus the Kelly growth rate
with `Z` alone is exactly the conditional mutual information `I(X; Y | Z)`. -/
theorem conditional_edge (p : X → Y → Z → ℝ) (o : X → ℝ)
    (hp : ∀ x y z, 0 < p x y z) (ho : ∀ x, 0 < o x) :
    growthYZ p o (kellyA p) - growthZ p o (kellyB p) = condMI p := by
  unfold growthYZ growthZ condMI kellyA kellyB
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro x _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro y _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro z _
  have h0 := hp x y z
  have h1 := pXZ_pos hp x y z
  have h2 := pYZ_pos hp x y z
  have h3 := pZ_pos hp x y z
  have h4 := ho x
  rw [← mul_sub, ← log_div (mul_pos (div_pos h0 h2) h4).ne' (mul_pos (div_pos h1 h3) h4).ne']
  congr 2
  field_simp

/-- **Proved.** Conditional mutual information is nonnegative (for strictly positive weights; no
normalisation needed). Proof: B's Kelly bet is one of A's admissible strategies, so by
`kellyA_optimal` and `conditional_edge`. -/
theorem condMI_nonneg (p : X → Y → Z → ℝ) (hp : ∀ x y z, 0 < p x y z) : 0 ≤ condMI p := by
  have hb : ∀ y z x, 0 < kellyB p z x := fun y z x => div_pos (pXZ_pos hp x y z) (pZ_pos hp x y z)
  rcases isEmpty_or_nonempty X with hXe | ⟨⟨x0⟩⟩
  · simp [condMI]
  have hb1 : ∀ (y : Y) (z : Z), ∑ x, kellyB p z x ≤ 1 := by
    intro y z
    apply le_of_eq
    unfold kellyB
    rw [← Finset.sum_div]
    exact div_self (pZ_pos hp (x0) y z).ne'
  have hopt := kellyA_optimal p (fun _ => 1) (fun _ z x => kellyB p z x) hp (fun _ => one_pos)
    (fun y z x => hb y z x) hb1
  have hedge := conditional_edge p (fun _ => 1) hp (fun _ => one_pos)
  have : growthYZ p (fun _ => 1) (fun _ z x => kellyB p z x) = growthZ p (fun _ => 1) (kellyB p) := rfl
  linarith

/-- **Proved (the edge bounds every strategy of B).** Whatever admissible strategy B uses with only `Z`,
its growth is at most A's Kelly growth minus `I(X; Y | Z)`. -/
theorem edge_over_any_B (p : X → Y → Z → ℝ) (o : X → ℝ) (b : Z → X → ℝ)
    (hp : ∀ x y z, 0 < p x y z) (ho : ∀ x, 0 < o x) (hb : ∀ z x, 0 < b z x)
    (hb1 : ∀ z, ∑ x, b z x ≤ 1) :
    growthZ p o b ≤ growthYZ p o (kellyA p) - condMI p := by
  have h1 := kellyB_optimal p o b hp ho hb hb1
  have h2 := conditional_edge p o hp ho
  linarith

/-! ## (3) No edge when B can compute A's information -/

/-- `a · log(c / c) = 0` for every real `c` (using `0 / 0 = 0`, `log 0 = 0`). -/
lemma mul_log_self_div_self (a c : ℝ) : a * log (c / c) = 0 := by
  rcases eq_or_ne c 0 with h | h
  · rw [h, zero_div, log_zero, mul_zero]
  · rw [div_self h, log_one, mul_zero]

/-- **Proved.** If `p` vanishes off the graph of `f : Z → Y` (A's information is a function of B's),
then `I(X; Y | Z) = 0`. No positivity or normalisation is assumed. -/
theorem condMI_eq_zero_of_function (p : X → Y → Z → ℝ) (f : Z → Y)
    (hsupp : ∀ x y z, y ≠ f z → p x y z = 0) : condMI p = 0 := by
  have hXZ : ∀ x z, pXZ p x z = p x (f z) z := by
    intro x z
    unfold pXZ
    rw [Finset.sum_eq_single (f z) (fun y _ hy => hsupp x y z hy) (by simp)]
  have hZ : ∀ z, pZ p z = pYZ p (f z) z := by
    intro z
    unfold pZ pYZ
    apply Finset.sum_congr rfl
    intro x _
    exact hXZ x z
  unfold condMI
  apply Finset.sum_eq_zero; intro x _
  apply Finset.sum_eq_zero; intro y _
  apply Finset.sum_eq_zero; intro z _
  by_cases hy : y = f z
  · subst hy
    rw [hXZ, hZ, mul_log_self_div_self]
  · rw [hsupp x y z hy, zero_mul]

/-- **Proved.** Under the same support condition, A's and B's Kelly growth rates coincide (at any odds):
seeing `Y` in addition to `Z` gives no edge. -/
theorem no_edge_of_function (p : X → Y → Z → ℝ) (o : X → ℝ) (f : Z → Y)
    (hsupp : ∀ x y z, y ≠ f z → p x y z = 0) :
    growthYZ p o (kellyA p) = growthZ p o (kellyB p) := by
  have hXZ : ∀ x z, pXZ p x z = p x (f z) z := by
    intro x z
    unfold pXZ
    rw [Finset.sum_eq_single (f z) (fun y _ hy => hsupp x y z hy) (by simp)]
  have hZ : ∀ z, pZ p z = pYZ p (f z) z := by
    intro z
    unfold pZ pYZ
    apply Finset.sum_congr rfl
    intro x _
    exact hXZ x z
  unfold growthYZ growthZ kellyA kellyB
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  apply Finset.sum_congr rfl; intro z _
  by_cases hy : y = f z
  · subst hy
    rw [hXZ, hZ]
  · rw [hsupp x y z hy, zero_mul, zero_mul]

open Classical in
/-- The joint law obtained from a weight `q` on `X × Z` by letting A's information be `Y := f Z`. -/
noncomputable def liftFn (q : X → Z → ℝ) (f : Z → Y) (x : X) (y : Y) (z : Z) : ℝ :=
  if y = f z then q x z else 0

/-- **Proved.** For any `q` and any `f`, the lifted law with `Y = f(Z)` has zero conditional edge. -/
theorem condMI_liftFn (q : X → Z → ℝ) (f : Z → Y) : condMI (liftFn q f) = 0 :=
  condMI_eq_zero_of_function _ f (fun x y z hy => by simp [liftFn, hy])

/-! ## (4) Going up: the edge vanishes *exactly* under conditional independence

Part (3) gives one sufficient condition for "no edge" (`Y` a function of `Z`). For strictly positive
`p` (where (3)'s hypothesis would force `|Y| = 1`), the right statement is an `iff`: the edge is zero
if and only if `X ⊥ Y | Z`, i.e. `p(x,y,z) p(z) = p(x,z) p(y,z)` everywhere. -/

/-- Pointwise `a − c ≤ a log(a/c)` for `a, c > 0`. -/
lemma sub_le_mul_log_div {a c : ℝ} (ha : 0 < a) (hc : 0 < c) : a - c ≤ a * log (a / c) := by
  have h := log_le_sub_one_of_pos (div_pos hc ha)
  rw [log_div hc.ne' ha.ne'] at h
  rw [log_div ha.ne' hc.ne']
  have h2 := mul_le_mul_of_nonneg_left h ha.le
  have e : a * (c / a - 1) = c - a := by field_simp
  nlinarith

/-- Pointwise strict version: `a − c < a log(a/c)` when moreover `a ≠ c`. -/
lemma sub_lt_mul_log_div {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hne : a ≠ c) :
    a - c < a * log (a / c) := by
  have hne' : c / a ≠ 1 := by
    intro h; apply hne; field_simp at h; linarith
  have h := log_lt_sub_one_of_pos (div_pos hc ha) hne'
  rw [log_div hc.ne' ha.ne'] at h
  rw [log_div ha.ne' hc.ne']
  have h2 := mul_lt_mul_of_pos_left h ha
  have e : a * (c / a - 1) = c - a := by field_simp
  nlinarith

/-- **Proved (going up: the edge is zero iff conditional independence).** For strictly positive
(not necessarily normalised) `p`, `I(X; Y | Z) = 0` if and only if `X` and `Y` are conditionally
independent given `Z`: `p(x,y,z) · p(z) = p(x,z) · p(y,z)` for all `x, y, z`. Combined with
`conditional_edge`: A's Kelly advantage over B vanishes exactly when `Y` carries no information about
`X` beyond `Z`. -/
theorem condMI_eq_zero_iff (p : X → Y → Z → ℝ) (hp : ∀ x y z, 0 < p x y z) :
    condMI p = 0 ↔ ∀ x y z, p x y z * pZ p z = pXZ p x z * pYZ p y z := by
  constructor
  · intro h0
    by_contra hne
    push Not at hne
    obtain ⟨x0, y0, z0, hne⟩ := hne
    -- the product law `q`
    set q : X → Y → Z → ℝ := fun x y z => pXZ p x z * pYZ p y z / pZ p z with hq
    have hqpos : ∀ x y z, 0 < q x y z := fun x y z =>
      div_pos (mul_pos (pXZ_pos hp x y z) (pYZ_pos hp x y z)) (pZ_pos hp x y z)
    have hterm : ∀ x y z, p x y z * log (p x y z * pZ p z / (pXZ p x z * pYZ p y z))
        = p x y z * log (p x y z / q x y z) := by
      intro x y z; simp only [hq, div_div_eq_mul_div]
    -- total mass of `q` equals total mass of `p`
    have hmass : ∑ x, ∑ y, ∑ z, q x y z = ∑ x, ∑ y, ∑ z, p x y z := by
      rw [sum_xyz_to_zxy q, sum_xyz_to_zxy p]
      apply Finset.sum_congr rfl; intro z _
      rcases isEmpty_or_nonempty X with hX | ⟨⟨x1⟩⟩
      · simp
      rcases isEmpty_or_nonempty Y with hY | ⟨⟨y1⟩⟩
      · simp
      have hZ0 := (pZ_pos hp x1 y1 z).ne'
      have hYsum : ∑ y, pYZ p y z = pZ p z := by
        unfold pYZ pZ; rw [Finset.sum_comm]
      have : ∀ x, ∑ y, q x y z = pXZ p x z := by
        intro x
        simp only [hq, ← Finset.sum_div, ← Finset.mul_sum, hYsum]
        field_simp
      simp only [this]
      rfl
    have hlt : ∑ x, ∑ y, ∑ z, (p x y z - q x y z) < condMI p := by
      unfold condMI
      simp only [hterm]
      refine Finset.sum_lt_sum (fun x _ => Finset.sum_le_sum (fun y _ => Finset.sum_le_sum
        (fun z _ => sub_le_mul_log_div (hp x y z) (hqpos x y z)))) ⟨x0, Finset.mem_univ _, ?_⟩
      refine Finset.sum_lt_sum (fun y _ => Finset.sum_le_sum
        (fun z _ => sub_le_mul_log_div (hp x0 y z) (hqpos x0 y z))) ⟨y0, Finset.mem_univ _, ?_⟩
      refine Finset.sum_lt_sum (fun z _ => sub_le_mul_log_div (hp x0 y0 z) (hqpos x0 y0 z))
        ⟨z0, Finset.mem_univ _, ?_⟩
      refine sub_lt_mul_log_div (hp x0 y0 z0) (hqpos x0 y0 z0) ?_
      intro heq
      apply hne
      have := (pZ_pos hp x0 y0 z0).ne'
      rw [heq, hq]; field_simp
    have hzero : ∑ x, ∑ y, ∑ z, (p x y z - q x y z) = 0 := by
      simp only [Finset.sum_sub_distrib]; rw [hmass]; ring
    linarith
  · intro hci
    unfold condMI
    apply Finset.sum_eq_zero; intro x _
    apply Finset.sum_eq_zero; intro y _
    apply Finset.sum_eq_zero; intro z _
    rw [hci, div_self (mul_pos (pXZ_pos hp x y z) (pYZ_pos hp x y z)).ne', log_one, mul_zero]

/-! ## Concrete examples (non-vacuity) -/

/-- Head start, concretely: depth 6 at speeds 3 (A) and 2 (B): B needs 3, A needs 2, head start 1. -/
example : headStart 6 3 2 = 1 := by norm_num [headStart]

/-- A noisy copy: `Z` is trivial, `Y` agrees with the outcome `X` with probability 4/5. -/
noncomputable def noisyCopy (x y : Bool) (_ : Unit) : ℝ := if x = y then 2 / 5 else 1 / 10

lemma noisyCopy_pos : ∀ x y z, 0 < noisyCopy x y z := by
  intro x y z; unfold noisyCopy; split_ifs <;> norm_num

/-- **Proved (non-vacuity of (2) and (4)).** The noisy copy is *not* conditionally independent, so
its edge is strictly positive: at any positive odds, A (who sees `Y`) strictly out-grows B. -/
theorem noisyCopy_edge_pos (o : Bool → ℝ) (ho : ∀ x, 0 < o x) :
    0 < growthYZ noisyCopy o (kellyA noisyCopy) - growthZ noisyCopy o (kellyB noisyCopy) := by
  rw [conditional_edge _ _ noisyCopy_pos ho]
  refine lt_of_le_of_ne (condMI_nonneg _ noisyCopy_pos) (fun h => ?_)
  have := ((condMI_eq_zero_iff _ noisyCopy_pos).1 h.symm) true true ()
  simp [noisyCopy, pZ, pXZ, pYZ] at this
  norm_num at this

/-- Non-vacuity of (3) with a two-element `Y`: `Y := Z` copied, `X` arbitrary — zero edge. -/
example (q : Bool → Bool → ℝ) : condMI (liftFn q (id : Bool → Bool)) = 0 := condMI_liftFn q id

end EdgeHeadStart
