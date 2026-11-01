import Mathlib

/-!
# F1: edge decomposition by the chain rule (finite) -- PROOFS

All information quantities are explicit finite sums with natural log.
`cmi q` is the conditional mutual information `I(A;B|C)` of a (not necessarily
normalised, nonnegative) weight function `q : A → B → C → ℝ`, with marginals
obtained by summation. Lean's `Real.log 0 = 0` and `0 * _ = 0` give the usual
`0 log 0 = 0` convention for zero-weight cells.

Setting: outcome `X`, public data `D`, private observation `O`, a strictly
positive joint `p : X → D → O → ℝ`, and a rival's summary `c : D → K`.
The coarse variable `K = c(D)` is realised by pushing `p` forward to explicit
joints (`jXDO_K`, `jXD_K`, `jXO_DK`) that put zero weight off the graph of `c`.

## What is PROVED (Lean, no sorry)
* `chain_rule`: `I(X;(D,O)|c D) = I(X;D|c D) + I(X;O|D,c D)` for strictly positive `p`
  (normalisation `Σ p = 1` is not needed; any positive weights work).
* `cmi_public_zero_of_injective`: `I(X;D|c D) = 0` when `c` is injective.
* `chain_rule_injective`: hence the whole edge equals the private term `I(X;O|D,c D)`.
* `cmi_eq_entropies`: for nonnegative weights, `I(A;B|C) = H(A,C)+H(B,C)-H(A,B,C)-H(C)`,
  tying the `cmi` definition to the explicit entropy sums.
* (added, second agent) `cmi_nonneg`: Gibbs inequality, `0 ≤ I(A;B|C)` for any nonnegative
  weights (proof via `log x ≥ 1 - 1/x`, no normalisation needed).
* (added, corollary) `private_le_edge`: `I(X;O|D,c D) ≤ I(X;(D,O)|c D)`.
* (added, non-vacuity) `pEx`, `pEx_pos`, `example_coarse_public_pos`: an explicit strictly
  positive joint on `Bool × Bool × Unit` with a constant summary `c`, where
  `I(X;D|c D) = 2 log(32/27) > 0`. So hypotheses are satisfiable and injectivity in
  `cmi_public_zero_of_injective` cannot be dropped.

## What is INTERPRETED (not proved; reading of the theorems)
* Reading `D` as public data, `O` as a private observation, and `c` as "the rival's
  computable summary" is narrative. Nothing here models computability: `c` is an
  arbitrary function, and "injective" is the formal stand-in for "the rival can
  compute everything about `D`".
* The "edge" language (information flowing from `(D,O)` to `X` splits into a part the
  rival's summary misses in `D` plus a private part) is an interpretation of the chain rule.
* Note `I(X;O|D,c D)` here is literally `I(X;O|D)`, since `c D` is a function of `D`;
  the `(D, K)` conditioning variable is kept explicit for faithfulness to the target.
* Scaling: `cmi` is positively homogeneous of degree 1 (`cmi (Z • q) = Z * cmi q`; this is
  NOT proved here, it is a reading of the formula). For `Σ p = Z`, the stated quantities are
  `Z` times the Shannon CMIs (nats) of `p / Z`, so all identities and the sign result
  transfer to the normalised distribution.
-/

open Finset

namespace F1

noncomputable section

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- Marginal of the conditioning variable. -/
def margC (q : A → B → C → ℝ) (c : C) : ℝ := ∑ a, ∑ b, q a b c
/-- Marginal of `(A, C)`. -/
def margAC (q : A → B → C → ℝ) (a : A) (c : C) : ℝ := ∑ b, q a b c
/-- Marginal of `(B, C)`. -/
def margBC (q : A → B → C → ℝ) (b : B) (c : C) : ℝ := ∑ a, q a b c

/-- Conditional mutual information `I(A;B|C) = Σ q log (q · q_C / (q_AC · q_BC))`. -/
def cmi (q : A → B → C → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, q a b c * Real.log (q a b c * margC q c / (margAC q a c * margBC q b c))

/-- Shannon entropy (natural log) of a finite weight function. -/
def entropy {S : Type*} [Fintype S] (r : S → ℝ) : ℝ := -∑ s, r s * Real.log (r s)

variable {X D O K : Type*} [Fintype X] [Fintype D] [Fintype O] [Fintype K]
  [DecidableEq K]

/-- Joint of `(X, (D,O), K)` with `K = c D`. -/
def jXDO_K (p : X → D → O → ℝ) (c : D → K) : X → D × O → K → ℝ :=
  fun x dO k => if c dO.1 = k then p x dO.1 dO.2 else 0

/-- Joint of `(X, D, K)` with `K = c D` (`O` summed out). -/
def jXD_K (p : X → D → O → ℝ) (c : D → K) : X → D → K → ℝ :=
  fun x d k => if c d = k then ∑ o, p x d o else 0

/-- Joint of `(X, O, (D,K))` with `K = c D`. -/
def jXO_DK (p : X → D → O → ℝ) (c : D → K) : X → O → D × K → ℝ :=
  fun x o dk => if c dk.1 = dk.2 then p x dk.1 o else 0


/-! ### Helper lemmas (not part of the target statements) -/

omit [Fintype K] [DecidableEq K] in
lemma ite_mul_log {P : Prop} [Decidable P] (a m n r : ℝ) :
    (if P then a else 0) * Real.log ((if P then a else 0) * m / (n * r))
      = if P then a * Real.log (a * m / (n * r)) else 0 := by
  split_ifs <;> simp

/-- Reduced form of `I(X;(D,O)|c D)`. -/
lemma cmi1_eq (p : X → D → O → ℝ) (c : D → K) :
    cmi (jXDO_K p c) = ∑ x, ∑ d, ∑ o, p x d o *
      Real.log (p x d o * margC (jXD_K p c) (c d) /
        (margAC (jXD_K p c) x (c d) * ∑ x', p x' d o)) := by
  have hC : ∀ k, margC (jXDO_K p c) k = margC (jXD_K p c) k := by
    intro k
    simp only [margC, jXDO_K, jXD_K, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  have hAC : ∀ x k, margAC (jXDO_K p c) x k = margAC (jXD_K p c) x k := by
    intro x k
    simp only [margAC, jXDO_K, jXD_K, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  have hBC : ∀ d o, margBC (jXDO_K p c) (d, o) (c d) = ∑ x', p x' d o := by
    intro d o; simp [margBC, jXDO_K]
  unfold cmi
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun o _ => ?_
  simp only [hC, hAC]
  have : ∀ k, jXDO_K p c x (d, o) k = if c d = k then p x d o else 0 := fun _ => rfl
  simp only [this, ite_mul_log, Finset.sum_ite_eq, Finset.mem_univ, ite_true, hBC]

/-- Reduced form of `I(X;D|c D)`. -/
lemma cmi2_eq (p : X → D → O → ℝ) (c : D → K) :
    cmi (jXD_K p c) = ∑ x, ∑ d, (∑ o, p x d o) *
      Real.log ((∑ o, p x d o) * margC (jXD_K p c) (c d) /
        (margAC (jXD_K p c) x (c d) * ∑ x', ∑ o, p x' d o)) := by
  have hBC : ∀ d, margBC (jXD_K p c) d (c d) = ∑ x', ∑ o, p x' d o := by
    intro d; simp [margBC, jXD_K]
  unfold cmi
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => ?_
  have : ∀ k, jXD_K p c x d k = if c d = k then ∑ o, p x d o else 0 := fun _ => rfl
  simp only [this, ite_mul_log, Finset.sum_ite_eq, Finset.mem_univ, ite_true, hBC]

/-- Reduced form of `I(X;O|D, c D)`. -/
lemma cmi3_eq (p : X → D → O → ℝ) (c : D → K) :
    cmi (jXO_DK p c) = ∑ x, ∑ d, ∑ o, p x d o *
      Real.log (p x d o * (∑ x', ∑ o', p x' d o') /
        ((∑ o', p x d o') * ∑ x', p x' d o)) := by
  have hC : ∀ d, margC (jXO_DK p c) (d, c d) = ∑ x', ∑ o', p x' d o' := by
    intro d; simp [margC, jXO_DK]
  have hAC : ∀ x d, margAC (jXO_DK p c) x (d, c d) = ∑ o', p x d o' := by
    intro x d; simp [margAC, jXO_DK]
  have hBC : ∀ o d, margBC (jXO_DK p c) o (d, c d) = ∑ x', p x' d o := by
    intro o d; simp [margBC, jXO_DK]
  unfold cmi
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun o _ => ?_
  have : ∀ k, jXO_DK p c x o (d, k) = if c d = k then p x d o else 0 := fun _ => rfl
  simp only [this, ite_mul_log, Finset.sum_ite_eq, Finset.mem_univ, ite_true, hC, hAC, hBC]

omit [Fintype X] [Fintype K] in
lemma margAC_pos (p : X → D → O → ℝ) (hp : ∀ x d o, 0 < p x d o) (c : D → K)
    (x : X) (d : D) (o : O) : 0 < margAC (jXD_K p c) x (c d) := by
  have hrow : 0 < ∑ o', p x d o' :=
    Finset.sum_pos (fun o' _ => hp x d o') ⟨o, Finset.mem_univ _⟩
  have hnn : ∀ d' ∈ (Finset.univ : Finset D), 0 ≤ jXD_K p c x d' (c d) := by
    intro d' _; unfold jXD_K; split_ifs
    · exact Finset.sum_nonneg fun o' _ => (hp x d' o').le
    · exact le_refl 0
  have := Finset.single_le_sum hnn (Finset.mem_univ d)
  simp only [jXD_K, ite_true] at this
  exact lt_of_lt_of_le hrow (by simpa [margAC, jXD_K] using this)

omit [Fintype K] in
lemma margC_pos (p : X → D → O → ℝ) (hp : ∀ x d o, 0 < p x d o) (c : D → K)
    (x : X) (d : D) (o : O) : 0 < margC (jXD_K p c) (c d) := by
  have hnn : ∀ x' ∈ (Finset.univ : Finset X), 0 ≤ margAC (jXD_K p c) x' (c d) := by
    intro x' _
    refine Finset.sum_nonneg fun d' _ => ?_
    unfold jXD_K; split_ifs
    · exact Finset.sum_nonneg fun o' _ => (hp x' d' o').le
    · exact le_refl 0
  have := Finset.single_le_sum hnn (Finset.mem_univ x)
  exact lt_of_lt_of_le (margAC_pos p hp c x d o) (by simpa [margC, margAC] using this)

/-- **Chain rule (edge decomposition).**
`I(X; (D,O) | c(D)) = I(X; D | c(D)) + I(X; O | D, c(D))`
for a strictly positive joint `p` (normalisation is not needed). -/
theorem chain_rule (p : X → D → O → ℝ) (hp : ∀ x d o, 0 < p x d o) (c : D → K) :
    cmi (jXDO_K p c) = cmi (jXD_K p c) + cmi (jXO_DK p c) := by
  rw [cmi1_eq, cmi2_eq, cmi3_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  have h0 := hp x d o
  have hXD : 0 < ∑ o', p x d o' := Finset.sum_pos (fun o' _ => hp x d o') ⟨o, Finset.mem_univ _⟩
  have hDO : 0 < ∑ x', p x' d o := Finset.sum_pos (fun x' _ => hp x' d o) ⟨x, Finset.mem_univ _⟩
  have hD : 0 < ∑ x', ∑ o', p x' d o' :=
    Finset.sum_pos (fun x' _ => Finset.sum_pos (fun o' _ => hp x' d o') ⟨o, Finset.mem_univ _⟩)
      ⟨x, Finset.mem_univ _⟩
  have hK := margC_pos p hp c x d o
  have hXK := margAC_pos p hp c x d o
  rw [← mul_add, ← Real.log_mul (by positivity) (by positivity)]
  congr 2
  field_simp

/-- **Rival computes everything.** If `c` is injective, `I(X; D | c(D)) = 0`. -/
theorem cmi_public_zero_of_injective (p : X → D → O → ℝ) (hp : ∀ x d o, 0 < p x d o)
    (c : D → K) (hc : Function.Injective c) :
    cmi (jXD_K p c) = 0 := by
  rw [cmi2_eq]
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun d _ => ?_
  have hrow : ∀ x', margAC (jXD_K p c) x' (c d) = ∑ o, p x' d o := by
    intro x'
    unfold margAC
    rw [Finset.sum_eq_single d]
    · simp [jXD_K]
    · intro b _ hb; simp only [jXD_K]; exact ite_eq_right_iff.mpr fun h => absurd (hc h) hb
    · simp
  have hXK := hrow x
  have hK : margC (jXD_K p c) (c d) = ∑ x', ∑ o, p x' d o := by
    simpa [margC, margAC] using Finset.sum_congr rfl fun x' (_ : x' ∈ Finset.univ) => hrow x'
  rw [hXK, hK]
  rcases isEmpty_or_nonempty O with hO | ⟨⟨o⟩⟩
  · simp
  have hXD : 0 < ∑ o', p x d o' := Finset.sum_pos (fun o' _ => hp x d o') ⟨o, Finset.mem_univ _⟩
  have hD : 0 < ∑ x', ∑ o', p x' d o' :=
    Finset.sum_pos (fun x' _ => Finset.sum_pos (fun o' _ => hp x' d o') ⟨o, Finset.mem_univ _⟩)
      ⟨x, Finset.mem_univ _⟩
  rw [div_self (by positivity), Real.log_one, mul_zero]

/-- Corollary: with an injective summary, the whole edge is the private term. -/
theorem chain_rule_injective (p : X → D → O → ℝ) (hp : ∀ x d o, 0 < p x d o)
    (c : D → K) (hc : Function.Injective c) :
    cmi (jXDO_K p c) = cmi (jXO_DK p c) := by
  rw [chain_rule p hp c, cmi_public_zero_of_injective p hp c hc, zero_add]

/-- Entropy form of CMI for nonnegative weights:
`I(A;B|C) = H(A,C) + H(B,C) - H(A,B,C) - H(C)`. -/
theorem cmi_eq_entropies (q : A → B → C → ℝ) (hq : ∀ a b c, 0 ≤ q a b c) :
    cmi q = entropy (fun ac : A × C => margAC q ac.1 ac.2)
      + entropy (fun bc : B × C => margBC q bc.1 bc.2)
      - entropy (fun abc : A × B × C => q abc.1 abc.2.1 abc.2.2)
      - entropy (margC q) := by
  have hAC : ∀ a b c, q a b c ≤ margAC q a c := fun a b c =>
    Finset.single_le_sum (fun b' _ => hq a b' c) (Finset.mem_univ b)
  have hBC : ∀ a b c, q a b c ≤ margBC q b c := fun a b c =>
    Finset.single_le_sum (fun a' _ => hq a' b c) (Finset.mem_univ a)
  have hC : ∀ a c, margAC q a c ≤ margC q c := fun a c => by
    unfold margC margAC
    exact Finset.single_le_sum (f := fun a' => ∑ b', q a' b' c)
      (fun a' _ => Finset.sum_nonneg fun b' _ => hq a' b' c) (Finset.mem_univ a)
  -- termwise expansion
  have hterm : ∀ a b c, q a b c * Real.log (q a b c * margC q c / (margAC q a c * margBC q b c))
      = q a b c * Real.log (q a b c) + q a b c * Real.log (margC q c)
        - q a b c * Real.log (margAC q a c) - q a b c * Real.log (margBC q b c) := by
    intro a b c
    rcases (hq a b c).eq_or_lt with h | h
    · rw [← h]; simp
    · have h1 := h.trans_le (hAC a b c)
      have h2 := h.trans_le (hBC a b c)
      have h3 := h1.trans_le (hC a c)
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul h.ne' h3.ne',
        Real.log_mul h1.ne' h2.ne']
      ring
  unfold cmi entropy
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, Fintype.sum_prod_type]
  have eC : ∑ a, ∑ b, ∑ c, q a b c * Real.log (margC q c) = ∑ c, margC q c * Real.log (margC q c) := by
    rw [Finset.sum_comm]; simp_rw [Finset.sum_comm (s := (Finset.univ : Finset B))]
    simp only [margC, Finset.sum_mul]
    rw [Finset.sum_comm]
  have eAC : ∑ a, ∑ b, ∑ c, q a b c * Real.log (margAC q a c)
      = ∑ a, ∑ c, margAC q a c * Real.log (margAC q a c) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    simp only [margAC, Finset.sum_mul]
  have eBC : ∑ a, ∑ b, ∑ c, q a b c * Real.log (margBC q b c)
      = ∑ b, ∑ c, margBC q b c * Real.log (margBC q b c) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    simp only [margBC, Finset.sum_mul]
  rw [eC, eAC, eBC]
  ring

/-! ### Added by the adversarial second agent -/

/-- **Gibbs / nonnegativity (going up).** For any nonnegative weights, `0 ≤ I(A;B|C)`.
Proof: termwise `q log(q q_C/(q_AC q_BC)) ≥ q - q_AC q_BC / q_C` (from `log x ≥ 1 - 1/x`),
and the right-hand side sums to `Σ_c (q_C - q_C q_C / q_C) = 0`. -/
theorem cmi_nonneg (q : A → B → C → ℝ) (hq : ∀ a b c, 0 ≤ q a b c) : 0 ≤ cmi q := by
  have hAC : ∀ a b c, q a b c ≤ margAC q a c := fun a b c =>
    Finset.single_le_sum (fun b' _ => hq a b' c) (Finset.mem_univ b)
  have hBC : ∀ a b c, q a b c ≤ margBC q b c := fun a b c =>
    Finset.single_le_sum (fun a' _ => hq a' b c) (Finset.mem_univ a)
  have hC : ∀ a c, margAC q a c ≤ margC q c := fun a c => by
    unfold margC margAC
    exact Finset.single_le_sum (f := fun a' => ∑ b', q a' b' c)
      (fun a' _ => Finset.sum_nonneg fun b' _ => hq a' b' c) (Finset.mem_univ a)
  have key : ∀ a b c, q a b c - margAC q a c * margBC q b c / margC q c
      ≤ q a b c * Real.log (q a b c * margC q c / (margAC q a c * margBC q b c)) := by
    intro a b c
    have n0 : 0 ≤ margAC q a c := (hq a b c).trans (hAC a b c)
    have r0 : 0 ≤ margBC q b c := (hq a b c).trans (hBC a b c)
    have m0 : 0 ≤ margC q c := n0.trans (hC a c)
    rcases (hq a b c).eq_or_lt with h | h
    · rw [← h]; simp only [zero_sub, zero_mul, neg_nonpos]; positivity
    · have h1 := h.trans_le (hAC a b c)
      have h2 := h.trans_le (hBC a b c)
      have h3 := h1.trans_le (hC a c)
      have hx : 0 < q a b c * margC q c / (margAC q a c * margBC q b c) := by positivity
      have hl := Real.one_sub_inv_le_log_of_pos hx
      have : q a b c - margAC q a c * margBC q b c / margC q c
          = q a b c * (1 - (q a b c * margC q c / (margAC q a c * margBC q b c))⁻¹) := by
        field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hl h.le
  have hsum : ∑ a, ∑ b, ∑ c, (q a b c - margAC q a c * margBC q b c / margC q c) = 0 := by
    have hswap : ∀ (f : A → B → C → ℝ), ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
      intro f
      rw [Finset.sum_congr rfl fun a _ => (Finset.sum_comm : ∑ b, ∑ c, f a b c = _),
        Finset.sum_comm]
    rw [hswap]
    refine Finset.sum_eq_zero fun c _ => ?_
    simp only [Finset.sum_sub_distrib]
    rw [show ∑ a, ∑ b, margAC q a c * margBC q b c / margC q c
        = (∑ a, margAC q a c) * (∑ b, margBC q b c) / margC q c by
      rw [Finset.sum_mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_div]]
    have e1 : ∑ a, margAC q a c = margC q c := rfl
    have e2 : ∑ b, margBC q b c = margC q c := by
      unfold margBC margC; exact Finset.sum_comm
    rw [e1, e2, show ∑ a, ∑ b, q a b c = margC q c from rfl]
    rcases eq_or_ne (margC q c) 0 with h0 | h0
    · simp [h0]
    · field_simp; ring
  calc (0 : ℝ) = ∑ a, ∑ b, ∑ c, (q a b c - margAC q a c * margBC q b c / margC q c) := hsum.symm
    _ ≤ cmi q := by
      unfold cmi
      exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
        Finset.sum_le_sum fun c _ => key a b c

/-- Corollary of `chain_rule` + `cmi_nonneg`: the private term never exceeds the whole edge. -/
theorem private_le_edge (p : X → D → O → ℝ) (hp : ∀ x d o, 0 < p x d o) (c : D → K) :
    cmi (jXO_DK p c) ≤ cmi (jXDO_K p c) := by
  have h0 : 0 ≤ cmi (jXD_K p c) := cmi_nonneg _ fun x d k => by
    unfold jXD_K; split_ifs
    · exact Finset.sum_nonneg fun o _ => (hp x d o).le
    · exact le_refl 0
  rw [chain_rule p hp c]; linarith

/-! ### Concrete example (non-vacuity) -/

/-- Example joint on `X = D = Bool`, `O = Unit`: `p x d = 2` if `x = d`, else `1`. Strictly positive. -/
def pEx : Bool → Bool → Unit → ℝ := fun x d _ => if x = d then 2 else 1

lemma pEx_pos : ∀ x d o, 0 < pEx x d o := by
  intro x d o; unfold pEx; split_ifs <;> norm_num

/-- With a constant (non-injective) rival summary `c : Bool → Unit`, the public term is
strictly positive: `I(X;D|c D) = 2 log (32/27) > 0`. So the injectivity hypothesis of
`cmi_public_zero_of_injective` is not removable, and the quantities are not all trivially 0. -/
theorem example_coarse_public_pos :
    cmi (jXD_K pEx (fun _ : Bool => ())) = 2 * Real.log (32 / 27) ∧
      0 < cmi (jXD_K pEx (fun _ : Bool => ())) := by
  have hval : cmi (jXD_K pEx (fun _ : Bool => ())) = 2 * Real.log (32 / 27) := by
    rw [cmi2_eq]
    simp only [margC, margAC, jXD_K, pEx, Fintype.sum_bool, Fintype.univ_punit,
      Finset.sum_singleton, ite_true]
    norm_num
    rw [show (32 / 27 : ℝ) = (4 / 3) ^ 2 * (2 / 3) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  refine ⟨hval, ?_⟩
  rw [hval]
  have : 0 < Real.log (32 / 27) := Real.log_pos (by norm_num)
  linarith

end

end F1
