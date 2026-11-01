import Mathlib

/-!
# U6: Private noise creates the learnable gap (proofs)

Two copies of one agent run the *same* deterministic program `f : Fin m → Bool`
on a seed. Seeds are uniform on `Fin m`; probabilities are counting fractions.

* Shared seed: one seed `s`, both copies play `f s`.
* Private seeds: an independent pair `(s, t)`, uniform on `Fin m × Fin m`.

PROVED in the proofs file (the statements file has the same statements with `sorry`):
1. `sharedDiffer_eq_zero`: under a shared seed the copies differ with probability 0,
   and `shared_on_diagonal`: every shared-seed outcome is on the diagonal.
2. `privateDiffer_eq`: under private seeds the copies differ with probability
   `2 q (1 - q)`, `q = P(f = true)`; `two_q_one_sub_q_le_half` /
   `privateDiffer_le_half`: this is at most `1/2`, with equality iff `q = 1/2`
   (`privateDiffer_eq_half_iff`), and `1/2` is attained for every even `m > 0`
   (`exists_privateDiffer_eq_half`).
3. For any `g : Bool → Bool → ℝ` vanishing on the diagonal:
   `sharedExp_eq_zero` (expectation exactly 0 under shared seeds),
   `privateExp_eq` (expectation `q (1-q) (g tt ff + g ff tt)` under private seeds),
   `privateExp_pos` (strictly positive when `g true false + g false true > 0`
   and `0 < q < 1`).
4. (adversarial pass) `privateDifferGen_eq_and_le`: for any finite action set the
   private-seed differing probability is `1 - ∑ₐ pₐ²` and at most `1 - 1/|α|`.

INTERPRETED (not formalised): reading `g` as regret or as the off-diagonal payoff of
chicken; the claim that this zero-vs-positive gap is what a learner can exploit.
-/

open Finset

namespace U6

variable {m : ℕ}

/-- `q = P(f s = true)` for `s` uniform on `Fin m`. -/
noncomputable def qfrac (f : Fin m → Bool) : ℝ :=
  ((univ.filter (fun s => f s = true)).card : ℝ) / m

/-- Shared seed: probability the two copies' actions differ. -/
noncomputable def sharedDiffer (f : Fin m → Bool) : ℝ :=
  ((univ.filter (fun s : Fin m => f s ≠ f s)).card : ℝ) / m

/-- Private independent seeds: probability the two copies' actions differ. -/
noncomputable def privateDiffer (f : Fin m → Bool) : ℝ :=
  ((univ.filter (fun p : Fin m × Fin m => f p.1 ≠ f p.2)).card : ℝ) / (m : ℝ) ^ 2

/-- Shared seed: expectation of a joint-outcome quantity `g`. -/
noncomputable def sharedExp (f : Fin m → Bool) (g : Bool → Bool → ℝ) : ℝ :=
  (∑ s, g (f s) (f s)) / m

/-- Private seeds: expectation of a joint-outcome quantity `g`. -/
noncomputable def privateExp (f : Fin m → Bool) (g : Bool → Bool → ℝ) : ℝ :=
  (∑ s, ∑ t, g (f s) (f t)) / (m : ℝ) ^ 2


/-! ### Auxiliary lemmas (not part of the statement surface) -/

/-- Bool → {0,1} indicator. -/
noncomputable def bI (x : Bool) : ℝ := if x then 1 else 0

lemma pointwise (g : Bool → Bool → ℝ) (x y : Bool) :
    g x y = bI x * bI y * g true true + bI x * (1 - bI y) * g true false
      + (1 - bI x) * bI y * g false true + (1 - bI x) * (1 - bI y) * g false false := by
  cases x <;> cases y <;> simp [bI]

lemma dsum (B C : Fin m → ℝ) (k : ℝ) :
    ∑ s, ∑ t, B s * C t * k = (∑ s, B s) * (∑ t, C t) * k := by
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_mul]

lemma sumB (f : Fin m → Bool) :
    ∑ s, bI (f s) = ((univ.filter (fun s => f s = true)).card : ℝ) := by
  simp [bI, Finset.sum_boole]

lemma sum_one_sub (f : Fin m → Bool) :
    ∑ s, (1 - bI (f s)) = (m : ℝ) - ((univ.filter (fun s => f s = true)).card : ℝ) := by
  rw [Finset.sum_sub_distrib, sumB]; simp

lemma double_sum (f : Fin m → Bool) (g : Bool → Bool → ℝ) :
    let S : ℝ := ((univ.filter (fun s => f s = true)).card : ℝ)
    ∑ s, ∑ t, g (f s) (f t) =
      S * S * g true true + S * (m - S) * g true false
        + (m - S) * S * g false true + (m - S) * (m - S) * g false false := by
  intro S
  simp_rw [pointwise g (f _) (f _), Finset.sum_add_distrib, dsum, sumB, sum_one_sub]
  rfl

lemma privateExp_indicator_aux (f : Fin m → Bool) :
    privateExp f (fun a b => if a ≠ b then 1 else 0) = privateDiffer f := by
  rw [privateExp, privateDiffer, Finset.card_filter, Fintype.sum_prod_type]
  push_cast
  rfl

/-- (1a) Every shared-seed outcome lies on the diagonal. -/
theorem shared_on_diagonal (f : Fin m → Bool) (s : Fin m) :
    (f s, f s) ∈ Set.diagonal Bool := by
  rfl

/-- (1b) Shared seed: the copies differ with probability exactly 0. -/
theorem sharedDiffer_eq_zero (f : Fin m → Bool) : sharedDiffer f = 0 := by
  simp [sharedDiffer]

/-- (2a) Private seeds: probability of differing is `2 q (1 - q)`. -/
theorem privateDiffer_eq (hm : 0 < m) (f : Fin m → Bool) :
    privateDiffer f = 2 * qfrac f * (1 - qfrac f) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have h := double_sum f (fun a b : Bool => if a ≠ b then (1 : ℝ) else 0)
  simp only [ne_eq, not_true_eq_false, ite_false, Bool.true_eq_false, Bool.false_eq_true,
    not_false_eq_true, ite_true] at h
  rw [← privateExp_indicator_aux, privateExp]
  simp only [ne_eq]
  rw [h, qfrac]
  field_simp
  ring

/-- (2b) Real-number bound: `2 q (1 - q) ≤ 1/2`, equality iff `q = 1/2`. -/
theorem two_q_one_sub_q_le_half (q : ℝ) : 2 * q * (1 - q) ≤ 1 / 2 := by
  nlinarith [sq_nonneg (q - 1 / 2)]

theorem two_q_one_sub_q_eq_half_iff (q : ℝ) : 2 * q * (1 - q) = 1 / 2 ↔ q = 1 / 2 := by
  constructor
  · intro h
    have : (q - 1 / 2) ^ 2 = 0 := by nlinarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · rintro rfl; norm_num

/-- (2c) Private seeds: differing probability is at most `1/2`. -/
theorem privateDiffer_le_half (hm : 0 < m) (f : Fin m → Bool) :
    privateDiffer f ≤ 1 / 2 := by
  rw [privateDiffer_eq hm]; exact two_q_one_sub_q_le_half _

/-- (2d) ... with equality exactly when `q = 1/2`. -/
theorem privateDiffer_eq_half_iff (hm : 0 < m) (f : Fin m → Bool) :
    privateDiffer f = 1 / 2 ↔ qfrac f = 1 / 2 := by
  rw [privateDiffer_eq hm]; exact two_q_one_sub_q_eq_half_iff _

/-- (2e) The maximum `1/2` is attained for every even positive seed count. -/
theorem exists_privateDiffer_eq_half (k : ℕ) (hk : 0 < k) :
    ∃ f : Fin (2 * k) → Bool, qfrac f = 1 / 2 ∧ privateDiffer f = 1 / 2 := by
  refine ⟨fun s => decide ((s : ℕ) < k), ?_, ?_⟩
  · have hc : (univ.filter (fun s : Fin (2 * k) => decide ((s : ℕ) < k) = true)).card = k := by
      simp only [decide_eq_true_eq]
      rw [Fin.card_filter_val_lt]; omega
    rw [qfrac, hc]
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    push_cast; field_simp
  · rw [privateDiffer_eq_half_iff (by omega)]
    have hc : (univ.filter (fun s : Fin (2 * k) => decide ((s : ℕ) < k) = true)).card = k := by
      simp only [decide_eq_true_eq]
      rw [Fin.card_filter_val_lt]; omega
    rw [qfrac, hc]
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    push_cast; field_simp

/-- (3a) Shared seed: any quantity vanishing on the diagonal has expectation 0. -/
theorem sharedExp_eq_zero (f : Fin m → Bool) (g : Bool → Bool → ℝ)
    (hg : ∀ a, g a a = 0) : sharedExp f g = 0 := by
  simp [sharedExp, hg]

/-- (3b) Private seeds: closed form for such a quantity. -/
theorem privateExp_eq (hm : 0 < m) (f : Fin m → Bool) (g : Bool → Bool → ℝ)
    (hg : ∀ a, g a a = 0) :
    privateExp f g = qfrac f * (1 - qfrac f) * (g true false + g false true) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [privateExp, double_sum, qfrac, hg true, hg false]
  field_simp
  ring

/-- (3c) Private seeds: strictly positive expectation whenever the policy is
genuinely mixed (`0 < q < 1`) and the two off-diagonal values of `g` have positive sum
(e.g. `g ≥ 0` off-diagonal and not both zero; no sign condition on each cell is needed). -/
theorem privateExp_pos (hm : 0 < m) (f : Fin m → Bool) (g : Bool → Bool → ℝ)
    (hg : ∀ a, g a a = 0)
    (h12 : 0 < g true false + g false true)
    (hq0 : 0 < qfrac f) (hq1 : qfrac f < 1) :
    0 < privateExp f g := by
  rw [privateExp_eq hm f g hg]
  exact mul_pos (mul_pos hq0 (by linarith)) h12

/-- (3d) The gap: shared-seed expectation 0, private-seed expectation positive. -/
theorem gap (hm : 0 < m) (f : Fin m → Bool) (g : Bool → Bool → ℝ)
    (hg : ∀ a, g a a = 0)
    (h12 : 0 < g true false + g false true)
    (hq0 : 0 < qfrac f) (hq1 : qfrac f < 1) :
    sharedExp f g = 0 ∧ 0 < privateExp f g := by
  exact ⟨sharedExp_eq_zero f g hg, privateExp_pos hm f g hg h12 hq0 hq1⟩

/-- (3e) Consistency: the differing indicator is such a `g`, and its private
expectation is `privateDiffer`. -/
theorem privateExp_indicator (f : Fin m → Bool) :
    privateExp f (fun a b => if a ≠ b then 1 else 0) = privateDiffer f := by
  rw [privateExp, privateDiffer, Finset.card_filter, Fintype.sum_prod_type]
  push_cast
  rfl

/-! ### Adversarial-pass additions

Added by the second (adversarial) agent. Everything below is PROVED in the proofs
file; the statements file has `sorry` in the same places.

**Going up: from `Bool` to any finite action set.** For a program `f : Fin m → α`
with `α` finite, private seeds make the copies differ with probability
`1 - ∑ₐ pₐ²` (one minus the collision probability of the action distribution),
which is at most `1 - 1/|α|`. For `α = Bool` this is `1 - q² - (1-q)² = 2 q (1-q)`
and the bound is the `1/2` of (2). INTERPRETED, not proved: the bound is attained by
the uniform distribution when `|α|` divides `m` (only the Bool case, (2e), is proved). -/

section General

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `pₐ = P(f s = a)` for `s` uniform on `Fin m`. -/
noncomputable def pfrac (f : Fin m → α) (a : α) : ℝ :=
  ((univ.filter (fun s => f s = a)).card : ℝ) / m

/-- Private independent seeds, general action set: probability the copies differ.
For `α = Bool` this is literally `privateDiffer`. -/
noncomputable def privateDifferGen (f : Fin m → α) : ℝ :=
  ((univ.filter (fun p : Fin m × Fin m => f p.1 ≠ f p.2)).card : ℝ) / (m : ℝ) ^ 2

lemma card_ne_eq (f : Fin m → α) :
    ((univ.filter (fun p : Fin m × Fin m => f p.1 ≠ f p.2)).card : ℝ)
      = (m : ℝ) ^ 2 - ∑ a, ((univ.filter (fun s => f s = a)).card : ℝ) ^ 2 := by
  have h1 : ((univ.filter (fun p : Fin m × Fin m => f p.1 ≠ f p.2)).card : ℝ)
      = ∑ s, ∑ t, (1 - if f s = f t then (1:ℝ) else 0) := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp_all
  have h2 : ∀ s t : Fin m, (if f s = f t then (1:ℝ) else 0)
      = ∑ a, (if f s = a then (1:ℝ) else 0) * (if f t = a then 1 else 0) := by
    intro s t
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have h3 : ∑ s : Fin m, ∑ t : Fin m, ∑ a, (if f s = a then (1:ℝ) else 0) * (if f t = a then 1 else 0)
      = ∑ a, ((univ.filter (fun s => f s = a)).card : ℝ) ^ 2 := by
    have hc : ∀ a, ((univ.filter (fun s : Fin m => f s = a)).card : ℝ)
        = ∑ s, (if f s = a then (1:ℝ) else 0) := by
      intro a; rw [Finset.card_filter]; push_cast; rfl
    simp_rw [hc, sq, Finset.sum_mul_sum]
    exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
  rw [h1]
  simp_rw [Finset.sum_sub_distrib, h2]
  rw [h3]
  simp
  ring
/-- (4) NEW. Private seeds with any finite action set: the copies differ with
probability `1 - ∑ₐ pₐ²`, and this is at most `1 - 1/|α|`. -/
theorem privateDifferGen_eq_and_le (hm : 0 < m) (f : Fin m → α) :
    privateDifferGen f = 1 - ∑ a, pfrac f a ^ 2 ∧
    privateDifferGen f ≤ 1 - 1 / (Fintype.card α : ℝ) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have heq : privateDifferGen f = 1 - ∑ a, pfrac f a ^ 2 := by
    rw [privateDifferGen, card_ne_eq]
    simp_rw [pfrac, div_pow, ← Finset.sum_div]
    field_simp
  refine ⟨heq, ?_⟩
  have hsum : ∑ a, pfrac f a = 1 := by
    simp_rw [pfrac, ← Finset.sum_div]
    rw [div_eq_one_iff_eq hm']
    have := Finset.card_eq_sum_card_fiberwise (f := f) (s := univ) (t := univ) (by simp)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this.symm
  have hα : 0 < (Fintype.card α : ℝ) := by
    have : Nonempty α := ⟨f ⟨0, hm⟩⟩
    exact_mod_cast Fintype.card_pos
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset α)) (f := pfrac f)
  rw [hsum, Finset.card_univ] at hcs
  rw [heq]
  have : 1 / (Fintype.card α : ℝ) ≤ ∑ a, pfrac f a ^ 2 := by
    rw [div_le_iff₀ hα]; linarith
  linarith

end General

/-! ### Concrete, non-vacuous instances -/

/-- A concrete policy on 4 seeds: play `true` on seed 0 only, so `q = 1/4`. -/
def f4 : Fin 4 → Bool := fun s => decide ((s : ℕ) < 1)

example : qfrac f4 = 1 / 4 := by
  have : (univ.filter (fun s : Fin 4 => f4 s = true)).card = 1 := by decide
  rw [qfrac, this]; norm_num

/-- `2 q (1-q) = 2 · 1/4 · 3/4 = 3/8`, checked by direct counting (6 of 16 pairs). -/
example : privateDiffer f4 = 3 / 8 := by
  have : (univ.filter (fun p : Fin 4 × Fin 4 => f4 p.1 ≠ f4 p.2)).card = 6 := by decide
  rw [privateDiffer, this]; norm_num

/-- An off-diagonal quantity with one NEGATIVE cell (`3` and `-1`): the weakened
hypothesis of `privateExp_pos` (positive sum only) is genuinely weaker and still met. -/
def gSkew : Bool → Bool → ℝ := fun a b => if a = b then 0 else if a then 3 else -1

example : sharedExp f4 gSkew = 0 ∧ privateExp f4 gSkew = 3 / 8 := by
  refine ⟨sharedExp_eq_zero f4 gSkew (by intro a; simp [gSkew]), ?_⟩
  simp [privateExp, gSkew, f4, Fin.sum_univ_four]; norm_num

example : 0 < privateExp f4 gSkew :=
  privateExp_pos (by norm_num) f4 gSkew (by intro a; simp [gSkew])
    (by norm_num [gSkew]) (by
      have : (univ.filter (fun s : Fin 4 => f4 s = true)).card = 1 := by decide
      rw [qfrac, this]; norm_num) (by
      have : (univ.filter (fun s : Fin 4 => f4 s = true)).card = 1 := by decide
      rw [qfrac, this]; norm_num)

/-- FIDELITY WARNING (proved). The spec's example "the off-diagonal payoff of chicken"
needs care. With the textbook row-player chicken payoffs `u(S,S)=0, u(D,S)=1,
u(S,D)=-1, u(D,D)=-10`, the off-diagonal part of ONE player's payoff has cell sum
`1 + (-1) = 0`, so by `privateExp_eq` its private-seed expectation is `0` for every
policy: private noise produces no gap in that quantity. The gap theorem needs
`g true false + g false true > 0`, which holds e.g. for the joint off-diagonal
indicator, for regret-type quantities `≥ 0`, or for chicken variants where the
winner's gain exceeds the loser's loss. -/
example (hm : 0 < m) (f : Fin m → Bool) :
    privateExp f (fun a b => if a = b then 0 else if a then 1 else -1) = 0 := by
  rw [privateExp_eq hm f _ (by intro a; simp)]
  norm_num

end U6
