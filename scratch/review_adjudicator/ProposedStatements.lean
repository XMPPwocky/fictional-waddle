import Mathlib

/-!
# Proposed freeze-ready statements for `EntropyConserved.lean`, with proofs

The definitions H, margA, margB, I and cnot repeat those of `scratch/EntropyConserved.lean` verbatim; KL and shift3 are defined here. Every statement below
(E5–E16, E4') is proved unconditionally; nothing is assumed. The helper lemmas
(`H_comp`, `mutual_info_nonneg`, `H_margA_le`, `H_margB_le`, `H_le_log_card`, `H_prod`,
`KL_nonneg`) are standard facts proved here so that the file is self-contained.
-/

namespace EntropyConserved
open Real Finset
variable {α β : Type*} [Fintype α] [Fintype β]

set_option linter.unusedSectionVars false

noncomputable def H {γ : Type*} [Fintype γ] (p : γ → ℝ) : ℝ := ∑ x, negMulLog (p x)
def margA (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)
def margB (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)
noncomputable def I (p : α × β → ℝ) : ℝ := H (margA p) + H (margB p) - H p
/-- Relative entropy (KL) in nats; terms with `p' x = 0` vanish. -/
noncomputable def KL {γ : Type*} [Fintype γ] (p' r : γ → ℝ) : ℝ := ∑ x, p' x * log (p' x / r x)

def cnot : Bool × Bool ≃ Bool × Bool where
  toFun x := (x.1, xor x.2 x.1)
  invFun x := (x.1, xor x.2 x.1)
  left_inv x := by cases x with | mk a b => cases a <;> cases b <;> rfl
  right_inv x := by cases x with | mk a b => cases a <;> cases b <;> rfl

/-! ## Helper lemmas -/

theorem H_comp {γ : Type*} [Fintype γ] (p : γ → ℝ) (f : γ ≃ γ) :
    H (fun x => p (f.symm x)) = H p := by
  unfold H
  exact Equiv.sum_comp f.symm (fun y => negMulLog (p y))

theorem sum_comp_symm {γ : Type*} [Fintype γ] (p : γ → ℝ) (f : γ ≃ γ) :
    ∑ x, p (f.symm x) = ∑ x, p x :=
  Equiv.sum_comp f.symm p

theorem margA_sum (p : α × β → ℝ) : ∑ a, margA p a = ∑ x, p x := by
  unfold margA; rw [Fintype.sum_prod_type]

theorem margB_sum (p : α × β → ℝ) : ∑ b, margB p b = ∑ x, p x := by
  unfold margB; rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem margA_nonneg (p : α × β → ℝ) (hp : ∀ x, 0 ≤ p x) (a : α) : 0 ≤ margA p a :=
  Finset.sum_nonneg fun b _ => hp (a, b)

theorem margB_nonneg (p : α × β → ℝ) (hp : ∀ x, 0 ≤ p x) (b : β) : 0 ≤ margB p b :=
  Finset.sum_nonneg fun a _ => hp (a, b)

/-- `I p` as a sum of `p log (p / (A B))`, with `A`, `B` the marginals. -/
theorem I_eq_sum (p : α × β → ℝ) (hp : ∀ x, 0 ≤ p x) :
    I p = ∑ x, p x * log (p x / (margA p x.1 * margB p x.2)) := by
  have hpA : ∀ a b, p (a, b) ≤ margA p a := fun a b =>
    Finset.single_le_sum (f := fun b => p (a, b)) (fun b _ => hp (a, b)) (Finset.mem_univ b)
  have hpB : ∀ a b, p (a, b) ≤ margB p b := fun a b =>
    Finset.single_le_sum (f := fun a => p (a, b)) (fun a _ => hp (a, b)) (Finset.mem_univ a)
  have hterm : ∀ x : α × β, p x * log (p x / (margA p x.1 * margB p x.2))
      = p x * log (p x) - p x * log (margA p x.1) - p x * log (margB p x.2) := by
    rintro ⟨a, b⟩
    rcases (hp (a, b)).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have ha : 0 < margA p a := lt_of_lt_of_le hpos (hpA a b)
      have hb : 0 < margB p b := lt_of_lt_of_le hpos (hpB a b)
      rw [Real.log_div hpos.ne' (by positivity), Real.log_mul ha.ne' hb.ne']
      ring
  have e1 : ∑ x : α × β, p x * log (margA p x.1) = ∑ a, margA p a * log (margA p a) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro a _
    show ∑ y, p (a, y) * log (margA p a) = _
    rw [← Finset.sum_mul]; rfl
  have e2 : ∑ x : α × β, p x * log (margB p x.2) = ∑ b, margB p b * log (margB p b) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b _
    show ∑ x, p (x, b) * log (margB p b) = _
    rw [← Finset.sum_mul]; rfl
  simp only [hterm, Finset.sum_sub_distrib, e1, e2]
  unfold I H
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

/-- Termwise Gibbs inequality: `p log (p / r) ≥ p - r` for `p ≥ 0`, `r > 0`. -/
theorem mul_log_div_ge {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) : p - r ≤ p * log (p / r) := by
  rcases hp.eq_or_lt with h0 | hpos
  · rw [← h0]; simp [hr.le]
  · have hl := Real.log_le_sub_one_of_pos (div_pos hr hpos)
    have heq : log (p / r) = - log (r / p) := by
      rw [← Real.log_inv, inv_div]
    rw [heq]
    have : p * (r / p - 1) = r - p := by field_simp
    nlinarith

/-- Strict termwise Gibbs inequality: equality only at `p = r`. -/
theorem mul_log_div_gt {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) (hne : p ≠ r) :
    p - r < p * log (p / r) := by
  rcases hp.eq_or_lt with h0 | hpos
  · rw [← h0]; simp [hr]
  · have hne' : r / p ≠ 1 := by
      intro h; apply hne; field_simp at h; linarith
    have hl := Real.log_lt_sub_one_of_pos (div_pos hr hpos) hne'
    have heq : log (p / r) = - log (r / p) := by
      rw [← Real.log_inv, inv_div]
    rw [heq]
    have : p * (r / p - 1) = r - p := by field_simp
    nlinarith

theorem mutual_info_nonneg (p : α × β → ℝ) (hp : ∀ x, 0 ≤ p x) (h1 : ∑ x, p x = 1) : 0 ≤ I p := by
  have hpA : ∀ a b, p (a, b) ≤ margA p a := fun a b =>
    Finset.single_le_sum (f := fun b => p (a, b)) (fun b _ => hp (a, b)) (Finset.mem_univ b)
  have hpB : ∀ a b, p (a, b) ≤ margB p b := fun a b =>
    Finset.single_le_sum (f := fun a => p (a, b)) (fun a _ => hp (a, b)) (Finset.mem_univ a)
  have key : ∀ x : α × β, p x - margA p x.1 * margB p x.2
      ≤ p x * log (p x / (margA p x.1 * margB p x.2)) := by
    rintro ⟨a, b⟩
    rcases (hp (a, b)).eq_or_lt with h0 | hpos
    · rw [← h0]; simp only [zero_mul, zero_sub, neg_nonpos]
      exact mul_nonneg (margA_nonneg p hp a) (margB_nonneg p hp b)
    · have ha : 0 < margA p a := lt_of_lt_of_le hpos (hpA a b)
      have hb : 0 < margB p b := lt_of_lt_of_le hpos (hpB a b)
      exact mul_log_div_ge hpos.le (mul_pos ha hb)
  have hprod : ∑ x : α × β, margA p x.1 * margB p x.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, margB_sum, margA_sum, h1, mul_one]
  rw [I_eq_sum p hp]
  calc (0 : ℝ) = ∑ x, (p x - margA p x.1 * margB p x.2) := by
        rw [Finset.sum_sub_distrib, h1, hprod]; ring
    _ ≤ _ := Finset.sum_le_sum fun x _ => key x

theorem H_margB_le (p : α × β → ℝ) (hp : ∀ x, 0 ≤ p x) : H (margB p) ≤ H p := by
  have hpB : ∀ a b, p (a, b) ≤ margB p b := fun a b =>
    Finset.single_le_sum (f := fun a => p (a, b)) (fun a _ => hp (a, b)) (Finset.mem_univ a)
  have e : H p - H (margB p) = ∑ a, ∑ b, p (a, b) * (log (margB p b) - log (p (a, b))) := by
    unfold H
    rw [Fintype.sum_prod_type]
    have : ∑ b, negMulLog (margB p b) = ∑ a, ∑ b, - (p (a, b) * log (margB p b)) := by
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _
      simp only [Real.negMulLog, margB, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
    rw [this, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro a _
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro b _
    simp only [Real.negMulLog]; ring
  have hnn : 0 ≤ ∑ a, ∑ b, p (a, b) * (log (margB p b) - log (p (a, b))) := by
    apply Finset.sum_nonneg; intro a _; apply Finset.sum_nonneg; intro b _
    rcases (hp (a, b)).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · exact mul_nonneg hpos.le (sub_nonneg.mpr (Real.log_le_log hpos (hpB a b)))
  linarith

theorem H_margA_le (p : α × β → ℝ) (hp : ∀ x, 0 ≤ p x) : H (margA p) ≤ H p := by
  have := H_margB_le (α := β) (β := α) (fun x => p x.swap) (fun x => hp _)
  have h1 : H (fun x : β × α => p x.swap) = H p := by
    unfold H; exact Equiv.sum_comp (Equiv.prodComm β α) (fun y => negMulLog (p y))
  have h2 : margB (fun x : β × α => p x.swap) = margA p := by funext a; rfl
  rw [h1, h2] at this; exact this

/-- Entropy is at most `log` of the alphabet size. -/
theorem H_le_log_card {γ : Type*} [Fintype γ] (p : γ → ℝ) (hp : ∀ x, 0 ≤ p x)
    (h1 : ∑ x, p x = 1) : H p ≤ Real.log (Fintype.card γ) := by
  have hne : Nonempty γ := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    simp at h1
  have hn : (0 : ℝ) < Fintype.card γ := Nat.cast_pos.mpr Fintype.card_pos
  set n : ℝ := (Fintype.card γ : ℝ) with hndef
  have key : ∀ x, negMulLog (p x) - p x * Real.log n ≤ 1 / n - p x := by
    intro x
    rcases (hp x).eq_or_lt with h0 | hpos
    · rw [← h0]; simp [hn.le]
    · have hl := Real.log_le_sub_one_of_pos (show 0 < 1 / (n * p x) by positivity)
      rw [one_div, Real.log_inv, Real.log_mul hn.ne' hpos.ne'] at hl
      have : p x * ((n * p x)⁻¹ - 1) = 1 / n - p x := by field_simp
      simp only [Real.negMulLog]
      nlinarith
  have hsum : ∑ x, (negMulLog (p x) - p x * Real.log n) ≤ ∑ x, (1 / n - p x) :=
    Finset.sum_le_sum fun x _ => key x
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, h1] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [← hndef] at hsum
  have : n * (1 / n) = 1 := by field_simp
  unfold H
  linarith

theorem H_prod (q : α → ℝ) (r : β → ℝ) (hq1 : ∑ a, q a = 1) (hr1 : ∑ b, r b = 1) :
    H (fun x : α × β => q x.1 * r x.2) = H q + H r := by
  unfold H
  rw [Fintype.sum_prod_type]
  simp only [Real.negMulLog_mul, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl; intro a _; rw [← Finset.sum_mul, hr1, one_mul]
  · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _; rw [← Finset.sum_mul, hq1, one_mul]

/-- Gibbs inequality. -/
theorem KL_nonneg {γ : Type*} [Fintype γ] (p' r : γ → ℝ) (hp' : ∀ x, 0 ≤ p' x) (hr : ∀ x, 0 < r x)
    (hp'1 : ∑ x, p' x = 1) (hr1 : ∑ x, r x = 1) : 0 ≤ KL p' r := by
  unfold KL
  calc (0 : ℝ) = ∑ x, (p' x - r x) := by rw [Finset.sum_sub_distrib, hp'1, hr1]; ring
    _ ≤ _ := Finset.sum_le_sum fun x _ => mul_log_div_ge (hp' x) (hr x)

/-! ## The proposed statements -/

/-- **E5** general step: any start, any bijection. -/
theorem parts_change_general (p₀ : α × β → ℝ) (f : α × β ≃ α × β) :
    let p₁ : α × β → ℝ := fun x => p₀ (f.symm x)
    (H (margA p₁) + H (margB p₁)) - (H (margA p₀) + H (margB p₀)) = I p₁ - I p₀ := by
  intro p₁
  unfold I
  rw [show H p₁ = H p₀ from H_comp p₀ f]
  ring

/-- **E6** the product start is necessary. -/
theorem correlated_start_can_decrease :
    ∃ (p₀ : Bool × Bool → ℝ) (f : Bool × Bool ≃ Bool × Bool), (∀ x, 0 ≤ p₀ x) ∧ ∑ x, p₀ x = 1 ∧
      (H (margA fun x => p₀ (f.symm x)) + H (margB fun x => p₀ (f.symm x)))
        - (H (margA p₀) + H (margB p₀)) < 0 := by
  refine ⟨fun x => if x.1 = x.2 then 1/2 else 0, cnot, ?_, ?_, ?_⟩
  · intro x; dsimp only; split_ifs <;> norm_num
  · simp [Fintype.sum_prod_type]
  · have h : (H (margA fun x => (fun x : Bool × Bool => if x.1 = x.2 then (1/2 : ℝ) else 0)
          (cnot.symm x)) + H (margB fun x => (fun x : Bool × Bool => if x.1 = x.2 then (1/2 : ℝ)
          else 0) (cnot.symm x))) - (H (margA fun x : Bool × Bool => if x.1 = x.2 then (1/2 : ℝ)
          else 0) + H (margB fun x : Bool × Bool => if x.1 = x.2 then (1/2 : ℝ) else 0))
          = - Real.log 2 := by
      simp only [H, margA, margB, cnot, Equiv.coe_fn_symm_mk, Fintype.sum_bool]
      norm_num [Real.negMulLog, Real.log_inv]
      rw [show Real.log (1 / 2) = -Real.log 2 by rw [one_div, Real.log_inv]]; ring
    rw [h]
    exact neg_neg_of_pos (Real.log_pos (by norm_num))

/-- **E7** exact recurrence: no monotone arrow in a finite reversible model. -/
theorem recurrence [DecidableEq α] [DecidableEq β] (p₀ : α × β → ℝ) (f : Equiv.Perm (α × β)) :
    ∃ n : ℕ, 0 < n ∧ (fun x => p₀ ((f ^ n).symm x)) = p₀ := by
  refine ⟨orderOf f, orderOf_pos f, ?_⟩
  rw [pow_orderOf_eq_one]
  rfl

/-- **E8** what claim 5 can honestly say: every time is at least as correlated as the product start. -/
theorem parts_gain_nonneg_all_t (q : α → ℝ) (r : β → ℝ) (hq : ∀ a, 0 ≤ q a) (hr : ∀ b, 0 ≤ r b)
    (hq1 : ∑ a, q a = 1) (hr1 : ∑ b, r b = 1) (f : Equiv.Perm (α × β)) (t : ℕ) :
    0 ≤ I (fun x => q ((f ^ t).symm x).1 * r ((f ^ t).symm x).2) := by
  apply mutual_info_nonneg
  · intro x; exact mul_nonneg (hq _) (hr _)
  · rw [sum_comp_symm (fun x : α × β => q x.1 * r x.2) (f ^ t), Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hr1, mul_one, hq1]

/-- **E9** classical caps on the correlation (proved in review_adjudicator/Adjudicator.lean as `I_le`). -/
theorem I_le (p : α × β → ℝ) (hp : ∀ x, 0 ≤ p x) :
    I p ≤ H (margA p) ∧ I p ≤ H (margB p) ∧ I p ≤ H p := by
  have := H_margA_le p hp; have := H_margB_le p hp
  unfold I; refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- **E10** the bipartite gain is capped by the system's size. -/
theorem I_le_log_card (p : α × β → ℝ) (hp : ∀ x, 0 ≤ p x) (h1 : ∑ x, p x = 1) :
    I p ≤ Real.log (Fintype.card α) :=
  (I_le p hp).1.trans
    (H_le_log_card (margA p) (margA_nonneg p hp) ((margA_sum p).trans h1))

/-- **E11** product-ness is not enough: the gain is capped by the starting entropy's distance from its maximum
(and by the starting entropy itself, via E9). -/
theorem gain_le_entropy_deficit (q : α → ℝ) (r : β → ℝ) (hq : ∀ a, 0 ≤ q a) (hr : ∀ b, 0 ≤ r b)
    (hq1 : ∑ a, q a = 1) (hr1 : ∑ b, r b = 1) (f : α × β ≃ α × β) :
    I (fun x => q (f.symm x).1 * r (f.symm x).2)
      ≤ Real.log (Fintype.card α) + Real.log (Fintype.card β) - (H q + H r) := by
  set p₁ : α × β → ℝ := fun x => q (f.symm x).1 * r (f.symm x).2 with hp₁
  have hp : ∀ x, 0 ≤ p₁ x := fun x => mul_nonneg (hq _) (hr _)
  have hs : ∑ x, p₁ x = 1 := by
    rw [hp₁, sum_comp_symm (fun x : α × β => q x.1 * r x.2) f, Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hr1, mul_one, hq1]
  have hH : H p₁ = H q + H r := by
    rw [hp₁, H_comp (fun x : α × β => q x.1 * r x.2) f, H_prod q r hq1 hr1]
  have hA := H_le_log_card (margA p₁) (margA_nonneg p₁ hp) ((margA_sum p₁).trans hs)
  have hB := H_le_log_card (margB p₁) (margB_nonneg p₁ hp) ((margB_sum p₁).trans hs)
  unfold I
  linarith

theorem I_eq_KL (p : α × β → ℝ) (hp : ∀ x, 0 ≤ p x) (h1 : ∑ x, p x = 1) :
    I p = KL p (fun x => margA p x.1 * margB p x.2) :=
  I_eq_sum p hp

/-- **E12** I is exactly "the correlation". -/
theorem I_eq_zero_iff_product (p : α × β → ℝ) (hp : ∀ x, 0 ≤ p x) (h1 : ∑ x, p x = 1) :
    I p = 0 ↔ ∀ a b, p (a, b) = margA p a * margB p b := by
  have hpA : ∀ a b, p (a, b) ≤ margA p a := fun a b =>
    Finset.single_le_sum (f := fun b => p (a, b)) (fun b _ => hp (a, b)) (Finset.mem_univ b)
  have hpB : ∀ a b, p (a, b) ≤ margB p b := fun a b =>
    Finset.single_le_sum (f := fun a => p (a, b)) (fun a _ => hp (a, b)) (Finset.mem_univ a)
  set t : α × β → ℝ := fun x => p x * log (p x / (margA p x.1 * margB p x.2))
    - (p x - margA p x.1 * margB p x.2) with ht
  have hprod : ∑ x : α × β, margA p x.1 * margB p x.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, margB_sum, margA_sum, h1, mul_one]
  have hIt : I p = ∑ x, t x := by
    rw [I_eq_sum p hp, ht]
    simp only [Finset.sum_sub_distrib, h1, hprod, sub_self, sub_zero]
  have htnn : ∀ x, 0 ≤ t x := by
    rintro ⟨a, b⟩
    simp only [ht]
    rcases (hp (a, b)).eq_or_lt with h0 | hpos
    · rw [← h0]; simp only [zero_mul, zero_sub, sub_neg_eq_add, zero_add]
      exact mul_nonneg (margA_nonneg p hp a) (margB_nonneg p hp b)
    · have ha : 0 < margA p a := lt_of_lt_of_le hpos (hpA a b)
      have hb : 0 < margB p b := lt_of_lt_of_le hpos (hpB a b)
      linarith [mul_log_div_ge hpos.le (mul_pos ha hb)]
  have htz : ∀ x : α × β, t x = 0 ↔ p x = margA p x.1 * margB p x.2 := by
    rintro ⟨a, b⟩
    simp only [ht]
    constructor
    · intro h
      by_contra hne
      rcases (hp (a, b)).eq_or_lt with h0 | hpos
      · rw [← h0] at h hne
        simp only [zero_mul, zero_sub, sub_neg_eq_add, zero_add] at h
        exact hne h.symm
      · have ha : 0 < margA p a := lt_of_lt_of_le hpos (hpA a b)
        have hb : 0 < margB p b := lt_of_lt_of_le hpos (hpB a b)
        linarith [mul_log_div_gt hpos.le (mul_pos ha hb) hne]
    · intro h
      rw [← h]
      rcases (hp (a, b)).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · rw [div_self hpos.ne', Real.log_one]; ring
  rw [hIt, Finset.sum_eq_zero_iff_of_nonneg (fun x _ => htnn x)]
  constructor
  · intro h a b; exact (htz (a, b)).1 (h (a, b) (Finset.mem_univ _))
  · intro h x _; exact (htz x).2 (h x.1 x.2)

/-- **E13** claim 4, the true one-sided half (M3 restated in these defs). -/
theorem one_sided_blind (p : α × β → ℝ) (h1 : ∑ x, p x = 1) (g : α → ℝ) :
    ∑ x : α × β, p x * g x.1 = ∑ x : α × β, (margA p x.1 * margB p x.2) * g x.1 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro a _
  have hB : ∑ b, margB p b = 1 := (margB_sum p).trans h1
  calc ∑ b, p (a, b) * g a = margA p a * g a := by rw [← Finset.sum_mul]; rfl
    _ = ∑ b, margA p a * margB p b * g a := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, hB, mul_one]

/-- **E14** claim 4, the false two-sided reading: a product observable reads the CNOT-copy correlation. -/
theorem two_sided_sees :
    let p : Bool × Bool → ℝ := fun x => if x.1 = x.2 then 1/2 else 0
    let g : Bool → ℝ := fun b => if b then 1 else 0
    ∑ x : Bool × Bool, p x * (g x.1 * g x.2) ≠ ∑ x : Bool × Bool, (margA p x.1 * margB p x.2) * (g x.1 * g x.2) := by
  intro p g
  simp only [p, g, margA, margB, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

/-- **E15** classical ELB step (ii): with a Gibbs reservoir, β·ΔE_R = ΔH_R + KL(r'‖r). -/
theorem gibbs_heat_identity (E : β → ℝ) (bβ : ℝ) (r' : β → ℝ) (hr' : ∀ b, 0 ≤ r' b) (hr'1 : ∑ b, r' b = 1) :
    let Z : ℝ := ∑ b, Real.exp (-bβ * E b)
    let r : β → ℝ := fun b => Real.exp (-bβ * E b) / Z
    bβ * (∑ b, r' b * E b - ∑ b, r b * E b) = (H r' - H r) + KL r' r := by
  intro Z r
  have hne : Nonempty β := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    simp at hr'1
  have hZ : 0 < Z := Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hr : ∀ b, 0 < r b := fun b => div_pos (Real.exp_pos _) hZ
  have hr1 : ∑ b, r b = 1 := by
    simp only [r]; rw [← Finset.sum_div]; exact div_self hZ.ne'
  have hlog : ∀ b, Real.log (r b) = -bβ * E b - Real.log Z := by
    intro b; simp only [r]; rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  have hHr : H r = bβ * ∑ b, r b * E b + Real.log Z := by
    unfold H
    simp only [Real.negMulLog, hlog]
    have : ∀ b, -r b * (-bβ * E b - Real.log Z) = bβ * (r b * E b) + Real.log Z * r b := by
      intro b; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hr1, mul_one]
  have hKL : KL r' r = - H r' + bβ * ∑ b, r' b * E b + Real.log Z := by
    unfold KL H
    have : ∀ b, r' b * Real.log (r' b / r b)
        = -negMulLog (r' b) + bβ * (r' b * E b) + Real.log Z * r' b := by
      intro b
      rcases (hr' b).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · rw [Real.log_div hpos.ne' (hr b).ne', hlog, Real.negMulLog]; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, hr'1, mul_one]
  rw [hHr, hKL]
  ring

/-- **E16** full classical ELB: product start with a Gibbs reservoir, any bijection.
Σ := ΔH_S + β·ΔE_R = I p₁ + KL(margB p₁ ‖ r) ≥ 0. (Calling β·ΔE_R "heat" also needs f to conserve energy.) -/
theorem elb_classical [Nonempty β] (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1) (E : β → ℝ) (bβ : ℝ)
    (f : α × β ≃ α × β) :
    let Z : ℝ := ∑ b, Real.exp (-bβ * E b)
    let r : β → ℝ := fun b => Real.exp (-bβ * E b) / Z
    let p₀ : α × β → ℝ := fun x => q x.1 * r x.2
    let p₁ : α × β → ℝ := fun x => p₀ (f.symm x)
    (H (margA p₁) - H q) + bβ * (∑ b, margB p₁ b * E b - ∑ b, r b * E b)
      = I p₁ + KL (margB p₁) r ∧ 0 ≤ KL (margB p₁) r := by
  intro Z r p₀ p₁
  have hZ : 0 < Z := Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hr : ∀ b, 0 < r b := fun b => div_pos (Real.exp_pos _) hZ
  have hr1 : ∑ b, r b = 1 := by
    simp only [r]; rw [← Finset.sum_div]; exact div_self hZ.ne'
  have hp : ∀ x, 0 ≤ p₁ x := fun x => mul_nonneg (hq _) (hr _).le
  have hs : ∑ x, p₁ x = 1 := by
    simp only [p₁]
    rw [sum_comp_symm p₀ f, Fintype.sum_prod_type]
    simp only [p₀, ← Finset.mul_sum, hr1, mul_one, hq1]
  have hB1 : ∑ b, margB p₁ b = 1 := (margB_sum p₁).trans hs
  have hgibbs := gibbs_heat_identity E bβ (margB p₁) (margB_nonneg p₁ hp) hB1
  have hH : H p₁ = H q + H r := by
    simp only [p₁]; rw [H_comp p₀ f]; exact H_prod q r hq1 hr1
  refine ⟨?_, KL_nonneg (margB p₁) r (margB_nonneg p₁ hp) hr hB1 hr1⟩
  simp only at hgibbs
  rw [hgibbs]
  unfold I
  rw [hH]
  ring

/-- **E4'** witness tied to E3 and testing the action's direction: a non-involutive 3-cycle on the
environment controlled by the system. -/
def shift3 : Bool × Fin 3 ≃ Bool × Fin 3 where
  toFun x := (x.1, if x.1 then x.2 + 1 else x.2)
  invFun x := (x.1, if x.1 then x.2 - 1 else x.2)
  left_inv x := by cases x with | mk a b => cases a <;> simp
  right_inv x := by cases x with | mk a b => cases a <;> simp

theorem shift3_not_involutive : ⇑shift3.symm ≠ ⇑shift3 := by
  intro h
  have := congrFun h (true, 0)
  simp [shift3] at this
  revert this
  decide

end EntropyConserved
