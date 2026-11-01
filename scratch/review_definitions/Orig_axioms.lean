import Mathlib

/-!
# Fine-grained entropy is conserved; the parts' entropy grows by exactly the correlation

Finite system `α`, finite environment `β`, joint distribution `p : α × β → ℝ`. Shannon entropy in nats,
`H p = ∑ x, negMulLog (p x)` with `negMulLog x = −x log x` (and `negMulLog 0 = 0`). Marginals `margA`, `margB`.
Mutual information `I p = H (margA p) + H (margB p) − H p`. Reversible joint dynamics is a bijection
`f : α × β ≃ α × β`, acting on distributions by `p ↦ p ∘ f.symm`.

* E1 `joint_entropy_conserved`: `H (p ∘ f.symm) = H p` for every bijection `f`. Fine-grained entropy is conserved.
* E2 `mutual_info_nonneg`: `0 ≤ I p` for every probability distribution (subadditivity). The parts never hold less
  entropy than the whole.
* E3 `second_law_from_reversibility`: start from an UNCORRELATED (product) state `p₀ = q ⊗ r` and apply any
  bijection. Then the joint entropy is unchanged, the parts' total entropy changes by EXACTLY `I(p₁)`, and that
  change is `≥ 0`.
* E4 `copy_makes_strict_increase`: non-vacuity. With `q` uniform on `Bool`, `r` concentrated at `false`, and `f` the
  CNOT copy, the parts' entropy rises by exactly `log 2 > 0`.

Not formalized here: the thermodynamic factor (kT per nat), and the environment's relative-entropy term in Esposito,
Lindenberg & Van den Broeck (2010). E3 is the information-only core of that identity.
-/

namespace EntropyConserved

open Real Finset

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Shannon entropy in nats. -/
noncomputable def H {γ : Type*} [Fintype γ] (p : γ → ℝ) : ℝ := ∑ x, negMulLog (p x)

def margA (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)
def margB (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)

/-- Mutual information in nats. -/
noncomputable def I (p : α × β → ℝ) : ℝ := H (margA p) + H (margB p) - H p

/-- **E1.** -/
theorem joint_entropy_conserved (p : α × β → ℝ) (f : α × β ≃ α × β) : H (fun x => p (f.symm x)) = H p := by
  unfold H
  exact Equiv.sum_comp f.symm (fun y => negMulLog (p y))

/-- **E2.** -/
theorem mutual_info_nonneg (p : α × β → ℝ) (hp : ∀ x, 0 ≤ p x) (h1 : ∑ x, p x = 1) : 0 ≤ I p := by
  classical
  set A := margA p with hAdef
  set B := margB p with hBdef
  have hA : ∀ a, 0 ≤ A a := fun a => Finset.sum_nonneg (fun b _ => hp (a, b))
  have hB : ∀ b, 0 ≤ B b := fun b => Finset.sum_nonneg (fun a _ => hp (a, b))
  have hpA : ∀ a b, p (a, b) ≤ A a := fun a b =>
    Finset.single_le_sum (f := fun b => p (a, b)) (fun b _ => hp (a, b)) (Finset.mem_univ b)
  have hpB : ∀ a b, p (a, b) ≤ B b := fun a b =>
    Finset.single_le_sum (f := fun a => p (a, b)) (fun a _ => hp (a, b)) (Finset.mem_univ a)
  have hsum : ∑ a, ∑ b, p (a, b) = 1 := by rw [← Fintype.sum_prod_type (f := p)]; exact h1
  have hA1 : ∑ a, A a = 1 := hsum
  have hB1 : ∑ b, B b = 1 := by
    show ∑ b, ∑ a, p (a, b) = 1
    rw [Finset.sum_comm]; exact hsum
  have key : ∀ a b, p (a, b) * (log (A a) + log (B b) - log (p (a, b))) ≤ A a * B b - p (a, b) := by
    intro a b
    rcases (hp (a, b)).eq_or_lt with h0 | hpos
    · rw [← h0]; simp only [zero_mul, sub_zero]; exact mul_nonneg (hA a) (hB b)
    · have ha : 0 < A a := lt_of_lt_of_le hpos (hpA a b)
      have hb : 0 < B b := lt_of_lt_of_le hpos (hpB a b)
      have hx : 0 < A a * B b / p (a, b) := by positivity
      have hlog := Real.log_le_sub_one_of_pos hx
      rw [Real.log_div (by positivity) hpos.ne', Real.log_mul ha.ne' hb.ne'] at hlog
      calc p (a, b) * (log (A a) + log (B b) - log (p (a, b)))
          ≤ p (a, b) * (A a * B b / p (a, b) - 1) := mul_le_mul_of_nonneg_left hlog hpos.le
        _ = A a * B b - p (a, b) := by field_simp
  have sumkey : ∑ a, ∑ b, p (a, b) * (log (A a) + log (B b) - log (p (a, b))) ≤ 0 := by
    calc _ ≤ ∑ a, ∑ b, (A a * B b - p (a, b)) :=
          Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => key a b))
      _ = (∑ a, A a) * (∑ b, B b) - ∑ a, ∑ b, p (a, b) := by
          rw [Finset.sum_mul_sum]; simp only [Finset.sum_sub_distrib]
      _ = 0 := by rw [hA1, hB1, hsum]; ring
  have e1 : ∑ a, ∑ b, p (a, b) * log (A a) = ∑ a, A a * log (A a) := by
    apply Finset.sum_congr rfl; intro a _; rw [← Finset.sum_mul]; rfl
  have e2 : ∑ a, ∑ b, p (a, b) * log (B b) = ∑ b, B b * log (B b) := by
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _; rw [← Finset.sum_mul]; rfl
  have e3 : ∑ a, ∑ b, p (a, b) * log (p (a, b)) = ∑ x, p x * log (p x) :=
    (Fintype.sum_prod_type (f := fun x => p x * log (p x))).symm
  have split : ∑ a, ∑ b, p (a, b) * (log (A a) + log (B b) - log (p (a, b)))
      = ∑ a, A a * log (A a) + ∑ b, B b * log (B b) - ∑ x, p x * log (p x) := by
    simp only [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]; rw [e1, e2, e3]
  rw [split] at sumkey
  unfold I H
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  linarith

/-- **E3.** -/
theorem second_law_from_reversibility (q : α → ℝ) (r : β → ℝ) (hq : ∀ a, 0 ≤ q a) (hr : ∀ b, 0 ≤ r b)
    (hq1 : ∑ a, q a = 1) (hr1 : ∑ b, r b = 1) (f : α × β ≃ α × β) :
    let p₀ : α × β → ℝ := fun x => q x.1 * r x.2
    let p₁ : α × β → ℝ := fun x => p₀ (f.symm x)
    H p₁ = H p₀ ∧
      (H (margA p₁) + H (margB p₁)) - (H (margA p₀) + H (margB p₀)) = I p₁ ∧
      0 ≤ I p₁ := by
  intro p₀ p₁
  have hmA : margA p₀ = q := by
    funext a; show ∑ b, q a * r b = q a; rw [← Finset.mul_sum, hr1, mul_one]
  have hmB : margB p₀ = r := by
    funext b; show ∑ a, q a * r b = r b; rw [← Finset.sum_mul, hq1, one_mul]
  have hH0 : H p₀ = H q + H r := by
    unfold H
    rw [Fintype.sum_prod_type]
    simp only [p₀, Real.negMulLog_mul, Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl; intro a _; rw [← Finset.sum_mul, hr1, one_mul]
    · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _; rw [← Finset.sum_mul, hq1, one_mul]
  have hcons : H p₁ = H p₀ := joint_entropy_conserved p₀ f
  have hp1 : ∀ x, 0 ≤ p₁ x := fun x => mul_nonneg (hq _) (hr _)
  have hs1 : ∑ x, p₁ x = 1 := by
    show ∑ x, p₀ (f.symm x) = 1
    rw [Equiv.sum_comp f.symm p₀, Fintype.sum_prod_type]
    simp only [p₀, ← Finset.mul_sum, hr1, mul_one, hq1]
  refine ⟨hcons, ?_, mutual_info_nonneg p₁ hp1 hs1⟩
  unfold I
  rw [hmA, hmB, hcons, hH0]

/-- The CNOT copy `(s, e) ↦ (s, e xor s)` as a bijection. -/
def cnot : Bool × Bool ≃ Bool × Bool where
  toFun x := (x.1, xor x.2 x.1)
  invFun x := (x.1, xor x.2 x.1)
  left_inv x := by cases x with | mk a b => cases a <;> cases b <;> rfl
  right_inv x := by cases x with | mk a b => cases a <;> cases b <;> rfl

/-- **E4.** -/
theorem copy_makes_strict_increase :
    let q : Bool → ℝ := fun _ => 1 / 2
    let r : Bool → ℝ := fun e => if e then 0 else 1
    let p₀ : Bool × Bool → ℝ := fun x => q x.1 * r x.2
    let p₁ : Bool × Bool → ℝ := fun x => p₀ (cnot.symm x)
    (H (margA p₁) + H (margB p₁)) - (H (margA p₀) + H (margB p₀)) = Real.log 2 ∧ 0 < Real.log 2 := by
  intro q r p₀ p₁
  refine ⟨?_, Real.log_pos (by norm_num)⟩
  simp only [H, margA, margB, p₁, p₀, q, r, cnot, Equiv.coe_fn_symm_mk, Fintype.sum_bool]
  norm_num [Real.negMulLog, Real.log_inv]
  rw [show Real.log (1 / 2) = -Real.log 2 by rw [one_div, Real.log_inv]]; ring

#print axioms EntropyConserved.second_law_from_reversibility
#print axioms EntropyConserved.copy_makes_strict_increase
end EntropyConserved
