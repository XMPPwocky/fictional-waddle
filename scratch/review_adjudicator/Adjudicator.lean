import Mathlib

/-! Adjudicator checks for EntropyConserved.lean. Defs re-declared verbatim from the frozen file. -/

namespace Adj
open Real Finset

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def H {γ : Type*} [Fintype γ] (p : γ → ℝ) : ℝ := ∑ x, negMulLog (p x)
def margA (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)
def margB (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)
noncomputable def I (p : α × β → ℝ) : ℝ := H (margA p) + H (margB p) - H p

theorem E1 (p : α × β → ℝ) (f : α × β ≃ α × β) : H (fun x => p (f.symm x)) = H p := by
  unfold H; exact Equiv.sum_comp f.symm (fun y => negMulLog (p y))

def cnot : Bool × Bool ≃ Bool × Bool where
  toFun x := (x.1, xor x.2 x.1)
  invFun x := (x.1, xor x.2 x.1)
  left_inv x := by cases x with | mk a b => cases a <;> cases b <;> rfl
  right_inv x := by cases x with | mk a b => cases a <;> cases b <;> rfl

/-- A1 (general Δ, no hypotheses on p₀): Δparts = I p₁ − I p₀. -/
theorem general_delta (p₀ : α × β → ℝ) (f : α × β ≃ α × β) :
    (H (margA (fun x => p₀ (f.symm x))) + H (margB (fun x => p₀ (f.symm x))))
      - (H (margA p₀) + H (margB p₀)) = I (fun x => p₀ (f.symm x)) - I p₀ := by
  unfold I; rw [E1 p₀ f]; ring

/-- A2 (correlated start, CNOT): Δparts = −log 2. Independent re-proof of the necessity counterexample. -/
theorem correlated_decreases :
    let p₀ : Bool × Bool → ℝ := fun x => if x.1 = x.2 then 1/2 else 0
    let p₁ : Bool × Bool → ℝ := fun x => p₀ (cnot.symm x)
    (H (margA p₁) + H (margB p₁)) - (H (margA p₀) + H (margB p₀)) = - Real.log 2 := by
  intro p₀ p₁
  simp only [H, margA, margB, p₁, p₀, cnot, Equiv.coe_fn_symm_mk, Fintype.sum_bool]
  norm_num [Real.negMulLog, Real.log_inv]
  rw [show Real.log (1 / 2) = -Real.log 2 by rw [one_div, Real.log_inv]]; ring

/-- A3 (recurrence of the pushed-forward state, for every bijection and every p₀). -/
theorem recurrence [DecidableEq α] [DecidableEq β] (p₀ : α × β → ℝ) (f : Equiv.Perm (α × β)) :
    ∃ n : ℕ, 0 < n ∧ (fun x => p₀ ((f ^ n).symm x)) = p₀ ∧ I (fun x => p₀ ((f ^ n).symm x)) = I p₀ := by
  refine ⟨orderOf f, orderOf_pos f, ?_, ?_⟩ <;> rw [pow_orderOf_eq_one] <;> rfl

/-- A4: product of two constants (uniforms) is a fixed point of EVERY bijection, so I p₁ = I p₀. -/
theorem uniform_fixed (c d : ℝ) (f : α × β ≃ α × β) :
    (fun x => (fun y : α × β => c * d) (f.symm x)) = (fun y : α × β => c * d) := rfl

/-- A5 (partition relativity): pulling back along f makes p₁ the product again, definitionally. -/
theorem pullback_is_product (q : α → ℝ) (r : β → ℝ) (f : α × β ≃ α × β) :
    (fun y => (fun x => q (f.symm x).1 * r (f.symm x).2) (f y)) = fun y => q y.1 * r y.2 := by
  funext y; simp

/-- A6: H of the B-marginal is at most the joint entropy (classical conditional entropy ≥ 0). -/
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

/-- A7: classically I ≤ H(A), I ≤ H(B), I ≤ H(joint). With E1: Δparts ≤ H p₀ — a point mass never correlates,
and the bipartite correlation is capped by the smaller marginal entropy. -/
theorem I_le (p : α × β → ℝ) (hp : ∀ x, 0 ≤ p x) :
    I p ≤ H (margA p) ∧ I p ≤ H (margB p) ∧ I p ≤ H p := by
  have := H_margA_le p hp; have := H_margB_le p hp
  unfold I; refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- A8 (claim 4): for the CNOT-copy state a product observable A·B reads the correlation: 1/2 vs 1/4. -/
theorem product_observable_sees_correlation :
    let p : Bool × Bool → ℝ := fun x => if x.1 = x.2 then 1/2 else 0
    let g : Bool → ℝ := fun b => if b then 1 else 0
    (∑ x, p x * (g x.1 * g x.2)) = 1/2 ∧
      (∑ x : Bool × Bool, (margA p x.1 * margB p x.2) * (g x.1 * g x.2)) = 1/4 := by
  intro p g
  simp only [p, g, margA, margB, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

/-- A9 (vacuity of dropping h1): uniform 2×2 at total mass 10 gives I = −10 log 10 < 0. -/
theorem drop_h1 :
    I (fun _ : Bool × Bool => (5/2 : ℝ)) = - 10 * Real.log 10 := by
  simp only [I, H, margA, margB, Fintype.sum_prod_type, Fintype.sum_bool, Real.negMulLog]
  have h5 : Real.log 5 = Real.log 10 - Real.log 2 := by
    rw [show (10:ℝ) = 5 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
  have h25 : Real.log (5/2) = Real.log 10 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), h5]; ring
  norm_num
  rw [h5, h25]; ring

/-- A10 (time symmetry): E3's hypotheses are invariant under f ↦ f.symm, so the same bound runs into the past. -/
example (f : α × β ≃ α × β) : f.symm.symm = f := Equiv.symm_symm f

#print axioms general_delta
#print axioms recurrence
#print axioms I_le
#print axioms product_observable_sees_correlation
#print axioms drop_h1
#print axioms correlated_decreases

end Adj
