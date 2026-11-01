import Mathlib

namespace FidelityCheck
open Real Finset

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def H {γ : Type*} [Fintype γ] (p : γ → ℝ) : ℝ := ∑ x, negMulLog (p x)
def margA (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)
def margB (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)
noncomputable def I (p : α × β → ℝ) : ℝ := H (margA p) + H (margB p) - H p

theorem E1 (p : α × β → ℝ) (f : α × β ≃ α × β) : H (fun x => p (f.symm x)) = H p := by
  unfold H; exact Equiv.sum_comp f.symm (fun y => negMulLog (p y))

/-- F1: the chat identity of claim 2 is definitional; no hypotheses at all (not even p a distribution). -/
example (p : α × β → ℝ) : H (margA p) + H (margB p) = H p + I p := by unfold I; ring

/-- F2: general case (any start, any bijection): parts change by Δ I, not by I p₁. -/
theorem general_delta (p₀ : α × β → ℝ) (f : α × β ≃ α × β) :
    let p₁ : α × β → ℝ := fun x => p₀ (f.symm x)
    (H (margA p₁) + H (margB p₁)) - (H (margA p₀) + H (margB p₀)) = I p₁ - I p₀ := by
  intro p₁; unfold I; rw [E1 p₀ f]; ring

def cnot : Bool × Bool ≃ Bool × Bool where
  toFun x := (x.1, xor x.2 x.1)
  invFun x := (x.1, xor x.2 x.1)
  left_inv x := by cases x with | mk a b => cases a <;> cases b <;> rfl
  right_inv x := by cases x with | mk a b => cases a <;> cases b <;> rfl

/-- F3: correlated start (the copy state), same CNOT: parts' entropy DROPS by log 2.
    So E3's product hypothesis is load-bearing (supports claim 5's "input" wording). -/
theorem correlated_start_decreases :
    let p₀ : Bool × Bool → ℝ := fun x => if x.1 = x.2 then 1/2 else 0
    let p₁ : Bool × Bool → ℝ := fun x => p₀ (cnot.symm x)
    (H (margA p₁) + H (margB p₁)) - (H (margA p₀) + H (margB p₀)) = - Real.log 2 := by
  intro p₀ p₁
  simp only [H, margA, margB, p₁, p₀, cnot, Equiv.coe_fn_symm_mk, Fintype.sum_bool]
  norm_num [Real.negMulLog, Real.log_inv]
  rw [show Real.log (1 / 2) = -Real.log 2 by rw [one_div, Real.log_inv]]; ring

/-- F4: recurrence. For ANY bijection of a finite joint space there is n > 0 with fⁿ = id,
    so the evolved state returns exactly to the product start and I returns to its initial value.
    "Arrow of time = growth of I" is not monotone in this model. -/
theorem recurrence [DecidableEq α] [DecidableEq β] (p₀ : α × β → ℝ) (f : Equiv.Perm (α × β)) :
    ∃ n : ℕ, 0 < n ∧ (fun x => p₀ ((f ^ n).symm x)) = p₀ := by
  refine ⟨orderOf f, orderOf_pos f, ?_⟩
  rw [pow_orderOf_eq_one]; rfl

end FidelityCheck
