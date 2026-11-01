import Mathlib
namespace EC
open Real Finset
variable {α β : Type*} [Fintype α] [Fintype β]
noncomputable def H {γ : Type*} [Fintype γ] (p : γ → ℝ) : ℝ := ∑ x, negMulLog (p x)
def margA (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)
def margB (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)
def cnot : Bool × Bool ≃ Bool × Bool where
  toFun x := (x.1, xor x.2 x.1)
  invFun x := (x.1, xor x.2 x.1)
  left_inv x := by cases x with | mk a b => cases a <;> cases b <;> rfl
  right_inv x := by cases x with | mk a b => cases a <;> cases b <;> rfl

/-- correlated start: perfectly correlated bits -/
noncomputable def p₀ : Bool × Bool → ℝ := fun x => if x.1 = x.2 then 1/2 else 0
noncomputable def p₁ : Bool × Bool → ℝ := fun x => p₀ (cnot.symm x)

theorem parts_decrease :
    (H (margA p₁) + H (margB p₁)) - (H (margA p₀) + H (margB p₀)) = - Real.log 2 ∧ Real.log 2 > 0 := by
  refine ⟨?_, Real.log_pos (by norm_num)⟩
  simp only [H, margA, margB, p₁, p₀, cnot, Equiv.coe_fn_symm_mk, Fintype.sum_bool]
  norm_num [Real.negMulLog, Real.log_inv]
  rw [show Real.log (1 / 2) = -Real.log 2 by rw [one_div, Real.log_inv]]; ring
#print axioms parts_decrease
end EC
