import Mathlib

namespace R
open Real Finset
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def H {γ : Type*} [Fintype γ] (p : γ → ℝ) : ℝ := ∑ x, negMulLog (p x)
def margA (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)
def margB (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)
noncomputable def I (p : α × β → ℝ) : ℝ := H (margA p) + H (margB p) - H p

def cnot : Bool × Bool ≃ Bool × Bool where
  toFun x := (x.1, xor x.2 x.1)
  invFun x := (x.1, xor x.2 x.1)
  left_inv x := by cases x with | mk a b => cases a <;> cases b <;> rfl
  right_inv x := by cases x with | mk a b => cases a <;> cases b <;> rfl

-- (a) E1 is not about Shannon entropy: ANY separable functional is invariant, no hypotheses on p.
theorem any_phi_conserved {γ : Type*} [Fintype γ] (φ : ℝ → ℝ) (p : γ → ℝ) (f : γ ≃ γ) :
    ∑ x, φ (p (f.symm x)) = ∑ x, φ (p x) := Equiv.sum_comp f.symm (fun y => φ (p y))

-- (b) The p ∘ f convention proves the same E1 (direction is undetected).
theorem E1_wrong_direction (p : α × β → ℝ) (f : α × β ≃ α × β) : H (fun x => p (f x)) = H p := by
  unfold H; exact Equiv.sum_comp f (fun y => negMulLog (p y))

-- (c) cnot is an involution, so E4 cannot distinguish p ∘ cnot from p ∘ cnot.symm.
theorem cnot_symm : ⇑cnot.symm = ⇑cnot := by
  funext x; cases x with | mk a b => cases a <;> cases b <;> rfl

-- (d) Recurrence: every finite bijection has finite order, so I returns EXACTLY to I p₀ = 0.
theorem recurrence (f : Equiv.Perm (α × β)) : ∃ n, 0 < n ∧ f ^ n = 1 :=
  ⟨orderOf f, (isOfFinOrder_of_finite f).orderOf_pos, pow_orderOf_eq_one f⟩

-- (e) Concretely: one more CNOT step after E4 DEcreases the parts' entropy by log 2.
theorem second_step_decreases :
    let q : Bool → ℝ := fun _ => 1 / 2
    let r : Bool → ℝ := fun e => if e then 0 else 1
    let p₀ : Bool × Bool → ℝ := fun x => q x.1 * r x.2
    let p₁ : Bool × Bool → ℝ := fun x => p₀ (cnot.symm x)
    let p₂ : Bool × Bool → ℝ := fun x => p₁ (cnot.symm x)
    (H (margA p₂) + H (margB p₂)) - (H (margA p₁) + H (margB p₁)) = - Real.log 2 ∧ I p₂ = 0 := by
  intro q r p₀ p₁ p₂
  constructor
  · simp only [H, margA, margB, p₂, p₁, p₀, q, r, cnot, Equiv.coe_fn_symm_mk, Fintype.sum_bool]
    norm_num [Real.negMulLog, Real.log_inv]
    rw [show Real.log (1 / 2) = -Real.log 2 by rw [one_div, Real.log_inv]]; ring
  · simp only [I, H, margA, margB, p₂, p₁, p₀, q, r, cnot, Equiv.coe_fn_symm_mk, Fintype.sum_bool,
      Fintype.sum_prod_type]
    norm_num [Real.negMulLog, Real.log_inv]

-- (f) Bistochastic (non-bijective) step: averaging the two CNOT branches. H strictly rises:
-- the model excludes stochastic dynamics, where E1 fails.
theorem stochastic_breaks_E1 :
    let p : Bool → ℝ := fun b => if b then 0 else 1
    let p' : Bool → ℝ := fun _ => 1 / 2   -- image of p under the doubly-stochastic matrix [[1/2,1/2],[1/2,1/2]]
    H p' - H p = Real.log 2 := by
  intro p p'
  simp only [H, p, p', Fintype.sum_bool]
  norm_num [Real.negMulLog, Real.log_inv]
  rw [show Real.log (1 / 2) = -Real.log 2 by rw [one_div, Real.log_inv]]; ring

end R
