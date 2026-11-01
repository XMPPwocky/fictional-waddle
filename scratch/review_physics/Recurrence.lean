import Mathlib
/-! Review (physics lens): the CNOT of E4 is an involution, so the E4 orbit returns to the product state at t = 2.
E3 compares t with 0 only; it gives no monotone arrow. Also: any bijection of a finite set has finite order. -/
def cnot : Bool × Bool ≃ Bool × Bool where
  toFun x := (x.1, xor x.2 x.1)
  invFun x := (x.1, xor x.2 x.1)
  left_inv x := by cases x with | mk a b => cases a <;> cases b <;> rfl
  right_inv x := by cases x with | mk a b => cases a <;> cases b <;> rfl

theorem cnot_twice : cnot.trans cnot = Equiv.refl _ := by
  ext x <;> (cases x with | mk a b => cases a <;> cases b <;> rfl)

theorem p2_eq_p0 (p₀ : Bool × Bool → ℝ) :
    (fun x => (fun y => p₀ (cnot.symm y)) (cnot.symm x)) = p₀ := by
  funext x; cases x with | mk a b => cases a <;> cases b <;> rfl

/-- Poincaré recurrence, discrete and exact: every permutation of a finite type has a positive power equal to id. -/
theorem finite_recurrence {γ : Type*} [Fintype γ] [DecidableEq γ] (f : Equiv.Perm γ) :
    ∃ n, 0 < n ∧ f ^ n = 1 := ⟨orderOf f, orderOf_pos f, pow_orderOf_eq_one f⟩
