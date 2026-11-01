import Mathlib
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} (d : ι)
example (a : α d) (r : ∀ j : {j // j ≠ d}, α j) : (Equiv.piSplitAt d α).symm (a, r) d = a := by simp
example (a : α d) (r : ∀ j : {j // j ≠ d}, α j) {j : ι} (hj : j ≠ d) : (Equiv.piSplitAt d α).symm (a, r) j = r ⟨j, hj⟩ := by simp [hj]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
example : ContinuousLinearMap.pi (Pi.single d (ContinuousLinearMap.id ℝ (E d))) = ContinuousLinearMap.single ℝ E d := by
  ext x j
  by_cases hj : j = d
  · subst hj; simp
  · simp [hj, Pi.single_eq_of_ne hj]
#check @Equiv.boolArrowEquivProd
#check @Equiv.boolArrowEquivProd_symm_apply
#check @div_le_one₀
#check @div_le_one_of_le₀
#check @Finset.Subset.antisymm
#check @Finset.induction_on
#check @Quotient.sound
#check @Quotient.exact
example (S : Type) (s : Setoid S) (a b : S) (h : s a b) : Quotient.mk s a = Quotient.mk s b := Quotient.sound h
example (S : Type) (s : Setoid S) (a b : S) (h : Quotient.mk s a = Quotient.mk s b) : s a b := Quotient.exact h
example (S T : Type) (f : S → T) (a b : S) (h : f a = f b) : Setoid.ker f a b := h
#check @Function.ne_iff
#check @Finset.prod_le_one
#check @mul_le_of_le_one_right
