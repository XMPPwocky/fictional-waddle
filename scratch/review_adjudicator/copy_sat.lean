import Mathlib
example : (∀ a:Bool, (0:ℝ) ≤ 1/2) ∧ (∀ b:Bool, (0:ℝ) ≤ (if b then 0 else 1)) ∧ ∑ a:Bool, (1/2:ℝ) = 1 ∧ ∑ b:Bool, (if b then (0:ℝ) else 1) = 1 := by
  refine ⟨fun _ => by norm_num, fun b => by split_ifs <;> norm_num, ?_, ?_⟩ <;> simp [Fintype.sum_bool] <;> norm_num
-- E3 hypotheses unsat when α empty:
example (q : Empty → ℝ) : ¬ (∑ a, q a = 1) := by simp
