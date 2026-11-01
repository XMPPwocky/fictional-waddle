import Mathlib
/-! Vacuity sweep test 2: LedgerColour L1 has five linear hypotheses; are they jointly satisfiable?
(a) at the Standard-Model point N = 3, yH = 1/2; (b) for every N ≠ 0 and every yH, by the forced values. -/
namespace ReviewVacuity2

theorem sm_point :
    let N : ℝ := 3
    let yH : ℝ := 1 / 2
    let yQ : ℝ := 1 / 6
    let yu : ℝ := -2 / 3
    let yd : ℝ := 1 / 3
    let yL : ℝ := -1 / 2
    let ye : ℝ := 1
    (yQ + yH + yu = 0) ∧ (yQ - yH + yd = 0) ∧ (yL - yH + ye = 0) ∧ (N * yQ + yL = 0) ∧
      (2 * N * yQ + N * yu + N * yd + 2 * yL + ye = 0) := by
  intros; norm_num

theorem all_N (N yH : ℝ) (hN : N ≠ 0) :
    (yH / N + yH + (-yH * (N + 1) / N) = 0) ∧
    (yH / N - yH + yH * (N - 1) / N = 0) ∧
    (-yH - yH + 2 * yH = 0) ∧
    (N * (yH / N) + -yH = 0) ∧
    (2 * N * (yH / N) + N * (-yH * (N + 1) / N) + N * (yH * (N - 1) / N) + 2 * (-yH) + 2 * yH = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

end ReviewVacuity2
