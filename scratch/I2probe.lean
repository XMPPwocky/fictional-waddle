import Mathlib
example : ((⊤ : WithTop ℕ∞)) = (⊤ : WithTop ℕ∞) := rfl
#check @ContDiff
set_option pp.all false in
#check (fun f : ℝ → ℝ => ContDiff ℝ ⊤ f)
example (f : ℝ → ℝ) (h : ContDiff ℝ ⊤ f) : AnalyticOnNhd ℝ f Set.univ := h.analyticOnNhd
