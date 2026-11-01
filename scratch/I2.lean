import Mathlib

/-!
I2 as written in AgentIdentityStatements.lean uses `ContDiff ℝ ⊤`, and in this Mathlib `⊤ : WithTop ℕ∞` is ω,
i.e. ANALYTIC. That version is false (it contradicts I1's identity theorem), proved below. The intended
statement, "a C^∞ (smooth, not analytic) mimic exists", is proved under a new name with `(⊤ : ℕ∞)`.
Nothing in AgentIdentityStatements.lean is changed.
-/

namespace AgentIdentity

/-- I2 as literally written is false: an analytic policy that is zero on [-1,1] is zero everywhere. -/
theorem smooth_mimic_exists_as_written_is_false :
    ¬ ∃ f : ℝ → ℝ, ContDiff ℝ ⊤ f ∧ (∀ x ∈ Set.Icc (-1 : ℝ) 1, f x = 0) ∧ f 2 ≠ 0 := by
  rintro ⟨f, hf, hzero, h2⟩
  have hA : AnalyticOnNhd ℝ f Set.univ := hf.analyticOnNhd
  have hev : f =ᶠ[nhds (0 : ℝ)] 0 := by
    filter_upwards [Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with x hx
    simpa using hzero x hx
  have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) hev
  exact h2 (this (Set.mem_univ 2))

/-- **I2 (corrected): smooth agents can be mimics.** A C^∞ policy matches the zero policy on the whole
observed region [-1, 1] and still differs off-path. -/
theorem smooth_mimic_exists_infty :
    ∃ f : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ (∀ x ∈ Set.Icc (-1 : ℝ) 1, f x = 0) ∧ f 2 ≠ 0 := by
  refine ⟨fun x => expNegInvGlue (x - 1), ?_, ?_, ?_⟩
  · exact expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)
  · intro x hx
    exact expNegInvGlue.zero_of_nonpos (by linarith [hx.2])
  · norm_num

end AgentIdentity

#print axioms AgentIdentity.smooth_mimic_exists_as_written_is_false
#print axioms AgentIdentity.smooth_mimic_exists_infty
