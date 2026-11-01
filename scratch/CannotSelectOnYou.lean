import Mathlib

/-!
# What doesn't model you cannot select on you

Your payoff as a function of your policy parameter `θ` is `U θ = A θ + B (r θ)`. Here `A` is the part you cause
directly, and `B ∘ r` is the part that runs through a counterpart's response `r θ`.

* J1 `blind_counterpart_adds_no_selection`: if the counterpart's response is invariant to your policy at `θ`
  (`r' θ = 0`: it does not model you), your selection gradient is exactly the frozen-world gradient `A' θ`. It is part
  of the scenery, not a selector.
* J2 `modelling_counterpart_reshapes_selection`: if it does respond (`r' θ ≠ 0`) and its response matters to you
  (`B' (r θ) ≠ 0`), your gradient differs from the frozen-world one. Only counterparts that model you can select on
  you.
* J3 `simulation_invariant_policy_is_flat_for_them`: the dual. Against the graduated refusal (accept with probability
  `c/s`), the counterpart's payoff `s · (c/s)` has derivative `0` in its own demand `s` for every `s > 0`. A policy
  that is invariant to being simulated gives a simulator no gradient to climb, so it cannot select against you.
-/

namespace CannotSelectOnYou

/-- **J1.** -/
theorem blind_counterpart_adds_no_selection (A B r : ℝ → ℝ) (θ a b : ℝ) (hA : HasDerivAt A a θ)
    (hB : HasDerivAt B b (r θ)) (hr : HasDerivAt r 0 θ) : HasDerivAt (fun x => A x + B (r x)) a θ := by
  have h := hA.add (hB.comp θ hr)
  rw [mul_zero, add_zero] at h
  exact h

/-- **J2.** -/
theorem modelling_counterpart_reshapes_selection (A B r : ℝ → ℝ) (θ a b ρ : ℝ) (hA : HasDerivAt A a θ)
    (hB : HasDerivAt B b (r θ)) (hr : HasDerivAt r ρ θ) (hb : b ≠ 0) (hρ : ρ ≠ 0) :
    HasDerivAt (fun x => A x + B (r x)) (a + b * ρ) θ ∧ a + b * ρ ≠ a := by
  have h := hA.add (hB.comp θ hr)
  refine ⟨h, ?_⟩
  intro e; exact mul_ne_zero hb hρ (by linarith)

/-- **J3.** -/
theorem simulation_invariant_policy_is_flat_for_them (c s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun x => x * (c / x)) 0 s := by
  have hev : (fun x => x * (c / x)) =ᶠ[nhds s] (fun _ => c) := by
    filter_upwards [Ioi_mem_nhds hs] with x hx using by field_simp [(Set.mem_Ioi.mp hx).ne']
  exact (hasDerivAt_const s c).congr_of_eventuallyEq hev

end CannotSelectOnYou
