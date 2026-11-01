import Mathlib
/-! Vacuity sweep test 3: several small checks.
(a) LandauerCounting L3: the ∀ s is inert (tautology); `simp` reduces it to `(∀ s : S, r₁ = s₀) ↔ r₁ = s₀`,
    which needs the inhabitant `s₀`, so the proof is a term.
(b) GrabbyPrograms G2' is a logical tautology (constant-on-a-set iff all values equal); `simp`/`constructor` suffice.
(c) WhoseCollapse W1's name says "converges": check |q| < 1 under its hypotheses (the file never states it).
(d) NoFurther N1: the fair demand s = 1/2 yields the SAME 1/2 − ε, so the proposer is indifferent, not pushed to fair
    (closed by `ring`; `norm_num` alone does not close it).
(e) DiscretizePump Q2b relies on Mathlib's round-half-up: round (1/2) = 1. -/
namespace ReviewVacuity3

theorem a_swap_tautology {S R : Type*} (s₀ r₁ : S) (r : R) :
    (∀ s : S, ((fun p : S × (S × R) => (p.2.1, (p.1, p.2.2))) (s, (r₁, r))).1 = s₀) ↔ r₁ = s₀ :=
  ⟨fun h => h s₀, fun h _ => h⟩

theorem b_neutral_tautology (g : ℝ → ℝ) :
    (∀ r₁ r₂ : ℝ, 0 < r₁ → 0 < r₂ → g r₁ = g r₂) ↔ ∃ c, ∀ r : ℝ, 0 < r → g r = c :=
  ⟨fun h => ⟨g 1, fun r hr => h r 1 hr one_pos⟩, fun ⟨c, hc⟩ r₁ r₂ h1 h2 => by rw [hc r₁ h1, hc r₂ h2]⟩

theorem c_gap_contracts (l c : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    |(1 - l) * (1 - 2 * c)| < 1 := by
  rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - l)]
  have h : |1 - 2 * c| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  nlinarith [abs_nonneg (1 - 2 * c)]

theorem d_fair_demand_same_payoff (ε : ℝ) : (1 / 2 : ℝ) * ((1 / 2 - ε) / (1 / 2)) = 1 / 2 - ε := by
  ring

theorem e_round_half : round (1 / 2 : ℝ) = 1 := by
  rw [round_eq]; norm_num

end ReviewVacuity3
