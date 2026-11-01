import Mathlib

/-!
# ComparativeAdvantageA

Two-agent, two-good Ricardian model with linear production. Agent `i` has one unit of
labour, produces `aᵢ` of good X or `bᵢ` of good Y per unit of labour (all positive), and
spends fraction `sᵢ ∈ [0,1]` of its labour on X. Totals:
`X = s₁ a₁ + s₂ a₂`, `Y = (1 - s₁) b₁ + (1 - s₂) b₂`.

PROVED
* `exists_improvement`: if `a₂ / b₂ < a₁ / b₁` (agent 1 has comparative advantage in X),
  `(s₁, s₂)` is feasible and not (`s₁ = 1` or `s₂ = 0`), then there is a feasible
  `(t₁, t₂)` with `s₁ ≤ t₁`, `t₂ ≤ s₂`, `X' ≥ X`, `Y' ≥ Y`, and `X' > X` or `Y' > Y`.
  The witness keeps `Y` fixed and strictly raises `X`
  (`exists_improvement_strictX`).
* `no_improvement_of_boundary`: the exception is sharp. If `s₁ = 1` or `s₂ = 0`, no
  feasible plan with `s₁ ≤ t₁`, `t₂ ≤ s₂` Pareto-improves on `(s₁, s₂)` (this direction
  uses only positivity, not comparative advantage).
* `improvement_iff`: the two combined into an equivalence.
* `absolute_advantage_not_needed_example`: with `a₁ = 1, b₁ = 1, a₂ = 3, b₂ = 6`
  (so `a₁ < a₂`, `b₁ < b₂`, and `3/6 < 1/1`), the fully specialised plan `(1, 0)`
  produces strictly more of both goods (`X = 1, Y = 6`) than the autarky plan
  `(1/2, 1/10)` (`X = 4/5, Y = 59/10`).
* `absolute_advantage_not_needed`: the existential packaging of that example.

INTERPRETED
* "Another plan producing at least as much of both goods and strictly more of at least
  one" is `ParetoImproves`: weak inequality on both totals and strict on at least one.
* "Unless `s₁ = 1` or `s₂ = 0` already" is taken as the hypothesis `¬ (s₁ = 1 ∨ s₂ = 0)`;
  `no_improvement_of_boundary` shows the exception cannot be removed.
* Plans are feasible when both fractions lie in `[0,1]`; the improved plan is required
  to be feasible too.
-/

namespace ComparativeAdvantageA

/-- Total output of good X. -/
def totX (a₁ a₂ s₁ s₂ : ℝ) : ℝ := s₁ * a₁ + s₂ * a₂

/-- Total output of good Y. -/
def totY (b₁ b₂ s₁ s₂ : ℝ) : ℝ := (1 - s₁) * b₁ + (1 - s₂) * b₂

/-- Both labour fractions lie in `[0,1]`. -/
def Feasible (s₁ s₂ : ℝ) : Prop := s₁ ∈ Set.Icc (0 : ℝ) 1 ∧ s₂ ∈ Set.Icc (0 : ℝ) 1

/-- Plan `(t₁, t₂)` produces at least as much of both goods as `(s₁, s₂)` and strictly
more of at least one. -/
def ParetoImproves (a₁ b₁ a₂ b₂ s₁ s₂ t₁ t₂ : ℝ) : Prop :=
  totX a₁ a₂ s₁ s₂ ≤ totX a₁ a₂ t₁ t₂ ∧ totY b₁ b₂ s₁ s₂ ≤ totY b₁ b₂ t₁ t₂ ∧
    (totX a₁ a₂ s₁ s₂ < totX a₁ a₂ t₁ t₂ ∨ totY b₁ b₂ s₁ s₂ < totY b₁ b₂ t₁ t₂)

/-- Stronger form: the improvement can keep `Y` unchanged and strictly raise `X`. -/
theorem exists_improvement_strictX {a₁ b₁ a₂ b₂ s₁ s₂ : ℝ}
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hca : a₂ / b₂ < a₁ / b₁) (hs : Feasible s₁ s₂) (hne : ¬ (s₁ = 1 ∨ s₂ = 0)) :
    ∃ t₁ t₂ : ℝ, Feasible t₁ t₂ ∧ s₁ ≤ t₁ ∧ t₂ ≤ s₂ ∧
      totX a₁ a₂ s₁ s₂ < totX a₁ a₂ t₁ t₂ ∧ totY b₁ b₂ s₁ s₂ = totY b₁ b₂ t₁ t₂ := by
  obtain ⟨⟨hs₁0, hs₁1⟩, ⟨hs₂0, hs₂1⟩⟩ := hs
  have hs₁ : s₁ < 1 := lt_of_le_of_ne hs₁1 (fun h => hne (Or.inl h))
  have hs₂ : 0 < s₂ := lt_of_le_of_ne hs₂0 (fun h => hne (Or.inr h.symm))
  have hcross : a₂ * b₁ < a₁ * b₂ := by
    rw [div_lt_div_iff₀ hb₂ hb₁] at hca
    exact hca
  set t := min ((1 - s₁) / b₂) (s₂ / b₁) with ht_def
  have ht : 0 < t := lt_min (div_pos (by linarith) hb₂) (div_pos hs₂ hb₁)
  have ht₁ : t * b₂ ≤ 1 - s₁ := (le_div_iff₀ hb₂).mp (min_le_left _ _)
  have ht₂ : t * b₁ ≤ s₂ := (le_div_iff₀ hb₁).mp (min_le_right _ _)
  have htb₁ : 0 < t * b₁ := mul_pos ht hb₁
  have htb₂ : 0 < t * b₂ := mul_pos ht hb₂
  refine ⟨s₁ + t * b₂, s₂ - t * b₁, ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩,
    by linarith, by linarith, ?_, ?_⟩
  · unfold totX
    have : 0 < t * (a₁ * b₂ - a₂ * b₁) := mul_pos ht (sub_pos.mpr hcross)
    nlinarith
  · unfold totY
    ring

/-- Comparative advantage: away from the boundary `s₁ = 1 ∨ s₂ = 0`, moving agent 1 toward
X and agent 2 toward Y yields a Pareto improvement. -/
theorem exists_improvement {a₁ b₁ a₂ b₂ s₁ s₂ : ℝ}
    (_ha₁ : 0 < a₁) (hb₁ : 0 < b₁) (_ha₂ : 0 < a₂) (hb₂ : 0 < b₂)
    (hca : a₂ / b₂ < a₁ / b₁) (hs : Feasible s₁ s₂) (hne : ¬ (s₁ = 1 ∨ s₂ = 0)) :
    ∃ t₁ t₂ : ℝ, Feasible t₁ t₂ ∧ s₁ ≤ t₁ ∧ t₂ ≤ s₂ ∧
      ParetoImproves a₁ b₁ a₂ b₂ s₁ s₂ t₁ t₂ := by
  obtain ⟨t₁, t₂, hf, h1, h2, hX, hY⟩ := exists_improvement_strictX hb₁ hb₂ hca hs hne
  exact ⟨t₁, t₂, hf, h1, h2, hX.le, hY.le, Or.inl hX⟩

/-- The exception is sharp: at `s₁ = 1` or `s₂ = 0`, no feasible plan in the stated
direction is a Pareto improvement. -/
theorem no_improvement_of_boundary {a₁ b₁ a₂ b₂ s₁ s₂ : ℝ}
    (hb₁ : 0 < b₁) (ha₂ : 0 < a₂) (h : s₁ = 1 ∨ s₂ = 0) :
    ¬ ∃ t₁ t₂ : ℝ, Feasible t₁ t₂ ∧ s₁ ≤ t₁ ∧ t₂ ≤ s₂ ∧
      ParetoImproves a₁ b₁ a₂ b₂ s₁ s₂ t₁ t₂ := by
  rintro ⟨t₁, t₂, ⟨⟨ht₁0, ht₁1⟩, ⟨ht₂0, ht₂1⟩⟩, h1, h2, hX, hY, hstrict⟩
  unfold totX at hX hstrict
  unfold totY at hY hstrict
  rcases h with rfl | rfl
  · have e1 : t₁ = 1 := le_antisymm ht₁1 h1
    subst e1
    have : s₂ * a₂ ≤ t₂ * a₂ := by linarith
    have e2 : t₂ = s₂ := le_antisymm h2 (le_of_mul_le_mul_right this ha₂)
    subst e2
    rcases hstrict with hs | hs <;> exact lt_irrefl _ hs
  · have e2 : t₂ = 0 := le_antisymm h2 ht₂0
    subst e2
    have : (1 - s₁) * b₁ ≤ (1 - t₁) * b₁ := by linarith
    have e1 : t₁ = s₁ := le_antisymm (by
      have := le_of_mul_le_mul_right this hb₁
      linarith) h1
    subst e1
    rcases hstrict with hs | hs <;> exact lt_irrefl _ hs

/-- Under comparative advantage, a feasible plan admits a Pareto improvement in the
stated direction iff it is not at the boundary `s₁ = 1 ∨ s₂ = 0`. -/
theorem improvement_iff {a₁ b₁ a₂ b₂ s₁ s₂ : ℝ}
    (ha₁ : 0 < a₁) (hb₁ : 0 < b₁) (ha₂ : 0 < a₂) (hb₂ : 0 < b₂)
    (hca : a₂ / b₂ < a₁ / b₁) (hs : Feasible s₁ s₂) :
    (∃ t₁ t₂ : ℝ, Feasible t₁ t₂ ∧ s₁ ≤ t₁ ∧ t₂ ≤ s₂ ∧
      ParetoImproves a₁ b₁ a₂ b₂ s₁ s₂ t₁ t₂) ↔ ¬ (s₁ = 1 ∨ s₂ = 0) := by
  constructor
  · intro hex hb
    exact no_improvement_of_boundary hb₁ ha₂ hb hex
  · intro hne
    exact exists_improvement ha₁ hb₁ ha₂ hb₂ hca hs hne

/-- Explicit example: agent 1 is worse at both goods (`1 < 3`, `1 < 6`) but has comparative
advantage in X (`3/6 < 1/1`); full specialisation `(1, 0)` beats the autarky plan
`(1/2, 1/10)` strictly in both goods. -/
theorem absolute_advantage_not_needed_example :
    (1 : ℝ) < 3 ∧ (1 : ℝ) < 6 ∧ (3 : ℝ) / 6 < 1 / 1 ∧
      Feasible (1 / 2) (1 / 10) ∧ Feasible 1 0 ∧
      totX 1 3 (1 / 2) (1 / 10) = 4 / 5 ∧ totY 1 6 (1 / 2) (1 / 10) = 59 / 10 ∧
      totX 1 3 1 0 = 1 ∧ totY 1 6 1 0 = 6 ∧
      totX 1 3 (1 / 2) (1 / 10) < totX 1 3 1 0 ∧
      totY 1 6 (1 / 2) (1 / 10) < totY 1 6 1 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [Feasible, totX, totY]

/-- Existential form: there are positive coefficients with `a₁ < a₂`, `b₁ < b₂` and
`a₂ / b₂ < a₁ / b₁`, and a feasible autarky plan strictly dominated in both goods by full
specialisation `(1, 0)`. -/
theorem absolute_advantage_not_needed :
    ∃ a₁ b₁ a₂ b₂ : ℝ, 0 < a₁ ∧ 0 < b₁ ∧ 0 < a₂ ∧ 0 < b₂ ∧
      a₁ < a₂ ∧ b₁ < b₂ ∧ a₂ / b₂ < a₁ / b₁ ∧
      ∃ s₁ s₂ : ℝ, Feasible s₁ s₂ ∧
        totX a₁ a₂ s₁ s₂ < totX a₁ a₂ 1 0 ∧ totY b₁ b₂ s₁ s₂ < totY b₁ b₂ 1 0 := by
  obtain ⟨h1, h2, h3, hf, -, -, -, -, -, hX, hY⟩ := absolute_advantage_not_needed_example
  exact ⟨1, 1, 3, 6, by norm_num, by norm_num, by norm_num, by norm_num, h1, h2, h3,
    1 / 2, 1 / 10, hf, hX, hY⟩

end ComparativeAdvantageA
