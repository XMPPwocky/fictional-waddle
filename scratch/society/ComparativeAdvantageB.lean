import Mathlib

/-!
# Ricardian comparative advantage, two agents, two goods

Agent `i` has one unit of labour and produces `aᵢ` of good X or `bᵢ` of good Y per unit
labour (all positive). A plan is a pair `(s₁, s₂) ∈ [0,1]²` of fractions of labour spent on X.
Totals: `X = s₁ a₁ + s₂ a₂`, `Y = (1 - s₁) b₁ + (1 - s₂) b₂`.
Comparative advantage of agent 1 in X: `a₁ / b₁ > a₂ / b₂`.

PROVED
* `exists_improvement`: under comparative advantage, for any feasible plan with
  `s₁ ≠ 1` and `s₂ ≠ 0` there is a feasible plan `(s₁', s₂')` with `s₁' ≥ s₁`, `s₂' ≤ s₂`,
  `X' ≥ X`, `Y' ≥ Y`, and `X' > X ∨ Y' > Y`. The witness keeps `X` fixed and strictly
  raises `Y`.
* `no_improvement_of_specialised`: the exception is sharp: if `s₁ = 1` or `s₂ = 0`, no plan
  with `s₁' ≥ s₁`, `s₂' ≤ s₂` weakly improves both goods with one strict.
* `exists_improvement_iff`: the two combined.
* `absolute_advantage_not_needed`: with `a = (1, 4)`, `b = (1, 8)` (agent 1 strictly worse at
  both goods, yet `1/1 > 4/8`), the autarky plan `(1/2, 1/2)` gives `(X, Y) = (5/2, 9/2)`,
  and the plan `(1, 2/5)`, in which agent 1 is fully specialised in X, gives `(13/5, 24/5)`,
  strictly more of both.

INTERPRETED
* "Another plan ... with `s₁' ≥ s₁` and `s₂' ≤ s₂`" is read as a feasible plan
  (`s₁', s₂' ∈ [0,1]`) moving each agent weakly toward its comparative-advantage good.
* "Unless `s₁ = 1` or `s₂ = 0`" is read as the hypothesis `s₁ ≠ 1 ∧ s₂ ≠ 0`; the converse
  is proved separately.
* "The specialised plan" in the example is the plan where agent 1 is fully specialised
  (`s₁' = 1`) and agent 2 shifts toward Y relative to autarky (`s₂' = 2/5 < 1/2`). Full
  specialisation of both agents, `(1, 0)`, gives `(1, 8)` there and does not dominate.
-/

namespace ComparativeAdvantageB

/-- Total output of good X under plan `(s₁, s₂)`. -/
def totX (a₁ a₂ s₁ s₂ : ℝ) : ℝ := s₁ * a₁ + s₂ * a₂

/-- Total output of good Y under plan `(s₁, s₂)`. -/
def totY (b₁ b₂ s₁ s₂ : ℝ) : ℝ := (1 - s₁) * b₁ + (1 - s₂) * b₂

/-- Feasibility of a plan. -/
def Feasible (s₁ s₂ : ℝ) : Prop := s₁ ∈ Set.Icc (0 : ℝ) 1 ∧ s₂ ∈ Set.Icc (0 : ℝ) 1

/-- `(s₁', s₂')` is a feasible, specialising, Pareto improvement on `(s₁, s₂)`. -/
def Improves (a₁ a₂ b₁ b₂ s₁ s₂ s₁' s₂' : ℝ) : Prop :=
  Feasible s₁' s₂' ∧ s₁ ≤ s₁' ∧ s₂' ≤ s₂ ∧
    totX a₁ a₂ s₁ s₂ ≤ totX a₁ a₂ s₁' s₂' ∧ totY b₁ b₂ s₁ s₂ ≤ totY b₁ b₂ s₁' s₂' ∧
    (totX a₁ a₂ s₁ s₂ < totX a₁ a₂ s₁' s₂' ∨ totY b₁ b₂ s₁ s₂ < totY b₁ b₂ s₁' s₂')

theorem exists_improvement {a₁ a₂ b₁ b₂ s₁ s₂ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hca : a₂ / b₂ < a₁ / b₁) (hs : Feasible s₁ s₂) (h₁ : s₁ ≠ 1) (h₂ : s₂ ≠ 0) :
    ∃ s₁' s₂', Improves a₁ a₂ b₁ b₂ s₁ s₂ s₁' s₂' := by
  obtain ⟨⟨hs₁0, hs₁1⟩, ⟨hs₂0, hs₂1⟩⟩ := hs
  have hs₁ : s₁ < 1 := lt_of_le_of_ne hs₁1 h₁
  have hs₂ : 0 < s₂ := lt_of_le_of_ne hs₂0 (Ne.symm h₂)
  have hcross : a₂ * b₁ < a₁ * b₂ := by
    rw [div_lt_div_iff₀ hb₂ hb₁] at hca; linarith
  set c : ℝ := a₁ + a₂ with hc
  have hcpos : 0 < c := by positivity
  set t : ℝ := s₂ * (1 - s₁) / c with ht
  have htpos : 0 < t := by
    have : 0 < 1 - s₁ := by linarith
    positivity
  have hta₁ : t * a₁ ≤ s₂ := by
    rw [ht, div_mul_eq_mul_div, div_le_iff₀ hcpos]
    nlinarith [mul_nonneg hs₂0 hs₁0, mul_nonneg hs₂0 ha₂.le, mul_nonneg (mul_nonneg hs₂0 hs₁0) ha₁.le]
  have hta₂ : t * a₂ ≤ 1 - s₁ := by
    rw [ht, div_mul_eq_mul_div, div_le_iff₀ hcpos]
    have h1 : 0 ≤ 1 - s₁ := by linarith
    have h2 : 0 ≤ 1 - s₂ := by linarith
    nlinarith [mul_nonneg h1 ha₁.le, mul_nonneg (mul_nonneg h1 h2) ha₂.le]
  refine ⟨s₁ + t * a₂, s₂ - t * a₁, ?_⟩
  have hX : totX a₁ a₂ (s₁ + t * a₂) (s₂ - t * a₁) = totX a₁ a₂ s₁ s₂ := by
    unfold totX; ring
  have hY : totY b₁ b₂ (s₁ + t * a₂) (s₂ - t * a₁)
      = totY b₁ b₂ s₁ s₂ + t * (a₁ * b₂ - a₂ * b₁) := by
    unfold totY; ring
  have hgain : 0 < t * (a₁ * b₂ - a₂ * b₁) := mul_pos htpos (by linarith)
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_, ?_, hX.ge, ?_, Or.inr ?_⟩
  · nlinarith [mul_pos htpos ha₂]
  · linarith
  · linarith
  · nlinarith [mul_pos htpos ha₁]
  · nlinarith [mul_pos htpos ha₂]
  · nlinarith [mul_pos htpos ha₁]
  · rw [hY]; linarith
  · rw [hY]; linarith

theorem no_improvement_of_specialised {a₁ a₂ b₁ b₂ s₁ s₂ : ℝ}
    (_ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (_hb₂ : 0 < b₂)
    (hs : Feasible s₁ s₂) (h : s₁ = 1 ∨ s₂ = 0) :
    ¬ ∃ s₁' s₂', Improves a₁ a₂ b₁ b₂ s₁ s₂ s₁' s₂' := by
  rintro ⟨s₁', s₂', ⟨⟨_, hs₁'1⟩, ⟨hs₂'0, _⟩⟩, hle₁, hle₂, hX, hY, hstrict⟩
  obtain ⟨⟨_, hs₁1⟩, ⟨hs₂0, _⟩⟩ := hs
  unfold totX at hX hstrict
  unfold totY at hY hstrict
  rcases h with h | h
  · subst h
    have e₁ : s₁' = 1 := le_antisymm hs₁'1 hle₁
    subst e₁
    have : s₂ ≤ s₂' := by nlinarith
    have e₂ : s₂' = s₂ := le_antisymm hle₂ this
    subst e₂
    rcases hstrict with h' | h' <;> linarith
  · subst h
    have e₂ : s₂' = 0 := le_antisymm hle₂ hs₂'0
    subst e₂
    have : s₁' ≤ s₁ := by nlinarith
    have e₁ : s₁' = s₁ := le_antisymm this hle₁
    subst e₁
    rcases hstrict with h' | h' <;> linarith

theorem exists_improvement_iff {a₁ a₂ b₁ b₂ s₁ s₂ : ℝ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hca : a₂ / b₂ < a₁ / b₁) (hs : Feasible s₁ s₂) :
    (∃ s₁' s₂', Improves a₁ a₂ b₁ b₂ s₁ s₂ s₁' s₂') ↔ (s₁ ≠ 1 ∧ s₂ ≠ 0) := by
  constructor
  · intro hex
    by_contra hn
    rw [not_and_or, not_ne_iff, not_ne_iff] at hn
    exact no_improvement_of_specialised ha₁ ha₂ hb₁ hb₂ hs hn hex
  · rintro ⟨h₁, h₂⟩
    exact exists_improvement ha₁ ha₂ hb₁ hb₂ hca hs h₁ h₂

theorem absolute_advantage_not_needed :
    let a₁ : ℝ := 1; let a₂ : ℝ := 4; let b₁ : ℝ := 1; let b₂ : ℝ := 8
    (0 < a₁ ∧ 0 < a₂ ∧ 0 < b₁ ∧ 0 < b₂) ∧
    a₁ < a₂ ∧ b₁ < b₂ ∧ a₂ / b₂ < a₁ / b₁ ∧
    Feasible (1/2) (1/2) ∧ Feasible 1 (2/5) ∧
    totX a₁ a₂ (1/2) (1/2) = 5/2 ∧ totY b₁ b₂ (1/2) (1/2) = 9/2 ∧
    totX a₁ a₂ 1 (2/5) = 13/5 ∧ totY b₁ b₂ 1 (2/5) = 24/5 ∧
    totX a₁ a₂ (1/2) (1/2) < totX a₁ a₂ 1 (2/5) ∧
    totY b₁ b₂ (1/2) (1/2) < totY b₁ b₂ 1 (2/5) := by
  intro a₁ a₂ b₁ b₂
  simp only [a₁, a₂, b₁, b₂, totX, totY, Feasible, Set.mem_Icc]
  norm_num

end ComparativeAdvantageB
