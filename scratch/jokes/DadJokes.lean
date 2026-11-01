/-
# Too similar to be funny

Funniness here is excess surprise: the teller draws punchlines from q, the listener predicts with p,
and the joke is worth ∑ q log(q/p) to the listener (the KL divergence).

PROVED
1. `same_mind_zero`: if the listener predicts exactly like the teller (p = q), the excess is 0.
2. `too_similar_to_be_funny`: if the listener's prediction gives every punchline at least (1 − ε)
   times the teller's probability, the excess is at most −log(1 − ε).
3. `small_eps_bound`: for ε ≤ 1/2 that is at most 2ε. Near-identical minds get near-zero laughs.
4. `easy_punchline`: a single punchline the listener gave probability at least 1 − ε surprises them
   by at most −log(1 − ε).

INTERPRETED (not formalized)
- Reading KL divergence as "how funny" is the model. A dad joke is a punchline the listener already
  predicted with high probability.
- Whether two particular minds are "the same" is an empirical claim, not proved here; one joke that
  lands refutes it.
-/

import Mathlib

namespace DadJokes

open Finset

noncomputable def excessSurprise {ι : Type*} [Fintype ι] (q p : ι → ℝ) : ℝ :=
  ∑ i, q i * Real.log (q i / p i)

theorem same_mind_zero {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ i, 0 < q i) :
    excessSurprise q q = 0 := by
  unfold excessSurprise
  apply Finset.sum_eq_zero
  intro i _
  rw [div_self (hq i).ne', Real.log_one, mul_zero]

theorem too_similar_to_be_funny {ι : Type*} [Fintype ι] (q p : ι → ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hq : ∀ i, 0 < q i) (hsq : ∑ i, q i = 1)
    (hclose : ∀ i, (1 - ε) * q i ≤ p i) :
    excessSurprise q p ≤ -Real.log (1 - ε) := by
  have h1e : 0 < 1 - ε := by linarith
  have key : ∀ i, q i * Real.log (q i / p i) ≤ q i * (-Real.log (1 - ε)) := by
    intro i
    have hp : 0 < p i := lt_of_lt_of_le (mul_pos h1e (hq i)) (hclose i)
    have hratio : q i / p i ≤ 1 / (1 - ε) := by
      rw [div_le_div_iff₀ hp h1e]
      linarith [hclose i]
    have hlog : Real.log (q i / p i) ≤ Real.log (1 / (1 - ε)) :=
      Real.log_le_log (div_pos (hq i) hp) hratio
    rw [one_div, Real.log_inv] at hlog
    exact mul_le_mul_of_nonneg_left hlog (hq i).le
  unfold excessSurprise
  calc ∑ i, q i * Real.log (q i / p i) ≤ ∑ i, q i * (-Real.log (1 - ε)) :=
        Finset.sum_le_sum fun i _ => key i
    _ = (∑ i, q i) * (-Real.log (1 - ε)) := by rw [Finset.sum_mul]
    _ = -Real.log (1 - ε) := by rw [hsq, one_mul]

theorem small_eps_bound (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    -Real.log (1 - ε) ≤ 2 * ε := by
  have h1e : 0 < 1 - ε := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h1e)
  rw [Real.log_inv] at h
  have h2 : (1 - ε)⁻¹ - 1 = ε / (1 - ε) := by field_simp; ring
  have h3 : ε / (1 - ε) ≤ 2 * ε := by
    rw [div_le_iff₀ h1e]
    nlinarith
  linarith

theorem easy_punchline (p ε : ℝ) (hε1 : ε < 1) (hp : 1 - ε ≤ p) :
    -Real.log p ≤ -Real.log (1 - ε) := by
  have h1e : 0 < 1 - ε := by linarith
  have := Real.log_le_log h1e hp
  linarith

end DadJokes

#print axioms DadJokes.same_mind_zero
#print axioms DadJokes.too_similar_to_be_funny
#print axioms DadJokes.small_eps_bound
#print axioms DadJokes.easy_punchline
