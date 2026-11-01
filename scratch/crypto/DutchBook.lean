/-
# Dutch books: one coherent agent, and two agents who must share a measure

Outcomes form a finite type Ω. An agent posts a price p ω for a ticket paying 1 if ω happens. Stakes
x ω ∈ ℝ say how many tickets the agent buys (negative: sells). The agent's net payoff in outcome ω is
x ω − ∑ x i · p i. A Dutch book is a choice of stakes with negative payoff in every outcome.

PROVED
1. `no_book_of_prob`: if p is a probability vector (nonnegative, summing to 1), no stakes give a sure
   loss.
2. `book_of_sum_ne_one`, `book_of_neg`: if the prices do not sum to 1, or some price is negative,
   explicit stakes give a sure loss.
3. `coherent_iff`: for a nonempty outcome space, no Dutch book exists exactly when p is a probability
   vector (finite de Finetti).
4. `arbitrage_of_disagree`: if two agents post different prices for some outcome, an outsider who buys
   that ticket from the cheaper one and sells it to the dearer one gains the same positive amount in
   every outcome.
5. `no_arbitrage_of_agree`: if both post the same probability vector, no combination of trades with
   the two of them gives the outsider a sure gain.
6. `joint_coherent_iff`: two agents posting prices pA and pB can be traded against by an outsider with
   no sure gain exactly when pA = pB and that common vector is a probability distribution.

INTERPRETED (not formalized)
- Two agents who cannot be jointly exploited must price by one shared probability measure: agreement
  is forced on the prices they post. They may still disagree about anything they do not post.
-/

import Mathlib

namespace DutchBook

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The agent's net payoff in outcome ω with stakes x at prices p. -/
def payoff (p x : Ω → ℝ) (ω : Ω) : ℝ := x ω - ∑ i, x i * p i

def DutchBook (p : Ω → ℝ) : Prop := ∃ x : Ω → ℝ, ∀ ω, payoff p x ω < 0

def IsProb (p : Ω → ℝ) : Prop := (∀ ω, 0 ≤ p ω) ∧ ∑ ω, p ω = 1

theorem expected_payoff_zero (p x : Ω → ℝ) (hs : ∑ ω, p ω = 1) :
    ∑ ω, p ω * payoff p x ω = 0 := by
  simp only [payoff, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
  rw [sub_eq_zero]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem no_book_of_prob [Nonempty Ω] (p : Ω → ℝ) (hp : IsProb p) : ¬ DutchBook p := by
  rintro ⟨x, hx⟩
  have h0 := expected_payoff_zero p x hp.2
  obtain ⟨ω₀, hω₀⟩ : ∃ ω, 0 < p ω := by
    by_contra h
    push_neg at h
    have : ∑ ω, p ω = 0 := Finset.sum_eq_zero fun ω _ => le_antisymm (h ω) (hp.1 ω)
    rw [hp.2] at this
    exact one_ne_zero this
  have hlt : ∑ ω, p ω * payoff p x ω < 0 := by
    apply Finset.sum_neg'
    · exact fun ω _ => mul_nonpos_of_nonneg_of_nonpos (hp.1 ω) (hx ω).le
    · exact ⟨ω₀, mem_univ _, mul_neg_of_pos_of_neg hω₀ (hx ω₀)⟩
  linarith

theorem book_of_sum_ne_one (p : Ω → ℝ) (hs : ∑ ω, p ω ≠ 1) : DutchBook p := by
  set c : ℝ := if 1 - ∑ ω, p ω < 0 then 1 else -1
  refine ⟨fun _ => c, fun ω => ?_⟩
  have hpay : payoff p (fun _ => c) ω = c * (1 - ∑ i, p i) := by
    simp only [payoff, ← Finset.mul_sum]; ring
  rw [hpay]
  by_cases h : 1 - ∑ ω, p ω < 0
  · simp only [c, if_pos h, one_mul]; exact h
  · have h' : 0 < 1 - ∑ ω, p ω := lt_of_le_of_ne (not_lt.mp h) (fun e => hs (by linarith))
    simp only [c, if_neg h]; linarith

theorem book_of_neg (p : Ω → ℝ) (j : Ω) (hj : p j < 0) : DutchBook p := by
  refine ⟨fun i => if i = j then -1 else 0, fun ω => ?_⟩
  have hsum : ∑ i, (if i = j then (-1 : ℝ) else 0) * p i = -p j := by
    simp [ite_mul]
  simp only [payoff, hsum]
  split_ifs <;> linarith

theorem coherent_iff [Nonempty Ω] (p : Ω → ℝ) : ¬ DutchBook p ↔ IsProb p := by
  constructor
  · intro h
    refine ⟨fun ω => ?_, ?_⟩
    · by_contra hneg
      exact h (book_of_neg p ω (lt_of_not_ge hneg))
    · by_contra hs
      exact h (book_of_sum_ne_one p hs)
  · exact no_book_of_prob p

/-- The outsider's payoff trading stakes xA with agent A (prices pA) and xB with agent B (prices pB). -/
def outsiderGain (pA pB xA xB : Ω → ℝ) (ω : Ω) : ℝ := -(payoff pA xA ω + payoff pB xB ω)

theorem arbitrage_of_disagree (pA pB : Ω → ℝ) (j : Ω) (h : pA j < pB j) :
    ∃ xA xB : Ω → ℝ, ∀ ω, outsiderGain pA pB xA xB ω = pB j - pA j := by
  refine ⟨fun i => if i = j then -1 else 0, fun i => if i = j then 1 else 0, fun ω => ?_⟩
  simp only [outsiderGain, payoff]
  simp only [ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq', mem_univ, if_true]
  split_ifs <;> ring

theorem no_arbitrage_of_agree [Nonempty Ω] (p : Ω → ℝ) (hp : IsProb p) (xA xB : Ω → ℝ) :
    ¬ ∀ ω, 0 < outsiderGain p p xA xB ω := by
  intro hgain
  apply no_book_of_prob p hp
  refine ⟨fun i => xA i + xB i, fun ω => ?_⟩
  have := hgain ω
  have heq : payoff p (fun i => xA i + xB i) ω = payoff p xA ω + payoff p xB ω := by
    simp only [payoff, add_mul, Finset.sum_add_distrib]; ring
  simp only [outsiderGain] at this
  rw [heq]; linarith

/-- No combination of trades with A and B gives the outsider a sure positive gain. -/
def JointlyCoherent (pA pB : Ω → ℝ) : Prop :=
  ∀ xA xB : Ω → ℝ, ¬ ∀ ω, 0 < outsiderGain pA pB xA xB ω

theorem joint_coherent_iff [Nonempty Ω] (pA pB : Ω → ℝ) :
    JointlyCoherent pA pB ↔ pA = pB ∧ IsProb pA := by
  constructor
  · intro h
    have heq : pA = pB := by
      funext j
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · obtain ⟨xA, xB, hx⟩ := arbitrage_of_disagree pA pB j hlt
        exact h xA xB fun ω => by rw [hx ω]; linarith
      · obtain ⟨xB, xA, hx⟩ := arbitrage_of_disagree pB pA j hgt
        refine h xA xB fun ω => ?_
        have := hx ω
        simp only [outsiderGain] at this ⊢
        linarith
    refine ⟨heq, (coherent_iff pA).mp ?_⟩
    rintro ⟨x, hx⟩
    subst heq
    refine h x (fun _ => 0) fun ω => ?_
    have hz : payoff pA (fun _ => 0) ω = 0 := by simp [payoff]
    simp only [outsiderGain, hz, add_zero]
    linarith [hx ω]
  · rintro ⟨rfl, hp⟩ xA xB
    exact no_arbitrage_of_agree pA hp xA xB

end DutchBook

#print axioms DutchBook.no_book_of_prob
#print axioms DutchBook.book_of_sum_ne_one
#print axioms DutchBook.book_of_neg
#print axioms DutchBook.coherent_iff
#print axioms DutchBook.arbitrage_of_disagree
#print axioms DutchBook.no_arbitrage_of_agree
#print axioms DutchBook.joint_coherent_iff
