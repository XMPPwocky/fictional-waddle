import Mathlib

/-!
# Hindsight cannot test a forecast; a sealed record can

A trial is a finite probability space `Ω` with weights `μ`. It has an outcome `o : Ω → α` (the idea that arrived) and a
record `r : Ω → α` (the lead the forecaster says they had). A hit is `r = o`.

PROVED:
* `hindsight_blind`: if the record is reconstructed from the outcome (`r = f ∘ o`), every statistic of
  (record, outcome) has an expectation fixed by the outcome's law alone. Two worlds with the same outcome law, one with
  real steering and one without, are indistinguishable by any test of a reconstructed record.
* `hindsight_perfect`: reconstruction can always report a perfect hit rate.
* `null_hit_eq`, `null_hit_le`: a record sealed independently of the outcome hits with probability `Σ p q`, at most the
  largest outcome probability.
* `steering_law_eq`, `steering_hit_eq`, `seal_separates`: a world where the lead determines the idea has the same
  outcome law as the null world but hits with probability 1, so a sealed record separates the two worlds that
  `hindsight_blind` cannot.
* `binding_bound`: if the record can be altered after sealing with probability at most `ε` (a hash collision, a
  rewritten log), the reported hit rate exceeds the sealed one by at most `ε`.
* `shuffle_identity`: the shuffled baseline over `n` leads and `m` ideas, the count of all (lead, idea) pairs that match,
  equals `Σ_x (#leads = x)(#ideas = x)`, the null hit count for the empirical marginals.
-/

namespace SealedEnvelope
open Finset

variable {α Ω : Type*} [Fintype α] [DecidableEq α] [Fintype Ω]

def hitProb (μ : Ω → ℝ) (r o : Ω → α) : ℝ := ∑ ω, if r ω = o ω then μ ω else 0

def law (μ : Ω → ℝ) (o : Ω → α) (a : α) : ℝ := ∑ ω ∈ univ.filter (fun ω => o ω = a), μ ω

lemma sum_by_outcome (μ : Ω → ℝ) (o : Ω → α) (g : α → ℝ) :
    ∑ ω, μ ω * g (o ω) = ∑ a, law μ o a * g a := by
  rw [← Finset.sum_fiberwise univ o (fun ω => μ ω * g (o ω))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  unfold law
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun ω hω => by rw [(Finset.mem_filter.mp hω).2])

theorem hindsight_blind (μ ν : Ω → ℝ) (o : Ω → α) (hlaw : ∀ a, law μ o a = law ν o a)
    (f : α → α) (T : α → α → ℝ) :
    ∑ ω, μ ω * T (f (o ω)) (o ω) = ∑ ω, ν ω * T (f (o ω)) (o ω) := by
  rw [sum_by_outcome μ o (fun a => T (f a) a), sum_by_outcome ν o (fun a => T (f a) a)]
  simp only [hlaw]

theorem hindsight_perfect (μ : Ω → ℝ) (hμ : ∑ ω, μ ω = 1) (o : Ω → α) : hitProb μ o o = 1 := by
  simp [hitProb, hμ]

theorem null_hit_eq (p q : α → ℝ) :
    hitProb (fun z : α × α => p z.1 * q z.2) Prod.fst Prod.snd = ∑ x, p x * q x := by
  simp [hitProb, Fintype.sum_prod_type]

theorem null_hit_le (p q : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (M : ℝ) (hM : ∀ x, q x ≤ M) :
    ∑ x, p x * q x ≤ M :=
  calc ∑ x, p x * q x ≤ ∑ x, p x * M :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hM x) (hp x))
    _ = M := by rw [← Finset.sum_mul, hp1, one_mul]

theorem null_law_eq (p q : α → ℝ) (hp1 : ∑ x, p x = 1) (a : α) :
    law (fun z : α × α => p z.1 * q z.2) Prod.snd a = q a := by
  simp [law, Finset.sum_filter, Fintype.sum_prod_type, ← Finset.sum_mul, hp1]

theorem steering_law_eq (q : α → ℝ) (a : α) :
    law (fun z : α × α => if z.1 = z.2 then q z.2 else 0) Prod.snd a = q a := by
  simp [law, Finset.sum_filter, Fintype.sum_prod_type]

theorem steering_hit_eq (q : α → ℝ) (hq1 : ∑ x, q x = 1) :
    hitProb (fun z : α × α => if z.1 = z.2 then q z.2 else 0) Prod.fst Prod.snd = 1 := by
  simp [hitProb, Fintype.sum_prod_type, hq1]

theorem seal_separates (p q : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1)
    (M : ℝ) (hM : ∀ x, q x ≤ M) (hM1 : M < 1) :
    (∀ a, law (fun z : α × α => p z.1 * q z.2) Prod.snd a =
          law (fun z : α × α => if z.1 = z.2 then q z.2 else 0) Prod.snd a) ∧
    hitProb (fun z : α × α => p z.1 * q z.2) Prod.fst Prod.snd <
      hitProb (fun z : α × α => if z.1 = z.2 then q z.2 else 0) Prod.fst Prod.snd := by
  refine ⟨fun a => by rw [null_law_eq p q hp1, steering_law_eq], ?_⟩
  rw [null_hit_eq, steering_hit_eq q hq1]
  exact (null_hit_le p q hp hp1 M hM).trans_lt hM1

theorem binding_bound (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (ℓ r o : Ω → α) (ε : ℝ)
    (hε : ∑ ω, (if r ω = ℓ ω then 0 else μ ω) ≤ ε) : hitProb μ r o ≤ hitProb μ ℓ o + ε := by
  have h : ∀ ω, (if r ω = o ω then μ ω else 0) ≤
      (if ℓ ω = o ω then μ ω else 0) + (if r ω = ℓ ω then 0 else μ ω) := by
    intro ω
    have := hμ ω
    split_ifs with h1 h2 h3 h3 <;> first | linarith | exact absurd (h3.symm.trans h1) h2
  calc hitProb μ r o ≤ ∑ ω, ((if ℓ ω = o ω then μ ω else 0) + (if r ω = ℓ ω then 0 else μ ω)) :=
        Finset.sum_le_sum (fun ω _ => h ω)
    _ ≤ hitProb μ ℓ o + ε := by rw [Finset.sum_add_distrib]; unfold hitProb; linarith

theorem shuffle_identity {ι κ : Type*} [Fintype ι] [Fintype κ] (l : ι → α) (o : κ → α) :
    (∑ i, ∑ j, if l i = o j then (1 : ℝ) else 0) =
      ∑ x, ((univ.filter (fun i => l i = x)).card : ℝ) * (univ.filter (fun j => o j = x)).card := by
  have hx : ∀ i j, (∑ x, (if l i = x then (1 : ℝ) else 0) * (if o j = x then 1 else 0)) =
      if l i = o j then 1 else 0 := by
    intro i j
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    by_cases h : l i = o j <;> simp [h, eq_comm]
  simp only [Finset.card_filter]
  push_cast
  symm
  calc ∑ x, (∑ i, if l i = x then (1 : ℝ) else 0) * (∑ j, if o j = x then (1 : ℝ) else 0)
      = ∑ x, ∑ i, ∑ j, (if l i = x then (1 : ℝ) else 0) * (if o j = x then 1 else 0) := by
        simp only [Finset.sum_mul_sum]
    _ = ∑ i, ∑ j, ∑ x, (if l i = x then (1 : ℝ) else 0) * (if o j = x then 1 else 0) := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ i, ∑ j, if l i = o j then (1 : ℝ) else 0 :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hx i j))

end SealedEnvelope
