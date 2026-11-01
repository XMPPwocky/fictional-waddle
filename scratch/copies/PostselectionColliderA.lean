import Mathlib

/-!
# Postselection on a collider creates correlation without causal influence

Finite model: a seed `S` and an answer `A`, independent and uniform on `Fin k` (`k ≥ 2`).
The sample space is `Fin k × Fin k` with the uniform measure, so an event `E` has
probability `P E = #{ω | E ω} / k²`. Success is the event `S = A`. Conditioning on an
event `C` of positive probability is `Pc C E = P (E ∧ C) / P C`.

PROVED
* `prob_seed` : `P(S = s) = 1/k`.
* `prob_answer` : `P(A = a) = 1/k`.
* `prob_joint` : `P(S = s ∧ A = a) = 1/k²`.
* `indep_unconditional` : `P(S = s ∧ A = a) = P(S = s) * P(A = a)` for all `s, a`.
* `answer_ignores_seed` : `P(A = a | S = s) = P(A = a)` for all `s, a`
  (the answer's distribution does not depend on the seed value: no causal influence).
* `prob_success` : `P(S = A) = 1/k`.
* `cond_success_match` : `P(S = A | success) = 1`.
* `cond_seed` : `P(S = s | success) = 1/k`.
* `cond_answer` : `P(A = a | success) = 1/k`.
* `cond_joint` : `P(S = s ∧ A = a | success) = if s = a then 1/k else 0`.
* `cond_joint_zero_one` : `P(S = 0 ∧ A = 1 | success) = 0`.
* `cond_marginals_zero_one` : `P(S = 0 | success) * P(A = 1 | success) = 1/k²`.
* `not_indep_conditional` : conditioned on success, `S` and `A` are not independent:
  there exist `s, a` with `P(S = s ∧ A = a | success) ≠ P(S = s | success) * P(A = a | success)`.
* `cond_answer_determined` : `P(A = s | S = s ∧ success) = 1` (given success, knowing the
  seed determines the answer).
* `postselection_collider` : the conjunction of unconditional independence, perfect
  matching under success, and conditional dependence.
-/

namespace PostselectionColliderA

open Finset

variable {k : ℕ}

/-- Probability of an event under the uniform measure on `Fin k × Fin k`. -/
noncomputable def P (k : ℕ) (E : Fin k × Fin k → Prop) [DecidablePred E] : ℝ :=
  ((univ.filter E).card : ℝ) / (k : ℝ) ^ 2

/-- Conditional probability `P(E | C) = P(E ∧ C) / P(C)`. -/
noncomputable def Pc (k : ℕ) (C E : Fin k × Fin k → Prop) [DecidablePred C]
    [DecidablePred E] : ℝ :=
  P k (fun ω => E ω ∧ C ω) / P k C

/-- The success event `S = A`. -/
def success (ω : Fin k × Fin k) : Prop := ω.1 = ω.2

instance : DecidablePred (success (k := k)) := fun ω => by
  unfold success; infer_instance

lemma card_seed (s : Fin k) : (univ.filter fun ω : Fin k × Fin k => ω.1 = s).card = k := by
  have : (univ.filter fun ω : Fin k × Fin k => ω.1 = s) = ({s} : Finset (Fin k)) ×ˢ univ := by
    ext ⟨x, y⟩; simp [eq_comm]
  rw [this, card_product]; simp

lemma card_answer (a : Fin k) : (univ.filter fun ω : Fin k × Fin k => ω.2 = a).card = k := by
  have : (univ.filter fun ω : Fin k × Fin k => ω.2 = a) = (univ : Finset (Fin k)) ×ˢ {a} := by
    ext ⟨x, y⟩; simp [eq_comm]
  rw [this, card_product]; simp

lemma card_joint (s a : Fin k) :
    (univ.filter fun ω : Fin k × Fin k => ω.1 = s ∧ ω.2 = a).card = 1 := by
  have : (univ.filter fun ω : Fin k × Fin k => ω.1 = s ∧ ω.2 = a) = {(s, a)} := by
    ext ω; simp [Prod.ext_iff]
  rw [this]; simp

lemma card_success : (univ.filter (success (k := k))).card = k := by
  have : (univ.filter (success (k := k))) = (univ : Finset (Fin k)).diag := by
    ext ω; simp [success, Finset.mem_diag]
  rw [this, Finset.diag_card]; simp

lemma card_joint_success (s a : Fin k) :
    (univ.filter fun ω : Fin k × Fin k => (ω.1 = s ∧ ω.2 = a) ∧ success ω).card
      = if s = a then 1 else 0 := by
  split_ifs with h
  · subst h
    have : (univ.filter fun ω : Fin k × Fin k => (ω.1 = s ∧ ω.2 = s) ∧ success ω)
        = {(s, s)} := by
      ext ⟨x, y⟩; simp only [mem_filter, mem_univ, true_and, mem_singleton,
        Prod.mk.injEq]; simp only [success]
      constructor
      · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, h1.trans h2.symm⟩
    rw [this]; simp
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro ω - ⟨⟨h1, h2⟩, h3⟩
    exact h (h1.symm.trans (h3.trans h2))

lemma card_seed_success (s : Fin k) :
    (univ.filter fun ω : Fin k × Fin k => ω.1 = s ∧ success ω).card = 1 := by
  have : (univ.filter fun ω : Fin k × Fin k => ω.1 = s ∧ success ω) = {(s, s)} := by
    ext ⟨x, y⟩; simp only [mem_filter, mem_univ, true_and, mem_singleton,
      Prod.mk.injEq]; simp only [success]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm.trans h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h1.trans h2.symm⟩
  rw [this]; simp

lemma card_answer_success (a : Fin k) :
    (univ.filter fun ω : Fin k × Fin k => ω.2 = a ∧ success ω).card = 1 := by
  have : (univ.filter fun ω : Fin k × Fin k => ω.2 = a ∧ success ω) = {(a, a)} := by
    ext ⟨x, y⟩; simp only [mem_filter, mem_univ, true_and, mem_singleton,
      Prod.mk.injEq]; simp only [success]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2.trans h1, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1.trans h2.symm⟩
  rw [this]; simp

lemma card_success_success :
    (univ.filter fun ω : Fin k × Fin k => success ω ∧ success ω).card = k := by
  simp only [and_self]; exact card_success

section

variable (hk : 2 ≤ k)
include hk

lemma k_ne_zero : (k : ℝ) ≠ 0 := by
  have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  exact this.ne'

theorem prob_seed (s : Fin k) : P k (fun ω => ω.1 = s) = 1 / k := by
  have := k_ne_zero hk
  unfold P; rw [card_seed]; field_simp

theorem prob_answer (a : Fin k) : P k (fun ω => ω.2 = a) = 1 / k := by
  have := k_ne_zero hk
  unfold P; rw [card_answer]; field_simp

omit hk in
theorem prob_joint (s a : Fin k) : P k (fun ω => ω.1 = s ∧ ω.2 = a) = 1 / (k : ℝ) ^ 2 := by
  unfold P; rw [card_joint]; simp

theorem indep_unconditional (s a : Fin k) :
    P k (fun ω => ω.1 = s ∧ ω.2 = a) = P k (fun ω => ω.1 = s) * P k (fun ω => ω.2 = a) := by
  rw [prob_joint, prob_seed hk, prob_answer hk]; ring

theorem answer_ignores_seed (s a : Fin k) :
    Pc k (fun ω => ω.1 = s) (fun ω => ω.2 = a) = P k (fun ω => ω.2 = a) := by
  have h0 := k_ne_zero hk
  unfold Pc
  have : P k (fun ω : Fin k × Fin k => ω.2 = a ∧ ω.1 = s) = P k (fun ω => ω.1 = s ∧ ω.2 = a) := by
    unfold P; congr 3; ext ω; simp only [mem_filter, mem_univ, true_and]; exact and_comm
  rw [this, prob_joint, prob_seed hk, prob_answer hk]
  field_simp

theorem prob_success : P k success = 1 / k := by
  have := k_ne_zero hk
  unfold P; rw [card_success]; field_simp

theorem cond_success_match : Pc k success success = 1 := by
  have := k_ne_zero hk
  unfold Pc
  have h1 : P k (fun ω : Fin k × Fin k => success ω ∧ success ω) = 1 / k := by
    unfold P; rw [card_success_success]; field_simp
  rw [h1, prob_success hk]; field_simp

theorem cond_seed (s : Fin k) : Pc k success (fun ω => ω.1 = s) = 1 / k := by
  have := k_ne_zero hk
  unfold Pc
  have h1 : P k (fun ω : Fin k × Fin k => ω.1 = s ∧ success ω) = 1 / (k : ℝ) ^ 2 := by
    unfold P; rw [card_seed_success]; simp
  rw [h1, prob_success hk]; field_simp

theorem cond_answer (a : Fin k) : Pc k success (fun ω => ω.2 = a) = 1 / k := by
  have := k_ne_zero hk
  unfold Pc
  have h1 : P k (fun ω : Fin k × Fin k => ω.2 = a ∧ success ω) = 1 / (k : ℝ) ^ 2 := by
    unfold P; rw [card_answer_success]; simp
  rw [h1, prob_success hk]; field_simp

theorem cond_joint (s a : Fin k) :
    Pc k success (fun ω => ω.1 = s ∧ ω.2 = a) = if s = a then 1 / (k : ℝ) else 0 := by
  have := k_ne_zero hk
  unfold Pc
  have h1 : P k (fun ω : Fin k × Fin k => (ω.1 = s ∧ ω.2 = a) ∧ success ω)
      = (if s = a then 1 else 0) / (k : ℝ) ^ 2 := by
    unfold P; rw [card_joint_success]; push_cast; rfl
  rw [h1, prob_success hk]
  split_ifs
  · field_simp
  · simp

/-- The seed value `0`. -/
def s0 : Fin k := ⟨0, by omega⟩

/-- The answer value `1`. -/
def a1 : Fin k := ⟨1, by omega⟩

lemma s0_ne_a1 : s0 hk ≠ a1 hk := by
  simp [s0, a1, Fin.ext_iff]

theorem cond_joint_zero_one :
    Pc k success (fun ω => ω.1 = s0 hk ∧ ω.2 = a1 hk) = 0 := by
  rw [cond_joint hk]; simp [s0_ne_a1 hk]

theorem cond_marginals_zero_one :
    Pc k success (fun ω => ω.1 = s0 hk) * Pc k success (fun ω => ω.2 = a1 hk)
      = 1 / (k : ℝ) ^ 2 := by
  rw [cond_seed hk, cond_answer hk]; ring

theorem not_indep_conditional :
    ∃ s a : Fin k, Pc k success (fun ω => ω.1 = s ∧ ω.2 = a)
      ≠ Pc k success (fun ω => ω.1 = s) * Pc k success (fun ω => ω.2 = a) := by
  refine ⟨s0 hk, a1 hk, ?_⟩
  rw [cond_joint_zero_one hk, cond_marginals_zero_one hk]
  have := k_ne_zero hk
  positivity

theorem cond_answer_determined (s : Fin k) :
    Pc k (fun ω => ω.1 = s ∧ success ω) (fun ω => ω.2 = s) = 1 := by
  have := k_ne_zero hk
  unfold Pc
  have h1 : P k (fun ω : Fin k × Fin k => ω.2 = s ∧ (ω.1 = s ∧ success ω))
      = P k (fun ω => ω.1 = s ∧ success ω) := by
    unfold P; congr 3; ext ω
    simp only [mem_filter, mem_univ, true_and]; simp only [success]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro ⟨h1, h2⟩; exact ⟨h2.symm.trans h1, h1, h2⟩
  have h2 : P k (fun ω : Fin k × Fin k => ω.1 = s ∧ success ω) = 1 / (k : ℝ) ^ 2 := by
    unfold P; rw [card_seed_success]; simp
  rw [h1, h2]; field_simp

theorem postselection_collider :
    (∀ s a : Fin k, P k (fun ω => ω.1 = s ∧ ω.2 = a)
        = P k (fun ω => ω.1 = s) * P k (fun ω => ω.2 = a)) ∧
    Pc k success success = 1 ∧
    Pc k success (fun ω => ω.1 = s0 hk ∧ ω.2 = a1 hk) = 0 ∧
    Pc k success (fun ω => ω.1 = s0 hk) * Pc k success (fun ω => ω.2 = a1 hk)
      = 1 / (k : ℝ) ^ 2 ∧
    ∃ s a : Fin k, Pc k success (fun ω => ω.1 = s ∧ ω.2 = a)
      ≠ Pc k success (fun ω => ω.1 = s) * Pc k success (fun ω => ω.2 = a) :=
  ⟨indep_unconditional hk, cond_success_match hk, cond_joint_zero_one hk,
    cond_marginals_zero_one hk, not_indep_conditional hk⟩

end

end PostselectionColliderA
