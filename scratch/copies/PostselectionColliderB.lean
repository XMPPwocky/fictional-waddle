import Mathlib

/-!
# Postselection on a collider creates correlation without causation

Finite model: a seed `S` and an answer `A`, independent and uniform on `Fin k`
(`k ≥ 2`), i.e. the uniform distribution on `Fin k × Fin k`. Success is the
event `S = A`. Probabilities are exact rationals: `prob k E = #E / k²`, and
`condSucc k E = prob k (E ∧ success) / prob k success`.

PROVED
* `prob_S_eq` : `P(S = s) = 1/k`.
* `prob_A_eq` : `P(A = a) = 1/k`.
* `prob_joint_eq` : `P(S = s ∧ A = a) = 1/k²`.
* `indep_uncond` : unconditionally `P(S = s ∧ A = a) = P(S = s) · P(A = a)` for all `s, a`.
* `prob_A_given_S` : `P(A = a | S = s) = P(A = a)`; the seed has no influence on the
  answer's distribution (the joint law is the product law, so nothing in the model
  routes `S` into `A`).
* `prob_success` : `P(success) = 1/k`.
* `cond_success_match` : `P(S = A | success) = 1`.
* `cond_offdiag_zero` : for `s ≠ a`, `P(S = s ∧ A = a | success) = 0`.
* `cond_diag` : `P(S = s ∧ A = s | success) = 1/k`.
* `cond_S_marg` : `P(S = s | success) = 1/k`.
* `cond_A_marg` : `P(A = a | success) = 1/k`.
* `cond_prod_marg` : `P(S = s | success) · P(A = a | success) = 1/k²`.
* `cond_example` : for `k ≥ 2`, `P(S = 0 ∧ A = 1 | success) = 0` while
  `P(S = 0 | success) · P(A = 1 | success) = 1/k²`.
* `not_indep_cond` : for `k ≥ 2`, `S` and `A` are not independent conditioned on success.
* `postselection_collider` : the combined statement: unconditional independence with
  `A`'s law unaffected by `S`, perfect agreement after conditioning on success, and
  failure of conditional independence.
-/

namespace PostselectionColliderB

open Finset

/-- Probability of an event under the uniform law on `Fin k × Fin k`. -/
def prob (k : ℕ) (E : Fin k × Fin k → Prop) [DecidablePred E] : ℚ :=
  ((univ.filter E).card : ℚ) / ((k : ℚ) ^ 2)

/-- The success event `S = A`. -/
def success {k : ℕ} (p : Fin k × Fin k) : Prop := p.1 = p.2

instance {k : ℕ} : DecidablePred (@success k) := fun p => inferInstanceAs (Decidable (p.1 = p.2))

/-- Conditional probability given success. -/
def condSucc (k : ℕ) (E : Fin k × Fin k → Prop) [DecidablePred E] : ℚ :=
  prob k (fun p => E p ∧ success p) / prob k success

/-- Conditional probability given `S = s`. -/
def condS (k : ℕ) (s : Fin k) (E : Fin k × Fin k → Prop) [DecidablePred E] : ℚ :=
  prob k (fun p => E p ∧ p.1 = s) / prob k (fun p => p.1 = s)

lemma card_S (k : ℕ) (s : Fin k) :
    (univ.filter (fun p : Fin k × Fin k => p.1 = s)).card = k := by
  have : univ.filter (fun p : Fin k × Fin k => p.1 = s) = ({s} : Finset (Fin k)) ×ˢ univ := by
    ext p; simp only [mem_filter_univ, mem_product, mem_singleton, mem_univ, and_true]
  rw [this, card_product]; simp

lemma card_A (k : ℕ) (a : Fin k) :
    (univ.filter (fun p : Fin k × Fin k => p.2 = a)).card = k := by
  have : univ.filter (fun p : Fin k × Fin k => p.2 = a) = (univ : Finset (Fin k)) ×ˢ {a} := by
    ext p; simp only [mem_filter_univ, mem_product, mem_singleton, mem_univ, true_and]
  rw [this, card_product]; simp

lemma card_joint (k : ℕ) (s a : Fin k) :
    (univ.filter (fun p : Fin k × Fin k => p.1 = s ∧ p.2 = a)).card = 1 := by
  have : univ.filter (fun p : Fin k × Fin k => p.1 = s ∧ p.2 = a) = {(s, a)} := by
    ext p; simp only [mem_filter_univ, mem_singleton, Prod.ext_iff]
  rw [this]; simp

lemma card_success (k : ℕ) :
    (univ.filter (fun p : Fin k × Fin k => success p)).card = k := by
  have : univ.filter (fun p : Fin k × Fin k => success p) = (univ : Finset (Fin k)).diag := by
    ext p; rw [mem_filter_univ, Finset.mem_diag]; simp [success]
  rw [this, Finset.diag_card]; simp

lemma card_joint_succ (k : ℕ) (s a : Fin k) :
    (univ.filter (fun p : Fin k × Fin k => (p.1 = s ∧ p.2 = a) ∧ success p)).card
      = if s = a then 1 else 0 := by
  split_ifs with h
  · subst h
    have : univ.filter (fun p : Fin k × Fin k => (p.1 = s ∧ p.2 = s) ∧ success p) = {(s, s)} := by
      ext p; rw [mem_filter_univ]; simp only [mem_singleton, success, Prod.ext_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, h1.trans h2.symm⟩
    rw [this]; simp
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro p - ⟨⟨h1, h2⟩, h3⟩
    exact h (h1.symm.trans (h3.trans h2))

lemma card_S_succ (k : ℕ) (s : Fin k) :
    (univ.filter (fun p : Fin k × Fin k => p.1 = s ∧ success p)).card = 1 := by
  have : univ.filter (fun p : Fin k × Fin k => p.1 = s ∧ success p) = {(s, s)} := by
    ext p; rw [mem_filter_univ]; simp only [mem_singleton, success, Prod.ext_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm.trans h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h1.trans h2.symm⟩
  rw [this]; simp

lemma card_A_succ (k : ℕ) (a : Fin k) :
    (univ.filter (fun p : Fin k × Fin k => p.2 = a ∧ success p)).card = 1 := by
  have : univ.filter (fun p : Fin k × Fin k => p.2 = a ∧ success p) = {(a, a)} := by
    ext p; rw [mem_filter_univ]; simp only [mem_singleton, success, Prod.ext_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2.trans h1, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1.trans h2.symm⟩
  rw [this]; simp

lemma card_match_succ (k : ℕ) :
    (univ.filter (fun p : Fin k × Fin k => p.1 = p.2 ∧ success p)).card = k := by
  have : univ.filter (fun p : Fin k × Fin k => p.1 = p.2 ∧ success p)
      = univ.filter (fun p : Fin k × Fin k => success p) := by
    ext p; rw [mem_filter_univ, mem_filter_univ]; simp only [success, and_self]
  rw [this, card_success]

variable {k : ℕ}

theorem prob_S_eq (hk : 0 < k) (s : Fin k) : prob k (fun p => p.1 = s) = 1 / k := by
  have : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold prob; rw [card_S]; field_simp

theorem prob_A_eq (hk : 0 < k) (a : Fin k) : prob k (fun p => p.2 = a) = 1 / k := by
  have : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold prob; rw [card_A]; field_simp

theorem prob_joint_eq (s a : Fin k) : prob k (fun p => p.1 = s ∧ p.2 = a) = 1 / (k : ℚ) ^ 2 := by
  unfold prob; rw [card_joint]; simp

theorem indep_uncond (hk : 0 < k) (s a : Fin k) :
    prob k (fun p => p.1 = s ∧ p.2 = a) = prob k (fun p => p.1 = s) * prob k (fun p => p.2 = a) := by
  rw [prob_joint_eq, prob_S_eq hk, prob_A_eq hk]; ring

theorem prob_A_given_S (hk : 0 < k) (s a : Fin k) :
    condS k s (fun p => p.2 = a) = prob k (fun p => p.2 = a) := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold condS
  have h : prob k (fun p => p.2 = a ∧ p.1 = s) = prob k (fun p => p.1 = s ∧ p.2 = a) := by
    unfold prob; congr 3; ext p; simp only [mem_filter_univ]; exact and_comm
  rw [h, prob_joint_eq, prob_S_eq hk, prob_A_eq hk]; field_simp

theorem prob_success (hk : 0 < k) : prob k success = 1 / k := by
  have : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold prob; rw [card_success]; field_simp

theorem cond_success_match (hk : 0 < k) : condSucc k (fun p => p.1 = p.2) = 1 := by
  have : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold condSucc; rw [prob_success hk]; unfold prob; rw [card_match_succ]; field_simp

theorem cond_offdiag_zero (s a : Fin k) (h : s ≠ a) :
    condSucc k (fun p => p.1 = s ∧ p.2 = a) = 0 := by
  unfold condSucc prob; rw [card_joint_succ]; simp [h]

theorem cond_diag (hk : 0 < k) (s : Fin k) :
    condSucc k (fun p => p.1 = s ∧ p.2 = s) = 1 / k := by
  have : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold condSucc; rw [prob_success hk]; unfold prob; rw [card_joint_succ]
  simp only [ite_true, Nat.cast_one]; field_simp

theorem cond_S_marg (hk : 0 < k) (s : Fin k) : condSucc k (fun p => p.1 = s) = 1 / k := by
  have : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold condSucc; rw [prob_success hk]; unfold prob; rw [card_S_succ]; push_cast; field_simp

theorem cond_A_marg (hk : 0 < k) (a : Fin k) : condSucc k (fun p => p.2 = a) = 1 / k := by
  have : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold condSucc; rw [prob_success hk]; unfold prob; rw [card_A_succ]; push_cast; field_simp

theorem cond_prod_marg (hk : 0 < k) (s a : Fin k) :
    condSucc k (fun p => p.1 = s) * condSucc k (fun p => p.2 = a) = 1 / (k : ℚ) ^ 2 := by
  rw [cond_S_marg hk, cond_A_marg hk]; ring

theorem cond_example (hk : 2 ≤ k) :
    condSucc k (fun p => p.1 = ⟨0, by omega⟩ ∧ p.2 = ⟨1, by omega⟩) = 0 ∧
    condSucc k (fun p => p.1 = ⟨0, by omega⟩) * condSucc k (fun p => p.2 = ⟨1, by omega⟩)
      = 1 / (k : ℚ) ^ 2 := by
  refine ⟨cond_offdiag_zero _ _ ?_, cond_prod_marg (by omega) _ _⟩
  simp [Fin.ext_iff]

theorem not_indep_cond (hk : 2 ≤ k) :
    ¬ ∀ s a : Fin k, condSucc k (fun p => p.1 = s ∧ p.2 = a)
        = condSucc k (fun p => p.1 = s) * condSucc k (fun p => p.2 = a) := by
  intro h
  obtain ⟨h0, h1⟩ := cond_example hk
  have := h ⟨0, by omega⟩ ⟨1, by omega⟩
  rw [h0, h1] at this
  have hk' : (0 : ℚ) < (k : ℚ) ^ 2 := by
    have : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
    positivity
  have : (0 : ℚ) < 1 / (k : ℚ) ^ 2 := by positivity
  linarith

theorem postselection_collider (hk : 2 ≤ k) :
    (∀ s a : Fin k, prob k (fun p => p.1 = s ∧ p.2 = a)
        = prob k (fun p => p.1 = s) * prob k (fun p => p.2 = a)) ∧
    (∀ s a : Fin k, condS k s (fun p => p.2 = a) = prob k (fun p => p.2 = a)) ∧
    condSucc k (fun p => p.1 = p.2) = 1 ∧
    ¬ ∀ s a : Fin k, condSucc k (fun p => p.1 = s ∧ p.2 = a)
        = condSucc k (fun p => p.1 = s) * condSucc k (fun p => p.2 = a) :=
  ⟨indep_uncond (by omega), prob_A_given_S (by omega), cond_success_match (by omega),
    not_indep_cond hk⟩

end PostselectionColliderB
