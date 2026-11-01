/-
# What a joke verifier can and cannot certify

A joke lands on a listener when it is new to them and their checker accepts it.

PROVED
1. `lands_once`: a joke that lands does not land again once the listener has learned it.
2. `excess_surprise_nonneg` and `excess_surprise_self`: if the teller's messages follow q and the
   listener predicts with p, the expected surprise in excess of the teller's own is
   ∑ q log(q/p) ≥ 0 (Gibbs' inequality), and it is 0 when p = q: messages from your own
   predictive model carry no excess surprise.
3. `selected_agree` and `agreement_uninformative`: among statements kept because two checkers both
   accepted them, the checkers agree on every one, true or false. Their agreement rate is 1 among
   the true ones and 1 among the false ones, so agreement carries no evidence about truth.
4. `unselected_checker_informative`: a third checker that played no part in the selection can
   accept every true selected statement and no false one.

INTERPRETED (not formalized)
- "You cannot tickle yourself": self-generated stimuli are predicted (item 2 with p = q).
- Item 3 is the jointly-selected-checker problem: two checkers trained or chosen on the same filter
  agree by construction. Item 4 is why an independent check (Lean's kernel, market data, a seeded
  human audit) can carry evidence where agreement cannot.
-/

import Mathlib

namespace JokeVerifier

/-! ## 1. A joke lands once -/

def lands {S : Type*} (K : Set S) (V : S → Bool) (s : S) : Prop := s ∉ K ∧ V s = true

theorem lands_once {S : Type*} (K : Set S) (V : S → Bool) (s : S) (_h : lands K V s) :
    ¬ lands (insert s K) V s := by
  intro h2
  exact h2.1 (Set.mem_insert s K)

/-! ## 2. Excess surprise is a KL divergence -/

/-- Expected surprise under the listener's prediction `p` minus the teller's own, when the teller
draws messages from `q`. -/
noncomputable def excessSurprise {ι : Type*} [Fintype ι] (q p : ι → ℝ) : ℝ :=
  ∑ i, q i * Real.log (q i / p i)

theorem term_ge {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : a - b ≤ a * Real.log (a / b) := by
  have h1 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb ha)
  have h2 : Real.log (a / b) = - Real.log (b / a) := by
    rw [← Real.log_inv, inv_div]
  rw [h2]
  have h3 : a * (b / a - 1) = b - a := by field_simp
  nlinarith [h1, h3]

theorem excess_surprise_nonneg {ι : Type*} [Fintype ι] (q p : ι → ℝ)
    (hq : ∀ i, 0 < q i) (hp : ∀ i, 0 < p i) (hsq : ∑ i, q i = 1) (hsp : ∑ i, p i = 1) :
    0 ≤ excessSurprise q p := by
  unfold excessSurprise
  have : ∑ i, (q i - p i) ≤ ∑ i, q i * Real.log (q i / p i) :=
    Finset.sum_le_sum fun i _ => term_ge (hq i) (hp i)
  rw [Finset.sum_sub_distrib, hsq, hsp, sub_self] at this
  exact this

theorem excess_surprise_self {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ i, 0 < q i) :
    excessSurprise q q = 0 := by
  unfold excessSurprise
  apply Finset.sum_eq_zero
  intro i _
  rw [div_self (hq i).ne', Real.log_one, mul_zero]

/-! ## 3. Agreement after joint selection carries no evidence -/

section Selection

variable {S : Type*}

/-- Statements kept because both checkers accepted them. -/
def selected (U : Finset S) (VA VB : S → Bool) : Finset S :=
  U.filter fun s => VA s = true ∧ VB s = true

theorem selected_agree (U : Finset S) (VA VB : S → Bool) :
    ∀ s ∈ selected U VA VB, VA s = VB s := by
  intro s hs
  simp only [selected, Finset.mem_filter] at hs
  rw [hs.2.1, hs.2.2]

/-- Fraction of a finite set on which a predicate holds. -/
def rate (A : Finset S) (P : S → Bool) : ℚ := ((A.filter fun s => P s = true).card : ℚ) / A.card

theorem rate_agree_one (U : Finset S) (VA VB : S → Bool) (T : S → Bool) (b : Bool)
    (hne : ((selected U VA VB).filter fun s => T s = b).Nonempty) :
    rate ((selected U VA VB).filter fun s => T s = b) (fun s => decide (VA s = VB s)) = 1 := by
  unfold rate
  have hall : (((selected U VA VB).filter fun s => T s = b).filter
      fun s => decide (VA s = VB s) = true) = (selected U VA VB).filter fun s => T s = b := by
    apply Finset.filter_true_of_mem
    intro s hs
    have := selected_agree U VA VB s (Finset.mem_of_mem_filter s hs)
    simpa using this
  rw [hall, div_self]
  exact_mod_cast (Finset.card_pos.mpr hne).ne'

theorem agreement_uninformative (U : Finset S) (VA VB : S → Bool) (T : S → Bool)
    (htrue : ((selected U VA VB).filter fun s => T s = true).Nonempty)
    (hfalse : ((selected U VA VB).filter fun s => T s = false).Nonempty) :
    rate ((selected U VA VB).filter fun s => T s = true) (fun s => decide (VA s = VB s)) =
      rate ((selected U VA VB).filter fun s => T s = false) (fun s => decide (VA s = VB s)) := by
  rw [rate_agree_one U VA VB T true htrue, rate_agree_one U VA VB T false hfalse]

end Selection

/-! ## 4. An unselected checker can carry evidence -/

theorem unselected_checker_informative :
    ∃ (U : Finset (Fin 4)) (VA VB VC T : Fin 4 → Bool),
      ((selected U VA VB).filter fun s => T s = true).Nonempty ∧
      ((selected U VA VB).filter fun s => T s = false).Nonempty ∧
      rate ((selected U VA VB).filter fun s => T s = true) VC = 1 ∧
      rate ((selected U VA VB).filter fun s => T s = false) VC = 0 := by
  refine ⟨Finset.univ, fun _ => true, fun _ => true, fun s => decide (s.val < 2),
    fun s => decide (s.val < 2), by decide, by decide, ?_, ?_⟩
  · have h : ((((selected Finset.univ (fun _ => true) (fun _ => true)).filter
        fun s : Fin 4 => decide (s.val < 2) = true).filter
        fun s => decide (s.val < 2) = true).card) = 2 := by decide
    have h' : (((selected Finset.univ (fun _ => true) (fun _ => true)).filter
        fun s : Fin 4 => decide (s.val < 2) = true).card) = 2 := by decide
    unfold rate
    rw [h, h']
    norm_num
  · have h : ((((selected Finset.univ (fun _ => true) (fun _ => true)).filter
        fun s : Fin 4 => decide (s.val < 2) = false).filter
        fun s => decide (s.val < 2) = true).card) = 0 := by decide
    unfold rate
    rw [h]
    norm_num

end JokeVerifier

#print axioms JokeVerifier.lands_once
#print axioms JokeVerifier.excess_surprise_nonneg
#print axioms JokeVerifier.excess_surprise_self
#print axioms JokeVerifier.selected_agree
#print axioms JokeVerifier.agreement_uninformative
#print axioms JokeVerifier.unselected_checker_informative
