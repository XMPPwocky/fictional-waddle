import Mathlib

/-!
# Lewis signaling games with `n` states, signals and acts

States, signals and acts are all `Fin n`. A sender is `s : Fin n → Fin n` (state to signal),
a receiver is `r : Fin n → Fin n` (signal to act). Communication succeeds on state `x`
iff `r (s x) = x`. A signaling system is a pair with `r ∘ s = id`.

PROVED:
* `isSignalingSystem_iff_forall`: `(s, r)` is a signaling system iff communication succeeds on
  every state.
* `isSignalingSystem_iff` (part 1): `(s, r)` is a signaling system iff `s` is a bijection and
  `r` is its inverse; `isSignalingSystem_iff_perm` is the same statement phrased with a
  permutation `e` with `⇑e = s` and `⇑e.symm = r`.
* `gauge` (part 2): for every permutation `π` of signals, `(π ∘ s, r ∘ π⁻¹)` is again a
  signaling system. `gauge_transitive`: any two signaling systems are related by exactly one
  such `π`.
* `card_signalingSystems` (part 3): the number of signaling systems is `n!`
  (`Nat.card` of the subtype of pairs `(s, r)` with `r ∘ s = id`).
* `numCorrect_mismatch` (part 4a): if speaker 1 sends with `s` and speaker 2 decodes with
  `s'⁻¹`, the number of correctly communicated states equals the number of fixed points of
  `s'⁻¹ * s` (as a `Finset` count and as `Fintype.card (Function.fixedPoints _)`).
* `card_perm_fix` : for `n ≥ 1` and every `x`, exactly `(n-1)!` permutations fix `x`.
* `sum_numCorrect`, `average_numCorrect`, `expect_numCorrect` (part 4b): for `n ≥ 1`, summed over
  all `n!` permutations `s'` the number of correct states is `n!`, so the uniform average
  (sum divided by `Fintype.card (Perm (Fin n)) = n!`, and also Mathlib's `𝔼`) is exactly `1`.
* `average_successFraction`, `expect_successFraction`: the expected success fraction is `1 / n`.

INTERPRETED:
* "Uniform average over the `n!` choices of `s'`" is the sum over `Equiv.Perm (Fin n)` divided by
  its cardinality, computed in `ℚ`; the `𝔼` versions use `Finset.expect` over `univ`.
* The mismatched receiver `s'⁻¹` is `s'.symm`; `s'⁻¹ * s` is composition `s'⁻¹ ∘ s`.
* The hypothesis `n ≥ 1` is used only in part 4b (for `n = 0` the sum is `0 ≠ 0! = 1`).
-/

namespace LewisSignalingGaugeB

open Finset Equiv
open scoped BigOperators

variable {n : ℕ}

/-- Communication on state `x` succeeds: the receiver's act equals the state. -/
def Succeeds (s r : Fin n → Fin n) (x : Fin n) : Prop := r (s x) = x

/-- A signaling system: `r ∘ s = id`. -/
def IsSignalingSystem (s r : Fin n → Fin n) : Prop := r ∘ s = id

theorem isSignalingSystem_iff_forall (s r : Fin n → Fin n) :
    IsSignalingSystem s r ↔ ∀ x, Succeeds s r x := by
  simp [IsSignalingSystem, Succeeds, funext_iff]

/-- Part (1): signaling systems are exactly (bijection, its inverse). -/
theorem isSignalingSystem_iff (s r : Fin n → Fin n) :
    IsSignalingSystem s r ↔
      ∃ h : Function.Bijective s, r = ⇑(Equiv.ofBijective s h).symm := by
  constructor
  · intro hsr
    have hl : Function.LeftInverse r s := fun x => congrFun hsr x
    have hb : Function.Bijective s := Finite.injective_iff_bijective.mp hl.injective
    refine ⟨hb, ?_⟩
    funext y
    obtain ⟨x, rfl⟩ := hb.2 y
    rw [hl x]
    exact ((Equiv.ofBijective s hb).symm_apply_apply x).symm
  · rintro ⟨hb, rfl⟩
    funext x
    exact (Equiv.ofBijective s hb).symm_apply_apply x

/-- Part (1), permutation form. -/
theorem isSignalingSystem_iff_perm (s r : Fin n → Fin n) :
    IsSignalingSystem s r ↔ ∃ e : Perm (Fin n), ⇑e = s ∧ ⇑e.symm = r := by
  rw [isSignalingSystem_iff]
  constructor
  · rintro ⟨hb, rfl⟩
    exact ⟨Equiv.ofBijective s hb, rfl, rfl⟩
  · rintro ⟨e, rfl, rfl⟩
    refine ⟨e.bijective, ?_⟩
    funext y
    exact (Equiv.ofBijective _ e.bijective).injective (by simp)

/-- Part (2): gauge freedom under relabeling of signals. -/
theorem gauge (s r : Fin n → Fin n) (h : IsSignalingSystem s r) (π : Perm (Fin n)) :
    IsSignalingSystem (π ∘ s) (r ∘ π.symm) := by
  funext x
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  exact congrFun h x

/-- Any two signaling systems differ by exactly one relabeling of signals. -/
theorem gauge_transitive (s r s' r' : Fin n → Fin n) (h : IsSignalingSystem s r)
    (h' : IsSignalingSystem s' r') :
    ∃! π : Perm (Fin n), s' = π ∘ s ∧ r' = r ∘ π.symm := by
  obtain ⟨e, rfl, rfl⟩ := (isSignalingSystem_iff_perm s r).mp h
  obtain ⟨e', rfl, rfl⟩ := (isSignalingSystem_iff_perm s' r').mp h'
  refine ⟨e' * e.symm, ⟨?_, ?_⟩, ?_⟩
  · funext x; simp [Perm.mul_def]
  · funext x; simp [Perm.mul_def]
  · rintro π ⟨h1, -⟩
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    have := congrFun h1 x
    simp only [Function.comp_apply] at this
    simp [← this]

/-- The type of signaling systems. -/
def SignalingSystem (n : ℕ) : Type :=
  {p : (Fin n → Fin n) × (Fin n → Fin n) // IsSignalingSystem p.1 p.2}

/-- Signaling systems are in bijection with permutations. -/
noncomputable def permEquivSignalingSystem : Perm (Fin n) ≃ SignalingSystem n where
  toFun e := ⟨(⇑e, ⇑e.symm), funext e.symm_apply_apply⟩
  invFun p := Equiv.ofBijective p.1.1 ((isSignalingSystem_iff _ _).mp p.2).1
  left_inv e := by ext x; rfl
  right_inv p := by
    obtain ⟨⟨s, r⟩, h⟩ := p
    obtain ⟨hb, rfl⟩ := (isSignalingSystem_iff s r).mp h
    rfl

/-- Part (3): there are exactly `n!` signaling systems. -/
theorem card_signalingSystems : Nat.card (SignalingSystem n) = n.factorial := by
  rw [← Nat.card_congr permEquivSignalingSystem, Nat.card_perm, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- Number of states communicated correctly by sender `s` and receiver `r`. -/
def numCorrect (s r : Fin n → Fin n) : ℕ := #{x | r (s x) = x}

/-- Part (4a): mismatch count equals the number of fixed points of `s'⁻¹ * s`. -/
theorem numCorrect_mismatch (s s' : Perm (Fin n)) :
    numCorrect s s'.symm = #{x | (s'⁻¹ * s) x = x} := rfl

theorem numCorrect_mismatch_fixedPoints (s s' : Perm (Fin n)) :
    numCorrect s s'.symm = Fintype.card (Function.fixedPoints ⇑(s'⁻¹ * s)) := by
  rw [numCorrect_mismatch, Fintype.card_ofFinset]
  rfl

lemma card_apply_eq_left (x y y' : Fin n) :
    #{σ : Perm (Fin n) | σ x = y} = #{σ : Perm (Fin n) | σ x = y'} := by
  apply Finset.card_nbij' (fun σ => Equiv.swap y y' * σ) (fun σ => Equiv.swap y y' * σ)
  · intro σ hσ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    simp [hσ]
  · intro σ hσ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    simp [hσ]
  · intro σ _
    exact Equiv.swap_mul_self_mul y y' σ
  · intro σ _
    exact Equiv.swap_mul_self_mul y y' σ

lemma card_apply_eq_right (x x' y : Fin n) :
    #{σ : Perm (Fin n) | σ x = y} = #{σ : Perm (Fin n) | σ x' = y} := by
  apply Finset.card_nbij' (fun σ => σ * Equiv.swap x x') (fun σ => σ * Equiv.swap x x')
  · intro σ hσ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    simp [hσ]
  · intro σ hσ
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    simp [hσ]
  · intro σ _
    exact Equiv.mul_swap_mul_self x x' σ
  · intro σ _
    exact Equiv.mul_swap_mul_self x x' σ

lemma card_apply_eq (x y z : Fin n) :
    #{σ : Perm (Fin n) | σ x = y} = #{σ : Perm (Fin n) | σ z = z} := by
  rw [card_apply_eq_left x y z, card_apply_eq_right x z z]

lemma mul_card_fix (z : Fin n) :
    n * #{σ : Perm (Fin n) | σ z = z} = n.factorial := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Perm (Fin n))))
    (t := univ) (f := fun σ => σ z) (fun _ _ => mem_univ _)
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h
  rw [h, Finset.sum_congr rfl (fun y _ => card_apply_eq z y z), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- For each `x`, exactly `(n-1)!` permutations fix `x`. -/
theorem card_perm_fix (x : Fin n) :
    #{σ : Perm (Fin n) | σ x = x} = (n - 1).factorial := by
  have hn : 0 < n := Fin.pos x
  have h := mul_card_fix x
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.factorial_succ] at h
  simpa using Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) h

/-- Part (4b), sum form: summed over all `s'`, the number of correct states is `n!`. -/
theorem sum_numCorrect (hn : 1 ≤ n) (s : Perm (Fin n)) :
    ∑ s' : Perm (Fin n), numCorrect s s'.symm = n.factorial := by
  have key : ∀ s' : Perm (Fin n),
      numCorrect s s'.symm = ∑ x, if s' x = s x then 1 else 0 := by
    intro s'
    unfold numCorrect
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact if_congr (s'.symm_apply_eq.trans eq_comm) rfl rfl
  simp_rw [key]
  rw [Finset.sum_comm]
  simp_rw [← Finset.card_filter]
  rw [Finset.sum_congr rfl (fun x _ => card_apply_eq x (s x) ⟨0, hn⟩), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_card_fix]

/-- Part (4b): the uniform average number of correct states is exactly `1`. -/
theorem average_numCorrect (hn : 1 ≤ n) (s : Perm (Fin n)) :
    (∑ s' : Perm (Fin n), (numCorrect s s'.symm : ℚ)) / (Fintype.card (Perm (Fin n)) : ℚ)
      = 1 := by
  rw [← Nat.cast_sum, sum_numCorrect hn, Fintype.card_perm, Fintype.card_fin]
  have : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  exact div_self this

theorem expect_numCorrect (hn : 1 ≤ n) (s : Perm (Fin n)) :
    𝔼 s' : Perm (Fin n), (numCorrect s s'.symm : ℚ) = 1 := by
  rw [Fintype.expect_eq_sum_div_card]
  exact average_numCorrect hn s

/-- Part (4b): the expected success fraction is `1 / n`. -/
theorem average_successFraction (hn : 1 ≤ n) (s : Perm (Fin n)) :
    (∑ s' : Perm (Fin n), (numCorrect s s'.symm : ℚ) / n) / (Fintype.card (Perm (Fin n)) : ℚ)
      = 1 / n := by
  rw [← Finset.sum_div, div_right_comm, average_numCorrect hn]

theorem expect_successFraction (hn : 1 ≤ n) (s : Perm (Fin n)) :
    𝔼 s' : Perm (Fin n), (numCorrect s s'.symm : ℚ) / n = 1 / n := by
  rw [Fintype.expect_eq_sum_div_card]
  exact average_successFraction hn s

end LewisSignalingGaugeB
