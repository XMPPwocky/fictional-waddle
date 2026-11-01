import Mathlib

/-!
# The sign of a permutation as a one-bit probe

## PROVED

* `sign_probe_blind`: for a finite type `α` and any family `F : ι → Equiv.Perm α` with
  `Equiv.Perm.sign (F i) = 1` for every `i`, any two members `F i`, `F j` are `relEq` for the
  response `fun σ _ => Equiv.Perm.sign σ` and the one-element probe set `{()} : Set Unit`.
* `eval_probe_separates`: if `σ ≠ τ` then `σ` and `τ` are not `relEq` for the response
  `fun σ x => σ x` and the probe set `Set.univ : Set α`.
  `relEq_eval_imp_eq`: `relEq` under all inputs implies `σ = τ`.
  `relEq_eval_iff`: `relEq` under all inputs is equivalent to `σ = τ`.
* `sign_map_collapses`: if `3 ≤ Fintype.card α`, there are `σ τ ∈ alternatingGroup α` with
  `σ ≠ τ` and `sign σ = sign τ` (namely `1` and `swap a b * swap b c` for distinct `a b c`).
  `sign_not_injOn_alternating`: under the same hypothesis, `sign` is not injective on
  `alternatingGroup α`.
* `sign_surjective_of_two_le`: if `2 ≤ Fintype.card α`, `sign : Perm α → ℤˣ` is surjective;
  `sign_range_eq`: its range is exactly `{1, -1}`; `card_units_int`: `Fintype.card ℤˣ = 2`.
* `one_time_pad_borromean`: for a finite additive commutative group `G`:
  (a) for every `P`, `K ↦ P + K` is bijective and, for every `C`,
      `Fintype.card {K // P + K = C} = 1`; also for every `K`, `Fintype.card {P // P + K = C} = 1`;
  (b) `P + K = C ↔ P = C - K` and `P + K = C ↔ K = C - P`.
* `fin3_witness`: on `Fin 3`, `1` and `swap 0 1 * swap 1 2` both have sign `1` and are distinct;
  `fin3_family_nonvacuous` packages them as a family `Fin 2 → Perm (Fin 3)` satisfying the
  hypothesis of `sign_probe_blind` with `F 0 ≠ F 1`; `fin3_blind_but_separated` shows that this
  pair is `relEq` under the sign probe and not `relEq` under the evaluation probes.

## INTERPRETED

* The sign is a one-bit boundary: every permutation lies on one side of it, and every cipher
  (all of whose permutations have sign 1) stays on the same side. It is a bridge between the
  realm of permutations and the realm `{1, -1}` that carries exactly one bit.
* The sign map sends many different permutations to the same symbol: the map is not the
  territory.
* Whether two things are "the same" depends on the probe set: the same pair of permutations is
  identified by the sign probe and distinguished by the evaluation probes (relative semantics).
-/

namespace ParityProbe

open Equiv

/-- `a` and `b` are the same relative to the probes `P`. -/
def relEq {Thing Probe R : Type*} (resp : Thing → Probe → R) (P : Set Probe) (a b : Thing) : Prop :=
  ∀ p ∈ P, resp a p = resp b p

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The sign probe: a single probe whose response is the sign. -/
theorem sign_probe_blind {ι : Type*} (F : ι → Perm α) (hF : ∀ i, Perm.sign (F i) = 1)
    (i j : ι) :
    relEq (fun (σ : Perm α) (_ : Unit) => Perm.sign σ) ({()} : Set Unit) (F i) (F j) := by
  intro _ _
  simp only [hF i, hF j]

omit [Fintype α] [DecidableEq α] in
/-- Agreement on every input implies equality. -/
theorem relEq_eval_imp_eq (σ τ : Perm α)
    (h : relEq (fun (σ : Perm α) (x : α) => σ x) (Set.univ : Set α) σ τ) : σ = τ := by
  ext x
  exact h x (Set.mem_univ x)

omit [Fintype α] [DecidableEq α] in
/-- Distinct permutations are separated by evaluation on inputs. -/
theorem eval_probe_separates (σ τ : Perm α) (hne : σ ≠ τ) :
    ¬ relEq (fun (σ : Perm α) (x : α) => σ x) (Set.univ : Set α) σ τ :=
  fun h => hne (relEq_eval_imp_eq σ τ h)

omit [Fintype α] [DecidableEq α] in
theorem relEq_eval_iff (σ τ : Perm α) :
    relEq (fun (σ : Perm α) (x : α) => σ x) (Set.univ : Set α) σ τ ↔ σ = τ := by
  refine ⟨relEq_eval_imp_eq σ τ, ?_⟩
  rintro rfl _ _
  rfl

/-- The 3-cycle `swap a b * swap b c` has sign 1 and is not the identity. -/
theorem three_cycle_facts {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Perm.sign (swap a b * swap b c) = 1 ∧ swap a b * swap b c ≠ 1 := by
  refine ⟨?_, ?_⟩
  · rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hbc]
    decide
  · intro h
    have hc := congrArg (fun σ : Perm α => σ c) h
    simp only [Perm.coe_mul, Function.comp_apply, swap_apply_right,
      Perm.coe_one, id_eq] at hc
    exact hac hc

theorem sign_map_collapses (h3 : 3 ≤ Fintype.card α) :
    ∃ σ ∈ alternatingGroup α, ∃ τ ∈ alternatingGroup α,
      σ ≠ τ ∧ Perm.sign σ = Perm.sign τ := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h3
  obtain ⟨hs, hne⟩ := three_cycle_facts hab hac hbc
  refine ⟨1, (alternatingGroup α).one_mem, swap a b * swap b c,
    Perm.mem_alternatingGroup.mpr hs, Ne.symm hne, ?_⟩
  rw [hs, map_one]

theorem sign_not_injOn_alternating (h3 : 3 ≤ Fintype.card α) :
    ¬ Set.InjOn (Perm.sign : Perm α → ℤˣ) (alternatingGroup α : Set (Perm α)) := by
  intro hinj
  obtain ⟨σ, hσ, τ, hτ, hne, heq⟩ := sign_map_collapses h3
  exact hne (hinj hσ hτ heq)

theorem sign_surjective_of_two_le (h2 : 2 ≤ Fintype.card α) :
    Function.Surjective (Perm.sign : Perm α → ℤˣ) := by
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp h2
  exact Perm.sign_surjective α

theorem sign_range_eq (h2 : 2 ≤ Fintype.card α) :
    Set.range (Perm.sign : Perm α → ℤˣ) = {1, -1} := by
  ext u
  constructor
  · intro _
    rcases Int.units_eq_one_or u with h | h <;> simp [h]
  · intro _
    exact sign_surjective_of_two_le h2 u

theorem card_units_int : Fintype.card ℤˣ = 2 := by
  decide

/-- One-time pad as counting: with `C = P + K`, each ciphertext comes from exactly one key for a
fixed plaintext (and from exactly one plaintext for a fixed key), and any two of `P, K, C`
determine the third. -/
theorem one_time_pad_borromean {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] :
    (∀ P : G, Function.Bijective (fun K : G => P + K)) ∧
    (∀ P C : G, Fintype.card {K : G // P + K = C} = 1) ∧
    (∀ K C : G, Fintype.card {P : G // P + K = C} = 1) ∧
    (∀ P K C : G, P + K = C ↔ P = C - K) ∧
    (∀ P K C : G, P + K = C ↔ K = C - P) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro P
    exact (Equiv.addLeft P).bijective
  · intro P C
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨C - P, add_sub_cancel P C⟩, ?_⟩
    rintro ⟨K, hK⟩
    apply Subtype.ext
    simp only
    rw [← hK]
    abel
  · intro K C
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨C - K, sub_add_cancel C K⟩, ?_⟩
    rintro ⟨P, hP⟩
    apply Subtype.ext
    simp only
    rw [← hP]
    abel
  · intro P K C
    exact eq_sub_iff_add_eq.symm
  · intro P K C
    exact eq_sub_iff_add_eq'.symm

/-- On `Fin 3`, the identity and a 3-cycle both have sign 1 and are distinct. -/
theorem fin3_witness :
    Perm.sign (1 : Perm (Fin 3)) = 1 ∧
    Perm.sign (swap (0 : Fin 3) 1 * swap 1 2) = 1 ∧
    (1 : Perm (Fin 3)) ≠ swap 0 1 * swap 1 2 := by
  obtain ⟨hs, hne⟩ := three_cycle_facts (α := Fin 3) (a := 0) (b := 1) (c := 2)
    (by decide) (by decide) (by decide)
  exact ⟨map_one _, hs, Ne.symm hne⟩

/-- The family used to show `sign_probe_blind` is not vacuous. -/
def fin3Family : Fin 2 → Perm (Fin 3) := ![1, swap 0 1 * swap 1 2]

theorem fin3_family_nonvacuous :
    (∀ i, Perm.sign (fin3Family i) = 1) ∧ fin3Family 0 ≠ fin3Family 1 := by
  obtain ⟨h1, h2, hne⟩ := fin3_witness
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · exact h1
    · exact h2
  · exact hne

theorem fin3_blind_but_separated :
    relEq (fun (σ : Perm (Fin 3)) (_ : Unit) => Perm.sign σ) ({()} : Set Unit)
      (fin3Family 0) (fin3Family 1) ∧
    ¬ relEq (fun (σ : Perm (Fin 3)) (x : Fin 3) => σ x) (Set.univ : Set (Fin 3))
      (fin3Family 0) (fin3Family 1) :=
  ⟨sign_probe_blind fin3Family fin3_family_nonvacuous.1 0 1,
   eval_probe_separates _ _ fin3_family_nonvacuous.2⟩

end ParityProbe

#print axioms ParityProbe.sign_probe_blind
#print axioms ParityProbe.relEq_eval_imp_eq
#print axioms ParityProbe.eval_probe_separates
#print axioms ParityProbe.relEq_eval_iff
#print axioms ParityProbe.three_cycle_facts
#print axioms ParityProbe.sign_map_collapses
#print axioms ParityProbe.sign_not_injOn_alternating
#print axioms ParityProbe.sign_surjective_of_two_le
#print axioms ParityProbe.sign_range_eq
#print axioms ParityProbe.card_units_int
#print axioms ParityProbe.one_time_pad_borromean
#print axioms ParityProbe.fin3_witness
#print axioms ParityProbe.fin3_family_nonvacuous
#print axioms ParityProbe.fin3_blind_but_separated
