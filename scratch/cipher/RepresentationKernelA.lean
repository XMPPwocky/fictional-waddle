import Mathlib

/-!
# What a representation can and cannot distinguish

Two elements are "the same relative to probes P" when every probe in P returns the
same response on both. For a group homomorphism `ρ : G →* H` used as the response
(single probe `()`, response `fun g _ => ρ g`), this relation is computed exactly.

## PROVED

* `relEq_hom_iff_eq`: `relEq (fun g (_ : Unit) => ρ g) {()} g g' ↔ ρ g = ρ g'`.
* `relEq_hom_iff_mem_ker`: for every group homomorphism `ρ : G →* H` and all `g g' : G`,
  `relEq (fun g (_ : Unit) => ρ g) {()} g g' ↔ g⁻¹ * g' ∈ ρ.ker`.
* `relEq_hom_iff_ker_coset`: the same relation is equivalent to `∃ k ∈ ρ.ker, g' = g * k`
  (`g'` lies in the left coset of the kernel through `g`).
* `injective_iff_relEq_iff_eq`: `Function.Injective ρ ↔ ∀ g g', (relEq ... g g' ↔ g = g')`.
* `injective_iff_ker_eq_bot_relEq`: `(∀ g g', relEq ... g g' ↔ g = g') ↔ ρ.ker = ⊥`.
* `sign_ker_eq_alternatingGroup`: `(Equiv.Perm.sign : Perm α →* ℤˣ).ker = alternatingGroup α`
  for `[Fintype α] [DecidableEq α]`.
* `relEq_sign_iff`: `relEq (fun σ (_ : Unit) => sign σ) {()} σ τ ↔ σ⁻¹ * τ ∈ alternatingGroup α`.
* `relEq_sign_of_mem_alternating`: any two members of `alternatingGroup α` are `relEq`
  for the sign response.
* `relEq_sign_of_mul_mem_alternating`: if `σ⁻¹ * τ` is even then `relEq` holds (one
  direction of `relEq_sign_iff`, stated separately for use).
* `card_quotient_ker_sign`: if `2 ≤ Fintype.card α`, then
  `Nat.card (Perm α ⧸ (sign : Perm α →* ℤˣ).ker) = 2`; and
  `fintype_card_quotient_ker_sign`: the same with `Fintype.card` for any `Fintype`
  instance on the quotient.
* `quotient_ker_sign_mulEquiv` (a definition, not a theorem): for `Nontrivial α`,
  a group isomorphism `Perm α ⧸ ker sign ≃* ℤˣ`.
* `card_quotient_ker_sign_iff`: `Nat.card (Perm α ⧸ ker sign) = 2 ↔ 2 ≤ Fintype.card α`
  (for `Fintype.card α ≤ 1` the quotient has one element).
* `card_quotient_ker_sign_fin3`, `fintype_card_quotient_ker_sign_fin3`,
  `relEq_sign_of_mul_mem_alternating_fin3`: the hypotheses of the corresponding general
  statements instantiated on `Fin 3`.
* `fin3_example`: on `Fin 3`, `1` and `finRotate 3` are distinct, both lie in
  `alternatingGroup (Fin 3)`, are `relEq` for sign; `Equiv.swap 0 1` is not `relEq` to `1`.

## CITED / INTERPRETED (not proved here)

* Reading: the equivalence classes of `relEq` for a homomorphism response are the cosets
  of its kernel, so the kernel is exactly the information the representation discards;
  a faithful representation discards nothing.
* Reading: the sign representation of a symmetric group retains exactly one bit (parity).
  "One bit" here means the quotient has two elements; no information-theoretic quantity
  is defined or proved.
-/

namespace RepresentationKernelA

/-- a and b are the same relative to the probes P. -/
def relEq {Thing Probe R : Type*} (resp : Thing -> Probe -> R) (P : Set Probe) (a b : Thing) : Prop := ∀ p ∈ P, resp a p = resp b p

section Hom

variable {G H : Type*} [Group G] [Group H]

theorem relEq_hom_iff_eq (ρ : G →* H) (g g' : G) :
    relEq (fun g (_ : Unit) => ρ g) {()} g g' ↔ ρ g = ρ g' := by
  simp [relEq]

/-- What `ρ` cannot distinguish is exactly its kernel (as left cosets). -/
theorem relEq_hom_iff_mem_ker (ρ : G →* H) (g g' : G) :
    relEq (fun g (_ : Unit) => ρ g) {()} g g' ↔ g⁻¹ * g' ∈ ρ.ker := by
  rw [relEq_hom_iff_eq, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]

theorem relEq_hom_iff_ker_coset (ρ : G →* H) (g g' : G) :
    relEq (fun g (_ : Unit) => ρ g) {()} g g' ↔ ∃ k ∈ ρ.ker, g' = g * k := by
  rw [relEq_hom_iff_mem_ker]
  constructor
  · intro h
    exact ⟨g⁻¹ * g', h, by group⟩
  · rintro ⟨k, hk, rfl⟩
    simpa using hk

/-- `ρ` is faithful iff it distinguishes every pair of distinct elements. -/
theorem injective_iff_relEq_iff_eq (ρ : G →* H) :
    Function.Injective ρ ↔ ∀ g g' : G, (relEq (fun g (_ : Unit) => ρ g) {()} g g' ↔ g = g') := by
  simp only [relEq_hom_iff_eq]
  constructor
  · intro h g g'
    exact ⟨fun e => h e, fun e => e ▸ rfl⟩
  · intro h g g' e
    exact (h g g').1 e

theorem injective_iff_ker_eq_bot_relEq (ρ : G →* H) :
    (∀ g g' : G, (relEq (fun g (_ : Unit) => ρ g) {()} g g' ↔ g = g')) ↔ ρ.ker = ⊥ := by
  rw [← injective_iff_relEq_iff_eq, MonoidHom.ker_eq_bot_iff]

end Hom

section Sign

open Equiv

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem sign_ker_eq_alternatingGroup :
    (Perm.sign : Perm α →* ℤˣ).ker = alternatingGroup α := rfl

theorem relEq_sign_iff (σ τ : Perm α) :
    relEq (fun σ (_ : Unit) => Perm.sign σ) {()} σ τ ↔ σ⁻¹ * τ ∈ alternatingGroup α := by
  rw [← sign_ker_eq_alternatingGroup]
  exact relEq_hom_iff_mem_ker Perm.sign σ τ

theorem relEq_sign_of_mul_mem_alternating (σ τ : Perm α) (h : σ⁻¹ * τ ∈ alternatingGroup α) :
    relEq (fun σ (_ : Unit) => Perm.sign σ) {()} σ τ :=
  (relEq_sign_iff σ τ).2 h

/-- All even permutations feel identical to the sign representation. -/
theorem relEq_sign_of_mem_alternating (σ τ : Perm α)
    (hσ : σ ∈ alternatingGroup α) (hτ : τ ∈ alternatingGroup α) :
    relEq (fun σ (_ : Unit) => Perm.sign σ) {()} σ τ := by
  rw [relEq_sign_iff]
  exact (alternatingGroup α).mul_mem ((alternatingGroup α).inv_mem hσ) hτ

/-- For a nontrivial type, the quotient by the kernel of sign is isomorphic to `ℤˣ`. -/
noncomputable def quotient_ker_sign_mulEquiv [Nontrivial α] :
    Perm α ⧸ (Perm.sign : Perm α →* ℤˣ).ker ≃* ℤˣ :=
  QuotientGroup.quotientKerEquivOfSurjective _ (Perm.sign_surjective α)

/-- The sign representation retains exactly two classes. -/
theorem card_quotient_ker_sign (h : 2 ≤ Fintype.card α) :
    Nat.card (Perm α ⧸ (Perm.sign : Perm α →* ℤˣ).ker) = 2 := by
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.1 h
  rw [Nat.card_congr (quotient_ker_sign_mulEquiv (α := α)).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_units_int]

theorem fintype_card_quotient_ker_sign (h : 2 ≤ Fintype.card α)
    [Fintype (Perm α ⧸ (Perm.sign : Perm α →* ℤˣ).ker)] :
    Fintype.card (Perm α ⧸ (Perm.sign : Perm α →* ℤˣ).ker) = 2 := by
  rw [← Nat.card_eq_fintype_card]
  exact card_quotient_ker_sign h

/-- The bound `2 ≤ card α` is necessary: otherwise the quotient is trivial. -/
theorem card_quotient_ker_sign_iff :
    Nat.card (Perm α ⧸ (Perm.sign : Perm α →* ℤˣ).ker) = 2 ↔ 2 ≤ Fintype.card α := by
  refine ⟨fun hq => ?_, card_quotient_ker_sign⟩
  by_contra hlt
  push Not at hlt
  have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.1 (by omega)
  have : Subsingleton (Perm α ⧸ (Perm.sign : Perm α →* ℤˣ).ker) := by
    constructor
    intro x y
    induction x using QuotientGroup.induction_on
    induction y using QuotientGroup.induction_on
    congr 1
    exact Subsingleton.elim _ _
  let _ : Unique (Perm α ⧸ (Perm.sign : Perm α →* ℤˣ).ker) := Unique.mk' _
  rw [Nat.card_unique] at hq
  omega

end Sign

section Example

open Equiv

/-- Non-vacuity on `Fin 3`: two distinct even permutations feel identical to sign,
and an odd one feels different. -/
theorem fin3_example :
    (1 : Perm (Fin 3)) ≠ finRotate 3 ∧
    (1 : Perm (Fin 3)) ∈ alternatingGroup (Fin 3) ∧
    finRotate 3 ∈ alternatingGroup (Fin 3) ∧
    relEq (fun σ (_ : Unit) => Perm.sign σ) {()} (1 : Perm (Fin 3)) (finRotate 3) ∧
    swap (0 : Fin 3) 1 ∉ alternatingGroup (Fin 3) ∧
    ¬ relEq (fun σ (_ : Unit) => Perm.sign σ) {()} (1 : Perm (Fin 3)) (swap 0 1) := by
  have hrot : finRotate 3 ∈ alternatingGroup (Fin 3) := by
    rw [Perm.mem_alternatingGroup, sign_finRotate]; decide
  have hswap : swap (0 : Fin 3) 1 ∉ alternatingGroup (Fin 3) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_swap (by decide)]; decide
  refine ⟨by decide, (alternatingGroup (Fin 3)).one_mem, hrot,
    relEq_sign_of_mem_alternating _ _ (alternatingGroup (Fin 3)).one_mem hrot, hswap, ?_⟩
  rw [relEq_sign_iff, inv_one, one_mul]
  exact hswap

/-- Instance for the hypothesis of `card_quotient_ker_sign`. -/
theorem card_quotient_ker_sign_fin3 :
    Nat.card (Perm (Fin 3) ⧸ (Perm.sign : Perm (Fin 3) →* ℤˣ).ker) = 2 :=
  card_quotient_ker_sign (by simp)

/-- Instance for the hypotheses of `relEq_sign_of_mul_mem_alternating`. -/
theorem relEq_sign_of_mul_mem_alternating_fin3 :
    relEq (fun σ (_ : Unit) => Perm.sign σ) {()} (1 : Perm (Fin 3)) (finRotate 3) :=
  relEq_sign_of_mul_mem_alternating _ _ (by
    rw [inv_one, one_mul, Perm.mem_alternatingGroup, sign_finRotate]; decide)

/-- Instance for the hypothesis of `fintype_card_quotient_ker_sign`. -/
theorem fintype_card_quotient_ker_sign_fin3 :
    @Fintype.card (Perm (Fin 3) ⧸ (Perm.sign : Perm (Fin 3) →* ℤˣ).ker)
      (Fintype.ofFinite _) = 2 :=
  @fintype_card_quotient_ker_sign (Fin 3) _ _ (by simp) (Fintype.ofFinite _)

end Example

end RepresentationKernelA

#print axioms RepresentationKernelA.relEq_hom_iff_eq
#print axioms RepresentationKernelA.relEq_hom_iff_mem_ker
#print axioms RepresentationKernelA.relEq_hom_iff_ker_coset
#print axioms RepresentationKernelA.injective_iff_relEq_iff_eq
#print axioms RepresentationKernelA.injective_iff_ker_eq_bot_relEq
#print axioms RepresentationKernelA.sign_ker_eq_alternatingGroup
#print axioms RepresentationKernelA.relEq_sign_iff
#print axioms RepresentationKernelA.relEq_sign_of_mul_mem_alternating
#print axioms RepresentationKernelA.relEq_sign_of_mem_alternating
#print axioms RepresentationKernelA.quotient_ker_sign_mulEquiv
#print axioms RepresentationKernelA.card_quotient_ker_sign
#print axioms RepresentationKernelA.fintype_card_quotient_ker_sign
#print axioms RepresentationKernelA.card_quotient_ker_sign_iff
#print axioms RepresentationKernelA.fin3_example
#print axioms RepresentationKernelA.card_quotient_ker_sign_fin3
#print axioms RepresentationKernelA.relEq_sign_of_mul_mem_alternating_fin3
#print axioms RepresentationKernelA.fintype_card_quotient_ker_sign_fin3
