import Mathlib

/-!
# Representation kernels: what a homomorphism cannot distinguish

Setup. A "thing" is observed only through a response function `resp : Thing → Probe → R`
evaluated on a set of probes `P`. Two things are `relEq` when every probe in `P` gives the
same response. For a group homomorphism `rho : G →* H` we use the single probe `()` and the
response `fun g _ => rho g`.

## PROVED

* `relEq_hom_iff_mem_ker`: for every group homomorphism `rho : G →* H` and all `g g' : G`,
  `relEq (fun g _ => rho g) {()} g g' ↔ g⁻¹ * g' ∈ rho.ker`.
* `relEq_hom_iff_eq_div`: the same relation holds iff `g` and `g'` have the same image in
  `G ⧸ rho.ker` (left cosets of the kernel).
* `injective_iff_relEq_iff_eq`: `Function.Injective rho ↔ ∀ g g', (relEq ... g g' ↔ g = g')`.
* `ker_eq_bot_iff_relEq_iff_eq`: the same with `rho.ker = ⊥` on the left.
* `sign_ker_eq_alternatingGroup`: `(Equiv.Perm.sign : Perm α →* ℤˣ).ker = alternatingGroup α`
  for `[Fintype α] [DecidableEq α]`.
* `relEq_sign_iff`: `relEq (fun s _ => sign s) {()} σ τ ↔ σ⁻¹ * τ ∈ alternatingGroup α`.
* `relEq_sign_of_mem_alternating`: any two members of `alternatingGroup α` are `relEq` for sign.
* `relEq_sign_iff_mul_inv`: `relEq ... σ τ ↔ τ * σ⁻¹ ∈ alternatingGroup α` (right-coset form).
* `card_quot_sign_ker`: if `2 ≤ Fintype.card α` then `Nat.card (Perm α ⧸ sign.ker) = 2`.
* `card_quot_sign_ker_iff`: `Nat.card (Perm α ⧸ sign.ker) = 2 ↔ 2 ≤ Fintype.card α`.
* `card_quot_sign_ker_of_le_one`: if `Fintype.card α ≤ 1` then the quotient has `Nat.card` 1.
* `fin3_nonvacuous`: on `Fin 3`, with `c = finRotate 3` and `t = swap 0 1`:
  `1 ≠ c`, `1 ∈ alternatingGroup`, `c ∈ alternatingGroup`, `relEq ... 1 c`,
  `t ∉ alternatingGroup`, `¬ relEq ... 1 t`, `¬ relEq ... c t`.
* `faithful_instance`: `MonoidHom.id` on `Multiplicative ℤ` satisfies the right side of
  `injective_iff_relEq_iff_eq`; `sign_not_faithful_fin3`: sign on `Fin 3` does not.
* `card_hyp_instance`: `2 ≤ Fintype.card (Fin 3)` (instance for the hypothesis of
  `card_quot_sign_ker`); `card_le_one_instance`: `Fintype.card (Fin 1) ≤ 1`.

## CITED / INTERPRETED (not proved here)

* Reading: an observer that accesses a group only through a representation `rho` cannot
  separate elements differing by a kernel element; the observable content is `G ⧸ ker rho`
  (first isomorphism theorem, used here via `QuotientGroup.quotientKerEquivOfSurjective`).
* Reading: the sign representation carries exactly one bit about a permutation (its parity)
  when the underlying type has at least two elements.
-/

namespace RepresentationKernelB

/-- a and b are the same relative to the probes P. -/
def relEq {Thing Probe R : Type*} (resp : Thing -> Probe -> R) (P : Set Probe) (a b : Thing) : Prop := ∀ p ∈ P, resp a p = resp b p

/-- With the single probe `()`, `relEq` is equality of the responses at `()`. -/
theorem relEq_unit_iff {Thing R : Type*} (f : Thing → R) (a b : Thing) :
    relEq (fun x (_ : Unit) => f x) {()} a b ↔ f a = f b := by
  constructor
  · intro h; exact h () rfl
  · intro h p _; exact h

section Hom

variable {G H : Type*} [Group G] [Group H]

/-- 1. What `rho` cannot feel is exactly its kernel. -/
theorem relEq_hom_iff_mem_ker (rho : G →* H) (g g' : G) :
    relEq (fun x (_ : Unit) => rho x) {()} g g' ↔ g⁻¹ * g' ∈ rho.ker := by
  rw [relEq_unit_iff, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]

/-- Equivalent coset form: same image in `G ⧸ rho.ker`. -/
theorem relEq_hom_iff_eq_div (rho : G →* H) (g g' : G) :
    relEq (fun x (_ : Unit) => rho x) {()} g g' ↔
      (g : G ⧸ rho.ker) = (g' : G ⧸ rho.ker) := by
  rw [relEq_hom_iff_mem_ker, QuotientGroup.eq]

/-- 2. `rho` is faithful iff `relEq` is equality. -/
theorem injective_iff_relEq_iff_eq (rho : G →* H) :
    Function.Injective rho ↔
      ∀ g g' : G, (relEq (fun x (_ : Unit) => rho x) {()} g g' ↔ g = g') := by
  constructor
  · intro hinj g g'
    rw [relEq_unit_iff]
    exact ⟨fun h => hinj h, fun h => h ▸ rfl⟩
  · intro h g g' hg
    exact (h g g').1 ((relEq_unit_iff _ _ _).2 hg)

/-- 2'. Same, with trivial kernel on the left. -/
theorem ker_eq_bot_iff_relEq_iff_eq (rho : G →* H) :
    rho.ker = ⊥ ↔
      ∀ g g' : G, (relEq (fun x (_ : Unit) => rho x) {()} g g' ↔ g = g') := by
  rw [MonoidHom.ker_eq_bot_iff, injective_iff_relEq_iff_eq]

end Hom

section Sign

open Equiv

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- 3a. The kernel of sign is the alternating group. -/
theorem sign_ker_eq_alternatingGroup :
    (Perm.sign : Perm α →* ℤˣ).ker = alternatingGroup α :=
  (alternatingGroup_eq_sign_ker).symm

/-- 3b. `σ` and `τ` feel the same to sign iff `σ⁻¹ * τ` is even. -/
theorem relEq_sign_iff (σ τ : Perm α) :
    relEq (fun s (_ : Unit) => Perm.sign s) {()} σ τ ↔ σ⁻¹ * τ ∈ alternatingGroup α := by
  rw [← sign_ker_eq_alternatingGroup]
  exact relEq_hom_iff_mem_ker Perm.sign σ τ

/-- 3b'. Right-coset form. -/
theorem relEq_sign_iff_mul_inv (σ τ : Perm α) :
    relEq (fun s (_ : Unit) => Perm.sign s) {()} σ τ ↔ τ * σ⁻¹ ∈ alternatingGroup α := by
  rw [relEq_unit_iff, Perm.mem_alternatingGroup, map_mul, map_inv,
    mul_inv_eq_one, eq_comm]

/-- 3c. All members of the alternating group feel identical to sign. -/
theorem relEq_sign_of_mem_alternating {σ τ : Perm α}
    (hσ : σ ∈ alternatingGroup α) (hτ : τ ∈ alternatingGroup α) :
    relEq (fun s (_ : Unit) => Perm.sign s) {()} σ τ := by
  rw [relEq_sign_iff]
  exact (alternatingGroup α).mul_mem ((alternatingGroup α).inv_mem hσ) hτ

/-- 4. For at least two points, the sign representation feels exactly one bit. -/
theorem card_quot_sign_ker (h : 2 ≤ Fintype.card α) :
    Nat.card (Perm α ⧸ (Perm.sign : Perm α →* ℤˣ).ker) = 2 := by
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.1 h
  rw [Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective _ (Perm.sign_surjective α)).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- 4'. With at most one point, the quotient is a single element. -/
theorem card_quot_sign_ker_of_le_one (h : Fintype.card α ≤ 1) :
    Nat.card (Perm α ⧸ (Perm.sign : Perm α →* ℤˣ).ker) = 1 := by
  have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.1 h
  have : Subsingleton (Perm α) := inferInstance
  have : Subsingleton (Perm α ⧸ (Perm.sign : Perm α →* ℤˣ).ker) := by
    refine ⟨fun x y => ?_⟩
    induction x using QuotientGroup.induction_on
    induction y using QuotientGroup.induction_on
    exact congrArg _ (Subsingleton.elim _ _)
  exact Nat.card_unique

/-- 4''. The quotient has exactly two elements iff `α` has at least two points. -/
theorem card_quot_sign_ker_iff :
    Nat.card (Perm α ⧸ (Perm.sign : Perm α →* ℤˣ).ker) = 2 ↔ 2 ≤ Fintype.card α := by
  constructor
  · intro h
    by_contra hlt
    rw [card_quot_sign_ker_of_le_one (by omega)] at h
    omega
  · exact card_quot_sign_ker

end Sign

section Instances

open Equiv

/-- 5. Non-vacuity on `Fin 3`: the identity and the 3-cycle `finRotate 3` are distinct, both
even, and feel identical to sign; the transposition `swap 0 1` is odd and feels different from
both. -/
theorem fin3_nonvacuous :
    (1 : Perm (Fin 3)) ≠ finRotate 3 ∧
    (1 : Perm (Fin 3)) ∈ alternatingGroup (Fin 3) ∧
    finRotate 3 ∈ alternatingGroup (Fin 3) ∧
    relEq (fun s (_ : Unit) => Perm.sign s) {()} (1 : Perm (Fin 3)) (finRotate 3) ∧
    swap (0 : Fin 3) 1 ∉ alternatingGroup (Fin 3) ∧
    ¬ relEq (fun s (_ : Unit) => Perm.sign s) {()} (1 : Perm (Fin 3)) (swap 0 1) ∧
    ¬ relEq (fun s (_ : Unit) => Perm.sign s) {()} (finRotate 3) (swap (0 : Fin 3) 1) := by
  have hc : Perm.sign (finRotate 3) = 1 := by
    rw [sign_finRotate]; decide
  have ht : Perm.sign (swap (0 : Fin 3) 1) = -1 := Perm.sign_swap (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun f : Perm (Fin 3) => f 0) h
    simp at this
  · exact (alternatingGroup (Fin 3)).one_mem
  · exact Perm.mem_alternatingGroup.2 hc
  · rw [relEq_unit_iff, hc, Perm.sign_one]
  · rw [Perm.mem_alternatingGroup, ht]; decide
  · rw [relEq_unit_iff, ht, Perm.sign_one]; decide
  · rw [relEq_unit_iff, ht, hc]; decide

/-- Instance: a faithful homomorphism satisfying the right side of
`injective_iff_relEq_iff_eq`. -/
theorem faithful_instance :
    ∀ g g' : Multiplicative ℤ,
      (relEq (fun x (_ : Unit) => (MonoidHom.id (Multiplicative ℤ)) x) {()} g g' ↔ g = g') :=
  (injective_iff_relEq_iff_eq _).1 (fun _ _ h => h)

/-- Instance: sign on `Fin 3` is not faithful. -/
theorem sign_not_faithful_fin3 :
    ¬ Function.Injective (Perm.sign : Perm (Fin 3) →* ℤˣ) := by
  intro hinj
  obtain ⟨hne, -, -, hrel, -⟩ := fin3_nonvacuous
  exact hne (((injective_iff_relEq_iff_eq Perm.sign).1 hinj _ _).1 hrel)

/-- Instance for the hypothesis of `card_quot_sign_ker`. -/
theorem card_hyp_instance : 2 ≤ Fintype.card (Fin 3) := by simp

/-- Instance for the hypothesis of `card_quot_sign_ker_of_le_one`. -/
theorem card_le_one_instance : Fintype.card (Fin 1) ≤ 1 := by simp

/-- The conclusion of `card_quot_sign_ker` at the instance `Fin 3`. -/
theorem card_quot_sign_ker_fin3 :
    Nat.card (Perm (Fin 3) ⧸ (Perm.sign : Perm (Fin 3) →* ℤˣ).ker) = 2 :=
  card_quot_sign_ker card_hyp_instance

end Instances

end RepresentationKernelB

#print axioms RepresentationKernelB.relEq_unit_iff
#print axioms RepresentationKernelB.relEq_hom_iff_mem_ker
#print axioms RepresentationKernelB.relEq_hom_iff_eq_div
#print axioms RepresentationKernelB.injective_iff_relEq_iff_eq
#print axioms RepresentationKernelB.ker_eq_bot_iff_relEq_iff_eq
#print axioms RepresentationKernelB.sign_ker_eq_alternatingGroup
#print axioms RepresentationKernelB.relEq_sign_iff
#print axioms RepresentationKernelB.relEq_sign_iff_mul_inv
#print axioms RepresentationKernelB.relEq_sign_of_mem_alternating
#print axioms RepresentationKernelB.card_quot_sign_ker
#print axioms RepresentationKernelB.card_quot_sign_ker_of_le_one
#print axioms RepresentationKernelB.card_quot_sign_ker_iff
#print axioms RepresentationKernelB.fin3_nonvacuous
#print axioms RepresentationKernelB.faithful_instance
#print axioms RepresentationKernelB.sign_not_faithful_fin3
#print axioms RepresentationKernelB.card_hyp_instance
#print axioms RepresentationKernelB.card_le_one_instance
#print axioms RepresentationKernelB.card_quot_sign_ker_fin3
