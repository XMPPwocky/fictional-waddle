/-
# Perfect obfuscation, equivalence, and cloning

An obfuscator `O` on programs is *perfect* if it preserves what each program computes and sends
programs that compute the same function to the identical output. Real indistinguishability
obfuscation (iO) only asks that the outputs be computationally indistinguishable; the perfect
version is the limiting case.

PROVED
1. `perfectIO_decides`: a perfect obfuscator turns functional equivalence into syntactic equality:
   eval c₁ = eval c₂ ↔ O c₁ = O c₂.
2. `canonical_perfectIO`: a perfect obfuscator always exists: send each program to a chosen
   representative of its function (a canonical form). It is real, but uses choice.
3. `no_computable_perfectIO`: for programs as Turing-complete codes, no computable perfect
   obfuscator exists. With one, "c computes the same as c₀" would be decidable, and Rice's
   theorem says it is not.
4. `no_cloning`: no linear map takes every vector v ∈ ℂ² to v ⊗ v.
5. `basis_cloning`: a linear map does take each basis vector e₀, e₁ to e₀ ⊗ e₀, e₁ ⊗ e₁. Classical
   bits copy; superpositions do not.

CITED, NOT PROVED HERE
- For circuits, deciding equivalence is coNP-complete, so an efficient perfect obfuscator for circuits
  would give P = NP; conversely, if P = NP the lexicographically first equivalent circuit is
  computable efficiently and is a perfect obfuscator (folklore). Goldwasser–Rothblum (2007): iO is
  "best-possible" obfuscation.
- Jain–Lin–Sahai (2021) built iO from well-founded assumptions, including pairings that Shor's
  algorithm breaks; post-quantum iO from standard assumptions is open.
- Classical software can always be copied (item 5). Copy-protection, a program that runs but cannot
  be duplicated, needs quantum states (Aaronson 2009). That, not iO itself, is where "it has to be
  quantum" holds.
-/

import Mathlib

namespace ObfuscationNP

/-! ## 1–2. Perfect obfuscators are canonical forms -/

def PerfectIO {Prog F : Type*} (eval : Prog → F) (O : Prog → Prog) : Prop :=
  (∀ c, eval (O c) = eval c) ∧ ∀ c₁ c₂, eval c₁ = eval c₂ → O c₁ = O c₂

theorem perfectIO_decides {Prog F : Type*} (eval : Prog → F) (O : Prog → Prog)
    (hO : PerfectIO eval O) (c₁ c₂ : Prog) : eval c₁ = eval c₂ ↔ O c₁ = O c₂ := by
  constructor
  · exact hO.2 c₁ c₂
  · intro h
    rw [← hO.1 c₁, h, hO.1 c₂]

/-- A chosen program computing `f`. -/
noncomputable def canon {Prog F : Type*} (eval : Prog → F) (f : F) (h : ∃ c, eval c = f) : Prog :=
  Classical.choose h

theorem canonical_perfectIO {Prog F : Type*} (eval : Prog → F) :
    ∃ O : Prog → Prog, PerfectIO eval O := by
  refine ⟨fun c => canon eval (eval c) ⟨c, rfl⟩, ?_, ?_⟩
  · intro c
    exact Classical.choose_spec (⟨c, rfl⟩ : ∃ c', eval c' = eval c)
  · intro c₁ c₂ h
    have key : ∀ (f g : F) (hf : ∃ c, eval c = f) (hg : ∃ c, eval c = g), f = g →
        canon eval f hf = canon eval g hg := by
      rintro f _ hf hg rfl
      rfl
    exact key _ _ _ _ h

/-! ## 3. No computable perfect obfuscator for Turing-complete programs -/

open Nat.Partrec in
theorem faithfulness_undecidable (f : ℕ →. ℕ) (hf : Nat.Partrec f) :
    ¬ ComputablePred (fun c : Code => Code.eval c = f) := by
  intro h
  have h' : ComputablePred (fun c : Code => Code.eval c ∈ ({f} : Set (ℕ →. ℕ))) := by
    simpa [Set.mem_singleton_iff] using h
  have h0 : (pure 0 : ℕ →. ℕ) ∈ ({f} : Set (ℕ →. ℕ)) :=
    ComputablePred.rice {f} h' hf Nat.Partrec.zero rfl
  have h1 : (fun _ => Part.none : ℕ →. ℕ) ∈ ({f} : Set (ℕ →. ℕ)) :=
    ComputablePred.rice {f} h' hf Nat.Partrec.none rfl
  have h1' : (fun _ => Part.none : ℕ →. ℕ) = f := h1
  have h0' : (pure 0 : ℕ →. ℕ) = f := h0
  have e := congrFun (h0'.trans h1'.symm) 0
  have hm : (0 : ℕ) ∈ (pure 0 : ℕ →. ℕ) 0 := Part.mem_some 0
  rw [e] at hm
  exact Part.notMem_none 0 hm

open Nat.Partrec in
theorem no_computable_perfectIO :
    ¬ ∃ O : Code → Code, Computable O ∧ PerfectIO Code.eval O := by
  rintro ⟨O, hcomp, hO⟩
  classical
  set c₀ : Code := Code.zero
  have hf : Nat.Partrec (Code.eval c₀) := Code.exists_code.mpr ⟨c₀, rfl⟩
  apply faithfulness_undecidable (Code.eval c₀) hf
  have hfun : (fun c : Code => Code.eval c = Code.eval c₀) = fun c => O c = O c₀ :=
    funext fun c => propext (perfectIO_decides Code.eval O hO c c₀)
  rw [hfun]
  refine ⟨inferInstance, ?_⟩
  have hp := (Primrec.eq (α := Code)).decide.to_comp
  convert hp.comp hcomp (Computable.const (O c₀)) using 1

/-! ## 4–5. Bits copy; amplitudes do not -/

/-- `U` copies every vector in `S`: U v = v ⊗ v. -/
def IsCloner (U : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 × Fin 2 → ℂ)) (S : Set (Fin 2 → ℂ)) : Prop :=
  ∀ v ∈ S, U v = fun p => v p.1 * v p.2

theorem no_cloning : ¬ ∃ U, IsCloner U Set.univ := by
  rintro ⟨U, hU⟩
  set e₀ : Fin 2 → ℂ := Pi.single 0 1
  set e₁ : Fin 2 → ℂ := Pi.single 1 1
  have h := congrFun (map_add U e₀ e₁) (0, 1)
  rw [hU _ (Set.mem_univ _), Pi.add_apply, hU _ (Set.mem_univ _), hU _ (Set.mem_univ _)] at h
  simp [e₀, e₁, Pi.single_apply] at h

/-- Copy along the diagonal: v ↦ (p ↦ v p.1 if p.1 = p.2, else 0). -/
def diag : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 × Fin 2 → ℂ) where
  toFun v p := if p.1 = p.2 then v p.1 else 0
  map_add' v w := by
    funext p
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' a v := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem basis_cloning : IsCloner diag {Pi.single 0 1, Pi.single 1 1} := by
  intro v hv
  rcases hv with rfl | rfl <;>
  · funext p
    rcases p with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp [diag]

end ObfuscationNP

#print axioms ObfuscationNP.perfectIO_decides
#print axioms ObfuscationNP.canonical_perfectIO
#print axioms ObfuscationNP.no_computable_perfectIO
#print axioms ObfuscationNP.no_cloning
#print axioms ObfuscationNP.basis_cloning
