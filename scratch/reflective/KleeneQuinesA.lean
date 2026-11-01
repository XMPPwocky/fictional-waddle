import Mathlib

/-!
# Kleene recursion theorems, quines, and mutual (two-machine) fixed points

Setting: Mathlib's `Nat.Partrec.Code` with semantics `Nat.Partrec.Code.eval`.

PROVED
* `kleene_second` : for every computable `f : Code → Code` there is `c` with
  `eval (f c) = eval c` (this is Mathlib's `Nat.Partrec.Code.fixed_point`, restated).
* `kleene_second_param` : for every `Partrec₂ g : Code → ℕ →. ℕ` there is `c` with
  `eval c = g c` (Mathlib's `Nat.Partrec.Code.fixed_point₂`, restated).
* `quine_exists` : there is a code `c` with `eval c = fun _ => Part.some (encode c)`:
  the program ignores its input and outputs its own code number.
* `mutual_fixed_point₂` : for `Partrec₂ g₁ g₂ : Code × Code → ℕ →. ℕ` there are codes
  `c₁ ≠ c₂` with `eval c₁ = g₁ (c₁, c₂)` and `eval c₂ = g₂ (c₁, c₂)`.
* `mutual_fixed_point` : for `Computable₂ f₁ f₂ : Code → Code → Code` there are codes
  `c₁ ≠ c₂` with `eval (f₁ c₁ c₂) = eval c₁` and `eval (f₂ c₁ c₂) = eval c₂`.
* `mutual_quine` : there are codes `c₁ ≠ c₂` such that `c₁` outputs `encode c₂` and
  `c₂` outputs `encode c₁` on every input.

Mathlib provides only the one-code theorems `fixed_point` and `fixed_point₂`; it has no
two-code version. The two-code versions here are derived from `fixed_point₂` by packing
both programs into one code `c`, with `c₁ = curry c 0` and `c₂ = curry c 1`, and
dispatching on the first component of the paired input.

INTERPRETED
* "Each machine reads both kernels" is modelled by `g₁ g₂` (or `f₁ f₂`) receiving the pair
  of codes `(c₁, c₂)`; "the machine behaves as prescribed" is equality of `eval`.
* The quine "returns its own code" means it outputs the natural number `encode c`.

Mathlib names used: `Nat.Partrec.Code.fixed_point`, `Nat.Partrec.Code.fixed_point₂`,
`Nat.Partrec.Code.eval_part`, `Nat.Partrec.Code.exists_code`,
`Nat.Partrec.Code.primrec₂_curry`, `Nat.Partrec.Code.eval_curry`,
`Nat.Partrec.Code.curry_inj`.
-/

namespace KleeneQuinesA

open Nat.Partrec Nat.Partrec.Code Encodable Computable

/-- Kleene's second recursion theorem (Rogers form), as in Mathlib. -/
theorem kleene_second {f : Code → Code} (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c :=
  Code.fixed_point hf

/-- Kleene's second recursion theorem, parametric form, as in Mathlib. -/
theorem kleene_second_param {g : Code → ℕ →. ℕ} (hg : Partrec₂ g) :
    ∃ c : Code, eval c = g c :=
  Code.fixed_point₂ hg

/-- A quine: a code that ignores its input and outputs its own code number. -/
theorem quine_exists : ∃ c : Code, eval c = fun _ => Part.some (encode c) := by
  have h : Partrec₂ (fun (c : Code) (_ : ℕ) => (Part.some (encode c) : Part ℕ)) :=
    ((Computable.encode.comp Computable.fst).partrec).to₂
  exact Code.fixed_point₂ h

/-- Two-code Kleene recursion theorem, partial-function form. -/
theorem mutual_fixed_point₂ {g₁ g₂ : Code × Code → ℕ →. ℕ}
    (hg₁ : Partrec₂ g₁) (hg₂ : Partrec₂ g₂) :
    ∃ c₁ c₂ : Code, c₁ ≠ c₂ ∧ eval c₁ = g₁ (c₁, c₂) ∧ eval c₂ = g₂ (c₁, c₂) := by
  obtain ⟨e₁, he₁⟩ := Code.exists_code.1 hg₁
  obtain ⟨e₂, he₂⟩ := Code.exists_code.1 hg₂
  have r₁ : ∀ p x, eval (curry e₁ (encode p)) x = g₁ p x := by
    rintro ⟨a, b⟩ x
    simp [he₁, Part.map_id', Encodable.encode_prod_val, Denumerable.ofNat_encode]
  have r₂ : ∀ p x, eval (curry e₂ (encode p)) x = g₂ p x := by
    rintro ⟨a, b⟩ x
    simp [he₂, Part.map_id', Encodable.encode_prod_val, Denumerable.ofNat_encode]
  let P : Code → Code × Code := fun c => (curry c 0, curry c 1)
  have hP : Computable P :=
    ((primrec₂_curry.comp Primrec.id (Primrec.const 0)).pair
      (primrec₂_curry.comp Primrec.id (Primrec.const 1))).to_comp
  let H : Code → ℕ → Code := fun c n =>
    bif (Nat.unpair n).1 == 0 then curry e₁ (encode (P c)) else curry e₂ (encode (P c))
  have hH : Computable₂ H := by
    have hb : Computable (fun q : Code × ℕ => (Nat.unpair q.2).1 == 0) :=
      (Primrec.beq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
        (Primrec.const 0)).to_comp
    have k₁ : Computable (fun q : Code × ℕ => curry e₁ (encode (P q.1))) :=
      (primrec₂_curry.to_comp.comp (Computable.const e₁)
        (Computable.encode.comp (hP.comp Computable.fst)))
    have k₂ : Computable (fun q : Code × ℕ => curry e₂ (encode (P q.1))) :=
      (primrec₂_curry.to_comp.comp (Computable.const e₂)
        (Computable.encode.comp (hP.comp Computable.fst)))
    exact (Computable.cond hb k₁ k₂).to₂
  let G : Code → ℕ →. ℕ := fun c n => eval (H c n) (Nat.unpair n).2
  have hG : Partrec₂ G :=
    (eval_part.comp hH (Computable.snd.comp (Primrec.unpair.to_comp.comp Computable.snd))).to₂
  obtain ⟨c, hc⟩ := Code.fixed_point₂ hG
  refine ⟨curry c 0, curry c 1, ?_, ?_, ?_⟩
  · intro h
    have := (curry_inj h).2
    exact absurd this (by decide)
  · funext x
    rw [eval_curry, hc]
    simp only [G, H, Nat.unpair_pair]
    simpa [P] using r₁ (P c) x
  · funext x
    rw [eval_curry, hc]
    simp only [G, H, Nat.unpair_pair]
    simpa [P] using r₂ (P c) x

/-- Two-code Rogers fixed-point theorem: two computable code transformers, each reading
both codes, have a simultaneous pair of semantic fixed points. -/
theorem mutual_fixed_point {f₁ f₂ : Code → Code → Code}
    (hf₁ : Computable₂ f₁) (hf₂ : Computable₂ f₂) :
    ∃ c₁ c₂ : Code, c₁ ≠ c₂ ∧ eval (f₁ c₁ c₂) = eval c₁ ∧ eval (f₂ c₁ c₂) = eval c₂ := by
  have h₁ : Partrec₂ (fun (p : Code × Code) (n : ℕ) => eval (f₁ p.1 p.2) n) :=
    (eval_part.comp (hf₁.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp Computable.fst)) Computable.snd).to₂
  have h₂ : Partrec₂ (fun (p : Code × Code) (n : ℕ) => eval (f₂ p.1 p.2) n) :=
    (eval_part.comp (hf₂.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp Computable.fst)) Computable.snd).to₂
  obtain ⟨c₁, c₂, hne, e₁, e₂⟩ := mutual_fixed_point₂ h₁ h₂
  exact ⟨c₁, c₂, hne, by rw [e₁], by rw [e₂]⟩

/-- Mutual quines: each code outputs the other's code number on every input. -/
theorem mutual_quine :
    ∃ c₁ c₂ : Code, c₁ ≠ c₂ ∧ eval c₁ = (fun _ => Part.some (encode c₂)) ∧
      eval c₂ = (fun _ => Part.some (encode c₁)) := by
  have h₁ : Partrec₂ (fun (p : Code × Code) (_ : ℕ) => (Part.some (encode p.2) : Part ℕ)) :=
    ((Computable.encode.comp (Computable.snd.comp Computable.fst)).partrec).to₂
  have h₂ : Partrec₂ (fun (p : Code × Code) (_ : ℕ) => (Part.some (encode p.1) : Part ℕ)) :=
    ((Computable.encode.comp (Computable.fst.comp Computable.fst)).partrec).to₂
  exact mutual_fixed_point₂ h₁ h₂

end KleeneQuinesA
