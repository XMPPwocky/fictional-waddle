import Mathlib

/-!
# Kleene recursion theorem, quines, and two-machine mutual fixed points

All statements are about Mathlib's `Nat.Partrec.Code` and `Nat.Partrec.Code.eval`.

PROVED
* `recursion_theorem` : for computable `f : Code → Code` there is `c` with
  `eval (f c) = eval c` (this is Mathlib's `Nat.Partrec.Code.fixed_point`, restated).
* `recursion_theorem₂` : for `g : Code → ℕ →. ℕ` with `Partrec₂ g` there is `c` with
  `eval c = g c` (Mathlib's `Nat.Partrec.Code.fixed_point₂`, restated).
* `exists_quine` : there is a code `c` with `eval c n = Part.some (encode c)` for every `n`.
* `mutual_fixed_point_code` : for `Computable₂ f₁ f₂ : Code → Code → Code` there are `c₁ c₂`
  with `eval (f₁ c₁ c₂) = eval c₁` and `eval (f₂ c₁ c₂) = eval c₂`.
* `mutual_fixed_point` : for partial recursive `g₁ g₂ : Code → Code → ℕ →. ℕ` there are
  `c₁ c₂` with `eval c₁ = g₁ c₁ c₂` and `eval c₂ = g₂ c₁ c₂`.
* `exists_mutual_quine` : there are codes `c₁ c₂` with `eval c₁ n = Part.some (encode c₂)` and
  `eval c₂ n = Part.some (encode c₁)` for every `n`.
* `exists_mutual_quine_pair` : there are codes `c₁ c₂` that both output
  `Nat.pair (encode c₁) (encode c₂)` on every input.

INTERPRETED
* "Two machines quine over their kernels": each machine `cᵢ` behaves as a partial recursive
  function `gᵢ` of both source codes `(c₁, c₂)`; `mutual_fixed_point` says such a pair of
  codes exists for any such pair of specifications. Mathlib provides only the one-machine
  theorems `fixed_point` and `fixed_point₂`; the two-machine statements are derived here by
  packing both machines into one code `c` and reading them off as `curry c 0` and `curry c 1`.
* This is the computability-theoretic (total-information) fixed point. Reflective oracles,
  which handle probabilistic queries about machines that may not halt, are not formalized.

Mathlib names used: `Nat.Partrec.Code.fixed_point`, `Nat.Partrec.Code.fixed_point₂`,
`Nat.Partrec.Code.curry`, `Nat.Partrec.Code.eval_curry`, `Nat.Partrec.Code.primrec₂_curry`,
`Nat.Partrec.Code.eval_part`, `Nat.Partrec.Code.exists_code`, `Computable.nat_casesOn`.
-/

namespace KleeneQuinesB

open Nat.Partrec Nat.Partrec.Code Encodable Computable

/-- Kleene's second recursion theorem, in Rogers' form. -/
theorem recursion_theorem {f : Code → Code} (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c :=
  Nat.Partrec.Code.fixed_point hf

/-- Kleene's second recursion theorem, parametric form. -/
theorem recursion_theorem₂ {g : Code → ℕ →. ℕ} (hg : Partrec₂ g) :
    ∃ c : Code, eval c = g c :=
  Nat.Partrec.Code.fixed_point₂ hg

/-- A quine: a code that ignores its input and outputs its own encoding. -/
theorem exists_quine : ∃ c : Code, ∀ n, eval c n = Part.some (encode c) := by
  have hg : Partrec₂ (fun (c : Code) (_ : ℕ) => (Part.some (encode c) : Part ℕ)) :=
    (Computable.encode.comp Computable.fst : Computable fun p : Code × ℕ => encode p.1).partrec
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.fixed_point₂ hg
  exact ⟨c, fun n => by rw [hc]⟩

/-- Two-machine Rogers fixed point. -/
theorem mutual_fixed_point_code {f₁ f₂ : Code → Code → Code}
    (hf₁ : Computable₂ f₁) (hf₂ : Computable₂ f₂) :
    ∃ c₁ c₂ : Code, eval (f₁ c₁ c₂) = eval c₁ ∧ eval (f₂ c₁ c₂) = eval c₂ := by
  let F : Code → ℕ → Code := fun c m =>
    Nat.casesOn (motive := fun _ => Code) (Nat.unpair m).1
      (f₁ (curry c 0) (curry c 1)) (fun _ => f₂ (curry c 0) (curry c 1))
  have hc0 : Computable fun p : Code × ℕ => curry p.1 0 :=
    (primrec₂_curry.comp _root_.Primrec.fst (_root_.Primrec.const 0)).to_comp
  have hc1 : Computable fun p : Code × ℕ => curry p.1 1 :=
    (primrec₂_curry.comp _root_.Primrec.fst (_root_.Primrec.const 1)).to_comp
  have hF : Computable₂ F := by
    have h1 : Computable fun p : Code × ℕ => f₁ (curry p.1 0) (curry p.1 1) := hf₁.comp hc0 hc1
    have h2 : Computable fun p : Code × ℕ => f₂ (curry p.1 0) (curry p.1 1) := hf₂.comp hc0 hc1
    exact Computable.nat_casesOn
      (Computable.fst.comp (Computable.unpair.comp Computable.snd)) h1 (h2.comp Computable.fst).to₂
  let g : Code → ℕ →. ℕ := fun c m => eval (F c m) (Nat.unpair m).2
  have hg : Partrec₂ g :=
    eval_part.comp hF (Computable.snd.comp (Computable.unpair.comp Computable.snd))
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.fixed_point₂ hg
  refine ⟨curry c 0, curry c 1, ?_, ?_⟩
  · funext x
    rw [eval_curry, hc]
    simp [g, F]
  · funext x
    rw [eval_curry, hc]
    simp [g, F]

/-- Two-machine Kleene recursion theorem: each machine may be any partial recursive function
of both source codes. -/
theorem mutual_fixed_point {g₁ g₂ : Code → Code → ℕ →. ℕ}
    (hg₁ : Partrec₂ fun (p : Code × Code) (n : ℕ) => g₁ p.1 p.2 n)
    (hg₂ : Partrec₂ fun (p : Code × Code) (n : ℕ) => g₂ p.1 p.2 n) :
    ∃ c₁ c₂ : Code, eval c₁ = g₁ c₁ c₂ ∧ eval c₂ = g₂ c₁ c₂ := by
  obtain ⟨e₁, he₁⟩ := exists_code.1 hg₁
  obtain ⟨e₂, he₂⟩ := exists_code.1 hg₂
  have hk : Computable₂ fun (c₁ c₂ : Code) => encode (c₁, c₂) :=
    Computable.encode.comp (Computable.pair Computable.fst Computable.snd)
  have h₁ : Computable₂ fun (c₁ c₂ : Code) => curry e₁ (encode (c₁, c₂)) :=
    (primrec₂_curry.to_comp.comp (Computable.const e₁) hk).to₂
  have h₂ : Computable₂ fun (c₁ c₂ : Code) => curry e₂ (encode (c₁, c₂)) :=
    (primrec₂_curry.to_comp.comp (Computable.const e₂) hk).to₂
  obtain ⟨c₁, c₂, k₁, k₂⟩ := mutual_fixed_point_code h₁ h₂
  refine ⟨c₁, c₂, ?_, ?_⟩
  · rw [← k₁]
    funext n
    simp [he₁, Part.map_id']
  · rw [← k₂]
    funext n
    simp [he₂, Part.map_id']

/-- Mutual quines: each machine outputs the other's code. -/
theorem exists_mutual_quine :
    ∃ c₁ c₂ : Code, ∀ n, eval c₁ n = Part.some (encode c₂) ∧
      eval c₂ n = Part.some (encode c₁) := by
  have h₁ : Partrec₂ fun (p : Code × Code) (_ : ℕ) => (Part.some (encode p.2) : Part ℕ) :=
    (Computable.encode.comp (Computable.snd.comp Computable.fst) :
      Computable fun q : (Code × Code) × ℕ => encode q.1.2).partrec
  have h₂ : Partrec₂ fun (p : Code × Code) (_ : ℕ) => (Part.some (encode p.1) : Part ℕ) :=
    (Computable.encode.comp (Computable.fst.comp Computable.fst) :
      Computable fun q : (Code × Code) × ℕ => encode q.1.1).partrec
  obtain ⟨c₁, c₂, k₁, k₂⟩ := mutual_fixed_point
    (g₁ := fun _ c₂ _ => Part.some (encode c₂)) (g₂ := fun c₁ _ _ => Part.some (encode c₁)) h₁ h₂
  exact ⟨c₁, c₂, fun n => ⟨by rw [k₁], by rw [k₂]⟩⟩

/-- Both machines output the pair of both codes. -/
theorem exists_mutual_quine_pair :
    ∃ c₁ c₂ : Code, ∀ n, eval c₁ n = Part.some (Nat.pair (encode c₁) (encode c₂)) ∧
      eval c₂ n = Part.some (Nat.pair (encode c₁) (encode c₂)) := by
  have hp : Computable fun q : (Code × Code) × ℕ => Nat.pair (encode q.1.1) (encode q.1.2) :=
    Computable₂.comp (Primrec₂.natPair.to_comp)
      (Computable.encode.comp (Computable.fst.comp Computable.fst))
      (Computable.encode.comp (Computable.snd.comp Computable.fst))
  have h : Partrec₂ fun (p : Code × Code) (_ : ℕ) =>
      (Part.some (Nat.pair (encode p.1) (encode p.2)) : Part ℕ) := hp.partrec
  obtain ⟨c₁, c₂, k₁, k₂⟩ := mutual_fixed_point
    (g₁ := fun c₁ c₂ _ => Part.some (Nat.pair (encode c₁) (encode c₂)))
    (g₂ := fun c₁ c₂ _ => Part.some (Nat.pair (encode c₁) (encode c₂))) h h
  exact ⟨c₁, c₂, fun n => ⟨by rw [k₁], by rw [k₂]⟩⟩

end KleeneQuinesB
