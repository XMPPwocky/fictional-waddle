import Mathlib.Computability.PartrecCode
import Mathlib.Computability.RE

/-!
# F5: Quines — patterns that generate themselves

Kleene's recursion theorem (Mathlib: `Nat.Partrec.Code.fixed_point`, Rogers' form, and
`Nat.Partrec.Code.fixed_point₂`, Kleene's second recursion theorem) applied to
self-reproducing programs.

Encoding used throughout: `Encodable.encode : Code → ℕ` (Mathlib proves
`Nat.Partrec.Code.encodeCode_eq : encode = encodeCode`, so this *is* Mathlib's
`encodeCode`; we keep `encode` because that is what `fixed_point` is phrased in).

## What is PROVED (machine-checked, no sorry)
* `rogers_fixed_point` / `kleene_second_recursion` : restatements of Mathlib's theorems.
* `quine_exists` : ∃ c, ∀ n, eval c n = some (encode c).
* `quine_trivial_zero` : CAVEAT — the code `zero` already satisfies `quine_exists`'s
  property, because `encode zero = 0`. So `quine_exists` alone is *not* evidence of
  any self-reference; it is witnessed by an accident of the numbering.
* `self_compute` : for ANY computable `g : Code → ℕ` there is a code that outputs
  `g` of its own source on every input (the honest, non-degenerate content of (1)).
* `quine_family` : for every payload `m` there is a quine carrying `m`
  (output `Nat.pair (encode c) m`), and different payloads force different codes:
  infinitely many genuinely distinct quines, none equal to `zero` once `m ≠ 0`.
* `self_replicator` : ∃ c, ∀ n, eval c n = some (Nat.pair (encode c) n) — the code
  emits its own source paired with its input; `self_replicator_ne_zero` shows this
  one is not the degenerate `zero`.
* `quine_undecidable` (added by the second, adversarial agent) : "is `c` a quine?" is
  NOT a computable predicate on codes. Proof: diagonalise through `self_compute` with
  `g c = if quine? c then encode c + 1 else encode c`. This is the formal shadow of
  Cohen's theorem that perfect virus detection is impossible. Rice's theorem does
  not apply directly, because being a quine is not extensional (it depends on
  `c`, not only on `eval c`).
* `example`s at the end: the concrete code `zero` evaluated at `42`, and a quine in the
  EXACT form of (1) that is not `zero`, derived from `quine_undecidable`. If `zero`
  were the only quine, "is a quine" would reduce to `encode c = 0`, which is decidable.
  This closes the vacuity gap in `quine_exists` for the requested statement itself.

## What is INTERPRETED (prose only, not formalised)
"Patterns that generate themselves" (viruses, memes, replicators) is a reading of these
theorems, not a theorem: nothing here models copying errors, resources, or selection.
What the math does say: in any acceptable programming system, self-reference is *free* —
for every computable "what to do with my own description" `g`, a program doing it exists.
So the existence of replicators is never the surprising part; which ones persist
(selection) is a separate question these theorems do not touch.
`quine_undecidable` is read as "no computable immune system recognises exactly the
self-reproducers". That reading is interpretation. The theorem is only about the
exact predicate `∀ n, eval c n = some (encode c)`. It says nothing about approximate
detectors, and nothing about other replicator notions such as `self_replicator`.

## Change log (second agent)
* Added `import Mathlib.Computability.RE` (for `ComputablePred`), the theorem
  `quine_undecidable`, and two `example`s. All 8 original statements are unchanged.
-/

namespace F5Quines

open Nat.Partrec Nat.Partrec.Code Encodable

/-- (2a) **Rogers' fixed-point theorem**, as in Mathlib: every computable total
transformation of codes has a semantic fixed point. -/
theorem rogers_fixed_point {f : Code → Code} (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c :=
  Code.fixed_point hf

/-- (2b) **Kleene's second recursion theorem**, as in Mathlib: for every partial recursive
`f : Code → ℕ →. ℕ` there is a code `c` that computes `f c`, i.e. "runs with access to
its own source". -/
theorem kleene_second_recursion {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) :
    ∃ c : Code, eval c = f c :=
  Code.fixed_point₂ hf

/-- Generalised self-computation (non-degenerate core of (1)): for every computable
`g : Code → ℕ` there is a code that, on every input, outputs `g` of its own source. -/
theorem self_compute {g : Code → ℕ} (hg : Computable g) :
    ∃ c : Code, ∀ n, eval c n = Part.some (g c) := by
  obtain ⟨c, hc⟩ := Code.fixed_point ((Primrec.to_comp primrec_const).comp hg)
  exact ⟨c, fun n => by rw [← hc]; exact eval_const (g c) n⟩

/-- (1) **A quine**: a code whose evaluation on every input is its own encoding. -/
theorem quine_exists :
    ∃ c : Code, ∀ n, eval c n = Part.some (encode c) :=
  self_compute (Primrec.to_comp Primrec.encode)

/-- Caveat on (1): the statement of `quine_exists` is satisfied trivially by `Code.zero`,
since `encode zero = 0` and `zero` outputs `0`. No recursion theorem is needed for it. -/
theorem quine_trivial_zero : ∀ n, eval Code.zero n = Part.some (encode Code.zero) := by
  intro n
  simp [encodeCode_eq, encodeCode]
  rfl

/-- Quines carrying a payload: for each `m`, a code outputting `⟨own source, m⟩`. Distinct
payloads give distinct codes, so there are infinitely many quines, and for `m ≠ 0` the
quine is not the degenerate `zero`. -/
theorem quine_family :
    (∀ m : ℕ, ∃ c : Code, ∀ n, eval c n = Part.some (Nat.pair (encode c) m)) ∧
    (∀ (m m' : ℕ) (c c' : Code),
        (∀ n, eval c n = Part.some (Nat.pair (encode c) m)) →
        (∀ n, eval c' n = Part.some (Nat.pair (encode c') m')) →
        c = c' → m = m') ∧
    (∀ (m : ℕ) (c : Code), m ≠ 0 →
        (∀ n, eval c n = Part.some (Nat.pair (encode c) m)) → c ≠ Code.zero) := by
  refine ⟨fun m => ?_, fun m m' c c' hc hc' hcc => ?_, fun m c hm hc hz => ?_⟩
  · exact self_compute
      ((Primrec₂.natPair.comp Primrec.encode (Primrec.const m)).to_comp)
  · subst hcc
    have h := (hc 0).symm.trans (hc' 0)
    have h2 := congrArg Nat.unpair (Part.some_injective h)
    simp only [Nat.unpair_pair, Prod.mk.injEq] at h2
    exact h2.2
  · subst hz
    have h := (quine_trivial_zero 0).symm.trans (hc 0)
    have h2 := Part.some_injective h
    have h3 := congrArg (fun k => (Nat.unpair k).2) h2
    simp only [Nat.unpair_pair] at h3
    have : (Nat.unpair (encode Code.zero)).2 = 0 := by
      simp [encodeCode_eq, encodeCode]
    exact hm (h3 ▸ this)

/-- (3) **A self-replicator**: a code that, on input `n`, outputs its own source paired
with `n` (it "copies itself and passes the environment through"). -/
theorem self_replicator :
    ∃ c : Code, ∀ n, eval c n = Part.some (Nat.pair (encode c) n) := by
  have hp : Primrec₂ (fun (c : Code) (n : ℕ) => Nat.pair (encode c) n) :=
    Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) Primrec.snd
  have hf : Partrec₂ (fun (c : Code) (n : ℕ) => (Part.some (Nat.pair (encode c) n) : Part ℕ)) :=
    (Primrec₂.to_comp hp).partrec₂
  obtain ⟨c, hc⟩ := Code.fixed_point₂ hf
  exact ⟨c, fun n => by rw [hc]⟩

/-- The self-replicator is not the degenerate `zero` code. -/
theorem self_replicator_ne_zero (c : Code)
    (hc : ∀ n, eval c n = Part.some (Nat.pair (encode c) n)) : c ≠ Code.zero := by
  rintro rfl
  have h := Part.some_injective ((quine_trivial_zero 1).symm.trans (hc 1))
  have h3 := congrArg (fun k => (Nat.unpair k).2) h
  simp only [Nat.unpair_pair] at h3
  have : (Nat.unpair (encode Code.zero)).2 = 0 := by
    simp [encodeCode_eq, encodeCode]
  omega

/-- **Quine-hood is undecidable** (added theorem, going *up*). No computable predicate on codes
holds exactly for the quines of (1). Diagonal argument: if `d` decided quine-hood, apply
`self_compute` to `g c = cond (d c) (encode c + 1) (encode c)`. The resulting `c` is a
quine iff it is not. Mathlib used: `ComputablePred`, `Computable.cond`, `Computable.succ`,
`Computable.encode`, `decide_eq_true`, `decide_eq_false`, `Part.some_injective`. -/
theorem quine_undecidable :
    ¬ ComputablePred (fun c : Code => ∀ n, eval c n = Part.some (encode c)) := by
  rintro ⟨hdec, hcomp⟩
  have hg : Computable (fun c : Code =>
      cond (decide (∀ n, eval c n = Part.some (encode c))) (encode c + 1) (encode c)) :=
    Computable.cond hcomp (Computable.succ.comp Computable.encode) Computable.encode
  obtain ⟨c, hc⟩ := self_compute hg
  by_cases hq : ∀ n, eval c n = Part.some (encode c)
  · have h := (hq 0).symm.trans (hc 0)
    have hd : decide (∀ n, eval c n = Part.some (encode c)) = true := decide_eq_true hq
    rw [hd, Bool.cond_true] at h
    have := Part.some_injective h
    omega
  · apply hq
    intro n
    have hd : decide (∀ n, eval c n = Part.some (encode c)) = false := decide_eq_false hq
    rw [hc n, hd, Bool.cond_false]

/-- Concrete example: the code `zero` run on input `42` outputs its own encoding, `0`. -/
example : eval Code.zero 42 = Part.some (encode Code.zero) := by
  simp [encodeCode_eq, encodeCode]; rfl

/-- Non-vacuity of (1) in its EXACT form: some quine in the sense of `quine_exists` is not
`zero`. If every quine were `zero`, quine-hood would be `encode c = 0`, which is
decidable, and that contradicts `quine_undecidable`. The proof is classical: it names no
specific witness. -/
example : ∃ c : Code, c ≠ Code.zero ∧ ∀ n, eval c n = Part.some (encode c) := by
  by_contra hne
  apply quine_undecidable
  have hiff : (fun c : Code => ∀ n, eval c n = Part.some (encode c)) =
      (fun c : Code => encode c = 0) := by
    funext c
    apply propext
    constructor
    · intro hq
      by_contra h0
      exact hne ⟨c, fun hz => h0 (by rw [hz]; simp [encodeCode_eq, encodeCode]), hq⟩
    · intro h0
      have : c = Code.zero := encode_injective (by rw [h0]; simp [encodeCode_eq, encodeCode])
      subst this
      exact quine_trivial_zero
  rw [hiff]
  obtain ⟨_, hp⟩ := PrimrecRel.comp (Primrec.eq (α := ℕ)) (Primrec.encode (α := Code))
    (Primrec.const (0 : ℕ))
  exact ⟨_, hp.to_comp⟩

end F5Quines
