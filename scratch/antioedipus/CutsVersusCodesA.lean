import Mathlib

/-!
# Cuts versus codes

A flow is a list `List α` or a stream `ℕ → α`. A *cut* splits a flow at a position;
a *code* applies a map `c : α → β` elementwise.

## PROVED

* `cut_lossless` : `l.take n ++ l.drop n = l`.
* `streamCut_reconstruct` : a stream is recovered from its length-`n` prefix and its
  `n`-shifted tail by `i ↦ if i < n then prefix i else tail (i - n)`.
* `streamCut_injective` : `s ↦ (fun i : Fin n => s i, fun i => s (i + n))` is injective.
* `twoCuts_lossless` : `l.take n ++ (l.drop n).take m ++ (l.drop n).drop m = l`.
* `cutSequence_lossless` : for any finite list of cut points applied successively to the
  remaining tail, concatenating the pieces recovers the list.
* `code_lossy_list` : if `c` is not injective then `List.map c` is not injective; in fact
  it is already not injective on lists of length 1 (`code_lossy_singleton`).
* `code_lossy_stream` : if `c` is not injective then `fun s : ℕ → α => c ∘ s` is not
  injective.
* `not_injective_of_card_lt` : for finite `α`, `β` with `card β < card α`, no
  `c : α → β` is injective; hence (`code_lossy_of_card_lt`) `List.map c` is not injective.
* `explicit_code` : the explicit code `fun _ : Bool => ()` satisfies
  `Fintype.card Unit < Fintype.card Bool` and `List.map` of it is not injective;
  more generally `toUnit_lossy` for any `α` with `card α ≥ 2`.

## INTERPRETED

The Deleuze–Guattari reading (Anti-Oedipus): desiring-machines operate by cuts on flows,
whereas the social machine codes flows. The theorems above say that, in this toy model,
cutting (including any finite sequence of cuts) is lossless, while coding through a
non-injective code, in particular any code into a strictly smaller alphabet, irreversibly
identifies distinct flows. The reading is an interpretation and is not part of any
theorem statement.
-/

namespace CutsVersusCodesA

/-! ### (1) Cuts are lossless -/

theorem cut_lossless {α : Type*} (l : List α) (n : ℕ) : l.take n ++ l.drop n = l :=
  List.take_append_drop n l

/-- The cut of a stream at `n`: its length-`n` prefix and its `n`-shifted tail. -/
def streamCut {α : Type*} (n : ℕ) (s : ℕ → α) : (Fin n → α) × (ℕ → α) :=
  (fun i : Fin n => s i, fun i => s (i + n))

/-- Gluing a prefix and a tail back into a stream. -/
def streamGlue {α : Type*} (n : ℕ) (p : (Fin n → α) × (ℕ → α)) : ℕ → α :=
  fun i => if h : i < n then p.1 ⟨i, h⟩ else p.2 (i - n)

theorem streamCut_reconstruct {α : Type*} (n : ℕ) (s : ℕ → α) :
    streamGlue n (streamCut n s) = s := by
  funext i
  unfold streamGlue streamCut
  by_cases h : i < n
  · simp [h]
  · simp only [h, dite_false]
    congr 1
    omega

theorem streamCut_injective {α : Type*} (n : ℕ) :
    Function.Injective (fun s : ℕ → α => (fun i : Fin n => s i, fun i => s (i + n))) := by
  intro s t hst
  have h := congrArg (streamGlue n) hst
  have hs := streamCut_reconstruct n s
  have ht := streamCut_reconstruct n t
  unfold streamCut at hs ht
  rw [hs, ht] at h
  exact h

/-! ### (2) Sequences of cuts are lossless -/

theorem twoCuts_lossless {α : Type*} (l : List α) (n m : ℕ) :
    l.take n ++ (l.drop n).take m ++ (l.drop n).drop m = l := by
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

/-- Cut `l` successively at the cut points `ns`, each cut applied to the remaining tail;
returns the list of pieces (the last piece is the final remainder). -/
def cuts {α : Type*} : List ℕ → List α → List (List α)
  | [], l => [l]
  | n :: ns, l => l.take n :: cuts ns (l.drop n)

theorem cutSequence_lossless {α : Type*} (ns : List ℕ) (l : List α) :
    (cuts ns l).flatten = l := by
  induction ns generalizing l with
  | nil => simp [cuts]
  | cons n ns ih => simp [cuts, ih]

/-! ### (3) Codes are lossy -/

theorem code_lossy_singleton {α β : Type*} (c : α → β) (hc : ¬ Function.Injective c) :
    ∃ a b : α, a ≠ b ∧ [a] ≠ [b] ∧ List.map c [a] = List.map c [b] := by
  simp only [Function.Injective, not_forall] at hc
  obtain ⟨a, b, hab, hne⟩ := hc
  exact ⟨a, b, hne, by simpa using hne, by simp [hab]⟩

theorem code_lossy_list {α β : Type*} (c : α → β) (hc : ¬ Function.Injective c) :
    ¬ Function.Injective (List.map c) := by
  intro hinj
  obtain ⟨a, b, _, hne, heq⟩ := code_lossy_singleton c hc
  exact hne (hinj heq)

theorem code_lossy_stream {α β : Type*} (c : α → β) (hc : ¬ Function.Injective c) :
    ¬ Function.Injective (fun s : ℕ → α => c ∘ s) := by
  intro hinj
  apply hc
  intro a b hab
  have h : (fun _ : ℕ => a) = (fun _ : ℕ => b) := hinj (by funext i; simp [hab])
  exact congrFun h 0

theorem not_injective_of_card_lt {α β : Type*} [Fintype α] [Fintype β] (c : α → β)
    (hcard : Fintype.card β < Fintype.card α) : ¬ Function.Injective c := by
  intro hinj
  have := Fintype.card_le_of_injective c hinj
  omega

theorem code_lossy_of_card_lt {α β : Type*} [Fintype α] [Fintype β] (c : α → β)
    (hcard : Fintype.card β < Fintype.card α) : ¬ Function.Injective (List.map c) :=
  code_lossy_list c (not_injective_of_card_lt c hcard)

theorem toUnit_lossy {α : Type*} [Fintype α] (h : 2 ≤ Fintype.card α) :
    ¬ Function.Injective (List.map (fun _ : α => ())) :=
  code_lossy_of_card_lt _ (by simp; omega)

theorem explicit_code :
    Fintype.card Unit < Fintype.card Bool ∧
      ¬ Function.Injective (fun _ : Bool => ()) ∧
      ¬ Function.Injective (List.map (fun _ : Bool => ())) ∧
      List.map (fun _ : Bool => ()) [true] = List.map (fun _ : Bool => ()) [false] := by
  refine ⟨by simp, ?_, ?_, by simp⟩
  · exact not_injective_of_card_lt _ (by simp)
  · exact code_lossy_of_card_lt _ (by simp)

end CutsVersusCodesA
