import Mathlib

/-!
# Cuts versus codes

A flow is a list `List α` or a stream `ℕ → α`. A *cut* splits a flow at a position;
a *code* rewrites each element through a map `c : α → β`.

## PROVED

* `list_cut_lossless` : `l.take n ++ l.drop n = l`.
* `stream_cut_reconstruct` : a stream equals the gluing of its length-`n` prefix and its
  shifted tail `fun i => s (i + n)`.
* `stream_cut_injective` : the map `s ↦ (fun i : Fin n => s i, fun i => s (i + n))` is injective.
* `list_two_cuts_lossless` : cutting at `n`, then at `m` inside the tail, and concatenating the
  three pieces recovers the list.
* `stream_two_cuts_injective` : the analogous three-piece cut of a stream is injective.
* `map_injective_iff` : `List.map c` is injective iff `c` is injective.
* `map_not_injective` : if `c` is not injective then `List.map c` is not injective, and the
  witnesses can be taken to be lists of length 1.
* `stream_code_not_injective` : if `c` is not injective then `s ↦ c ∘ s` is not injective.
* `not_injective_of_card_lt` : `Fintype.card β < Fintype.card α` implies `c` is not injective.
* `code_lossy_of_card_lt` : under `card β < card α`, both `List.map c` (already on length-1 lists)
  and `s ↦ c ∘ s` fail to be injective.
* `collapse` (`Bool → Unit`) : an explicit code with `card Unit = 1 < 2 = card Bool`, and
  `collapse_lossy` : `List.map collapse` is not injective (`[true] ≠ [false]` have the same image).

## INTERPRETED

In the reading of Deleuze–Guattari's *Anti-Oedipus*, desiring-machines operate by *cuts*
(breaks in a flow that extract a part while the flow continues), while social machines operate
by *coding* (inscribing flows onto a register). The theorems above say: cuts, singly or in
sequence, lose no information about the flow; an elementwise code into a smaller alphabet
necessarily identifies distinct flows. This is only a formal shadow of that distinction, not
a formalization of the book's claims.
-/

namespace CutsVersusCodesB

variable {α β : Type*}

/-! ### Cuts on lists -/

theorem list_cut_lossless (l : List α) (n : ℕ) : l.take n ++ l.drop n = l :=
  List.take_append_drop n l

theorem list_two_cuts_lossless (l : List α) (n m : ℕ) :
    l.take n ++ (l.drop n).take m ++ (l.drop n).drop m = l := by
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

/-- The list cut map is injective. -/
theorem list_cut_injective (n : ℕ) :
    Function.Injective (fun l : List α => (l.take n, l.drop n)) := by
  intro l₁ l₂ h
  simp only [Prod.mk.injEq] at h
  rw [← List.take_append_drop n l₁, ← List.take_append_drop n l₂, h.1, h.2]

/-! ### Cuts on streams -/

/-- Glue a length-`n` prefix and a tail back into a stream. -/
def glue (n : ℕ) (p : Fin n → α) (t : ℕ → α) : ℕ → α :=
  fun i => if h : i < n then p ⟨i, h⟩ else t (i - n)

/-- The stream cut at `n`: prefix of length `n` and the shifted tail. -/
def streamCut (n : ℕ) (s : ℕ → α) : (Fin n → α) × (ℕ → α) :=
  (fun i : Fin n => s i, fun i => s (i + n))

theorem stream_cut_reconstruct (n : ℕ) (s : ℕ → α) :
    glue n (streamCut n s).1 (streamCut n s).2 = s := by
  funext i
  simp only [glue, streamCut]
  split_ifs with h
  · rfl
  · congr 1
    omega

theorem stream_cut_injective (n : ℕ) :
    Function.Injective (streamCut (α := α) n) := by
  intro s₁ s₂ h
  rw [← stream_cut_reconstruct n s₁, ← stream_cut_reconstruct n s₂, h]

/-- Two successive stream cuts: at `n`, then at `m` inside the tail. -/
def streamCut2 (n m : ℕ) (s : ℕ → α) : (Fin n → α) × (Fin m → α) × (ℕ → α) :=
  ((streamCut n s).1, streamCut m (streamCut n s).2)

theorem stream_two_cuts_reconstruct (n m : ℕ) (s : ℕ → α) :
    glue n (streamCut2 n m s).1
      (glue m (streamCut2 n m s).2.1 (streamCut2 n m s).2.2) = s := by
  simp only [streamCut2]
  rw [stream_cut_reconstruct m, stream_cut_reconstruct n]

theorem stream_two_cuts_injective (n m : ℕ) :
    Function.Injective (streamCut2 (α := α) n m) := by
  intro s₁ s₂ h
  rw [← stream_two_cuts_reconstruct n m s₁, ← stream_two_cuts_reconstruct n m s₂, h]

/-! ### Codes -/

theorem map_injective_iff (c : α → β) :
    Function.Injective (List.map c) ↔ Function.Injective c :=
  List.map_injective_iff

theorem map_not_injective (c : α → β) (hc : ¬ Function.Injective c) :
    ¬ Function.Injective (List.map c) ∧
      ∃ a b : α, [a] ≠ [b] ∧ List.map c [a] = List.map c [b] := by
  refine ⟨fun h => hc ((map_injective_iff c).1 h), ?_⟩
  simp only [Function.Injective, not_forall] at hc
  obtain ⟨a, b, hab, hne⟩ := hc
  exact ⟨a, b, by simpa using hne, by simp [hab]⟩

theorem stream_code_not_injective (c : α → β) (hc : ¬ Function.Injective c) :
    ¬ Function.Injective (fun s : ℕ → α => c ∘ s) := by
  intro h
  apply hc
  intro a b hab
  have := h (a₁ := fun _ => a) (a₂ := fun _ => b) (by funext i; simp [hab])
  exact congrFun this 0

theorem not_injective_of_card_lt [Fintype α] [Fintype β] (c : α → β)
    (hcard : Fintype.card β < Fintype.card α) : ¬ Function.Injective c :=
  fun h => absurd (Fintype.card_le_of_injective c h) (not_le.2 hcard)

theorem code_lossy_of_card_lt [Fintype α] [Fintype β] (c : α → β)
    (hcard : Fintype.card β < Fintype.card α) :
    ¬ Function.Injective (List.map c) ∧
      (∃ a b : α, [a] ≠ [b] ∧ List.map c [a] = List.map c [b]) ∧
      ¬ Function.Injective (fun s : ℕ → α => c ∘ s) :=
  let hc := not_injective_of_card_lt c hcard
  ⟨(map_not_injective c hc).1, (map_not_injective c hc).2, stream_code_not_injective c hc⟩

/-- An explicit code collapsing a two-letter alphabet to one letter. -/
def collapse : Bool → Unit := fun _ => ()

theorem collapse_card_lt : Fintype.card Unit < Fintype.card Bool := by decide

theorem collapse_lossy :
    ¬ Function.Injective (List.map collapse) ∧
      List.map collapse [true] = List.map collapse [false] ∧ [true] ≠ [false] :=
  ⟨(code_lossy_of_card_lt collapse collapse_card_lt).1, rfl, by decide⟩

end CutsVersusCodesB
