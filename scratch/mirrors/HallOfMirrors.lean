import Mathlib

/-!
# Hall of mirrors: perspective, Projective SET and tit for tat

PROVED:
* `cross_ratio_perspective`: a pinhole view sends an image at depth `d` to screen position `f * a / d`. That map
  preserves the cross-ratio of any four distinct nonzero depths, so the receding images in a hall of mirrors keep
  their cross-ratio on the screen even though their spacing shrinks.
* `proset`: any `n + 1` cards of Projective SET with `n` dots (vectors in `(ZMod 2)^n`) contain a nonempty set whose
  dots all appear an even number of times. `proset_seven`: the usual deal of 7 cards with 6 dots always has one.
* `mirror_involution`, `mirror_set`: projecting from a card `c` pairs each card `x` with its mirror image `x + c`.
  Mirroring twice returns `x`, and `x`, `x + c`, `c` always form a set.
* `tft_echo`: two tit-for-tat players copy each other's last move, so the pair of moves is swapped each round. After
  a single mistake the defection bounces between them forever: the state alternates between the two lopsided pairs
  and never returns to mutual cooperation.
INTERPRETED (not formalized): a forgiving tit for tat as a partly reflecting mirror; the echo of a mistake surviving
`n` rounds with probability `(1 - g)^n` like the brightness `r^n` of the `n`-th image.
-/

namespace HallOfMirrors

/-- Cross-ratio of four numbers. -/
noncomputable def cr (a b c d : ℝ) : ℝ := ((c - a) * (d - b)) / ((c - b) * (d - a))

theorem cross_ratio_perspective (f x a b c d : ℝ) (hf : f ≠ 0) (hx : x ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    cr (f * x / a) (f * x / b) (f * x / c) (f * x / d) = cr a b c d := by
  unfold cr
  by_cases h1 : c - b = 0
  · have : c = b := by linarith
    subst this; simp
  by_cases h2 : d - a = 0
  · have : d = a := by linarith
    subst this; simp
  have e1 : f * x / c - f * x / a = f * x * (a - c) / (a * c) := by field_simp
  have e2 : f * x / d - f * x / b = f * x * (b - d) / (b * d) := by field_simp
  have e3 : f * x / c - f * x / b = f * x * (b - c) / (b * c) := by field_simp
  have e4 : f * x / d - f * x / a = f * x * (a - d) / (a * d) := by field_simp
  rw [e1, e2, e3, e4]
  have hbc : b - c ≠ 0 := fun h => h1 (by linarith)
  have had : a - d ≠ 0 := fun h => h2 (by linarith)
  field_simp
  ring

theorem proset (n : ℕ) (v : Fin (n + 1) → (Fin n → ZMod 2)) :
    ∃ s : Finset (Fin (n + 1)), s.Nonempty ∧ ∑ i ∈ s, v i = 0 := by
  have hnot : ¬ LinearIndependent (ZMod 2) v := by
    intro h
    have := h.fintype_card_le_finrank
    simp at this
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnot
  refine ⟨Finset.univ.filter (fun j => g j ≠ 0), ⟨i, by simp [hi]⟩, ?_⟩
  have h01 : ∀ j, g j • v j = if g j ≠ 0 then v j else 0 := by
    intro j
    rcases (show g j = 0 ∨ g j = 1 by generalize g j = a; revert a; decide) with h | h <;> simp [h]
  calc ∑ j ∈ Finset.univ.filter (fun j => g j ≠ 0), v j
      = ∑ j, (if g j ≠ 0 then v j else 0) := Finset.sum_filter _ _
    _ = ∑ j, g j • v j := Finset.sum_congr rfl (fun j _ => (h01 j).symm)
    _ = 0 := hg

theorem proset_seven (v : Fin 7 → (Fin 6 → ZMod 2)) :
    ∃ s : Finset (Fin 7), s.Nonempty ∧ ∑ i ∈ s, v i = 0 := proset 6 v

theorem mirror_involution {n : ℕ} (x c : Fin n → ZMod 2) : (x + c) + c = x := by
  ext i; simp only [Pi.add_apply]; generalize x i = a; generalize c i = b
  fin_cases a <;> fin_cases b <;> rfl

theorem mirror_set {n : ℕ} (x c : Fin n → ZMod 2) : x + (x + c) + c = 0 := by
  ext i; simp only [Pi.add_apply, Pi.zero_apply]; generalize x i = a; generalize c i = b
  fin_cases a <;> fin_cases b <;> rfl

/-- One round of tit for tat for both players: each plays the other's last move (`true` = cooperate). -/
def tft (s : Bool × Bool) : Bool × Bool := (s.2, s.1)

theorem tft_echo (n : ℕ) :
    tft^[n] (false, true) = (if n % 2 = 0 then (false, true) else (true, false)) ∧
    tft^[n] (false, true) ≠ (true, true) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih.1]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have : (k + 1) % 2 = 1 := by omega
      simp [h, this, tft]
    · have : (k + 1) % 2 = 0 := by omega
      simp [h, this, tft]

end HallOfMirrors
