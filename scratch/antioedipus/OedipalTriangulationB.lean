import Mathlib

/-!
# Oedipal triangulation as a pigeonhole statement

Setting: `D` is a finite type with `Fintype.card D = n`, and `t : D → Fin 3` is an arbitrary map.
The fibre over a corner `k` is `fibre t k = univ.filter (fun d => t d = k)`.
An unordered pair of distinct elements is a 2-element `Finset D`; it is *collapsed* by `t`
if both of its elements have the same image. `collapsedPairs t` is the finset of such pairs.

## PROVED
* `not_injective_of_card_gt_three`: if `3 < n` then `t` is not injective.
* `exists_large_fibre`: `∃ k, n ≤ (fibre t k).card * 3`, i.e. some fibre has at least `⌈n/3⌉`
  elements.
* `card_collapsedPairs_eq`: `(collapsedPairs t).card = ∑ k, ((fibre t k).card).choose 2`.
* `collapsedPairs_lower_bound` (full target (3)):
  `3 * (n / 3).choose 2 ≤ (collapsedPairs t).card`.
* `collapsedPairs_pos_of_four_le`: if `4 ≤ n` then at least one collapsed pair exists.
* `three_le_collapsedPairs_of_seven_le`: if `7 ≤ n` then at least three collapsed pairs exist.

All statements hold for every `t`, so the bound in (3) is the full stated target, not the weaker
fallback; the fallback statements are proved as well, as separate theorems.

## INTERPRETED
Reading of Deleuze–Guattari, *Anti-Oedipus*: `D` is a multiplicity of desires and `t` is the
Oedipal triangulation daddy–mommy–me (`Fin 3`). The theorems say that once there are more than
three desires the triangulation must identify distinct desires (1), that some corner absorbs at
least a third of all desire (2), and that the number of pairs of distinct desires that the
triangle cannot tell apart grows quadratically, at least `3·C(⌊n/3⌋, 2)` (3). This reading is
an interpretation only; the mathematics is the finite pigeonhole principle and convexity of
`a ↦ C(a, 2)`.
-/

namespace OedipalTriangulationB

open Finset

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The fibre of `t` over the corner `k`. -/
def fibre (t : D → Fin 3) (k : Fin 3) : Finset D :=
  univ.filter (fun d => t d = k)

/-- Unordered pairs of distinct elements (2-element subsets) whose elements share a corner. -/
def collapsedPairs (t : D → Fin 3) : Finset (Finset D) :=
  (univ.powersetCard 2).filter (fun s => ∃ k, ∀ x ∈ s, t x = k)

omit [DecidableEq D] in
theorem not_injective_of_card_gt_three (t : D → Fin 3) (h : 3 < Fintype.card D) :
    ¬ Function.Injective t := by
  intro hinj
  have := Fintype.card_le_of_injective t hinj
  simp at this
  omega

omit [DecidableEq D] in
theorem sum_card_fibre (t : D → Fin 3) :
    ∑ k, (fibre t k).card = Fintype.card D := by
  unfold fibre
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := t) (t := univ)
    (fun _ _ => Finset.mem_univ _)]

omit [DecidableEq D] in
theorem exists_large_fibre (t : D → Fin 3) :
    ∃ k, Fintype.card D ≤ (fibre t k).card * 3 := by
  by_contra hcon
  push Not at hcon
  have hs := sum_card_fibre t
  rw [Fin.sum_univ_three] at hs
  have h0 := hcon 0
  have h1 := hcon 1
  have h2 := hcon 2
  omega

theorem collapsedPairs_eq_biUnion (t : D → Fin 3) :
    collapsedPairs t = univ.biUnion (fun k => (fibre t k).powersetCard 2) := by
  ext s
  simp only [collapsedPairs, fibre, mem_filter, mem_powersetCard, mem_biUnion, mem_univ,
    true_and, subset_univ]
  constructor
  · rintro ⟨hc, k, hk⟩
    refine ⟨k, ?_, hc⟩
    intro x hx
    simp [hk x hx]
  · rintro ⟨k, hsub, hc⟩
    refine ⟨hc, k, ?_⟩
    intro x hx
    have := hsub hx
    simpa using this

theorem card_collapsedPairs_eq (t : D → Fin 3) :
    (collapsedPairs t).card = ∑ k, ((fibre t k).card).choose 2 := by
  rw [collapsedPairs_eq_biUnion, card_biUnion]
  · simp [Finset.card_powersetCard]
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro s hsi hsj
    rw [mem_powersetCard] at hsi hsj
    obtain ⟨x, hx⟩ : s.Nonempty := by
      rw [← Finset.card_pos, hsi.2]; norm_num
    have hi := hsi.1 hx
    have hj := hsj.1 hx
    simp only [fibre, mem_filter, mem_univ, true_and] at hi hj
    exact hij (hi.symm.trans hj)

/-- Convexity inequality: `a(a-1) + b(b-1) + c(c-1) ≥ 3q(q-1)` whenever `3q ≤ a+b+c`. -/
theorem convex_aux (a b c q : ℕ) (h : 3 * q ≤ a + b + c) :
    3 * (q.choose 2) ≤ a.choose 2 + b.choose 2 + c.choose 2 := by
  have key : ∀ x : ℕ, (x : ℤ) * (x - 1) ≥ (q : ℤ) * (q - 1) + 2 * ((x : ℤ) - q) * ((q : ℤ) - 1) := by
    intro x
    have hcons : ((x : ℤ) - q) * ((x : ℤ) - q + 1) ≥ 0 := by
      rcases le_or_gt q x with hx | hx
      · have h1 : ((x : ℤ) - q) ≥ 0 := by
          have : (q : ℤ) ≤ x := by exact_mod_cast hx
          linarith
        have h2 : ((x : ℤ) - q + 1) ≥ 0 := by linarith
        exact mul_nonneg h1 h2
      · have h1 : ((x : ℤ) - q) ≤ -1 := by
          have : (x : ℤ) + 1 ≤ q := by exact_mod_cast hx
          linarith
        have h2 : ((x : ℤ) - q + 1) ≤ 0 := by linarith
        nlinarith
    nlinarith
  have hc2 : ∀ x : ℕ, ((x.choose 2 : ℕ) : ℤ) * 2 = (x : ℤ) * (x - 1) := by
    intro x
    have hn : x.choose 2 * 2 = x * (x - 1) := by
      rw [Nat.choose_two_right]
      exact Nat.div_mul_cancel (Nat.even_mul_pred_self x).two_dvd
    rcases Nat.eq_zero_or_pos x with h0 | hpos
    · subst h0; simp
    · have := congrArg (Nat.cast (R := ℤ)) hn
      push_cast [Nat.cast_sub hpos] at this
      linarith
  have ka := key a
  have kb := key b
  have kc := key c
  have hz : (3 : ℤ) * q ≤ a + b + c := by exact_mod_cast h
  have target : ((3 * q.choose 2 : ℕ) : ℤ) * 2 ≤
      ((a.choose 2 + b.choose 2 + c.choose 2 : ℕ) : ℤ) * 2 := by
    push_cast
    have e1 := hc2 q
    have e2 := hc2 a
    have e3 := hc2 b
    have e4 := hc2 c
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      simp
      positivity
    · have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast hq
      have hsum : 0 ≤ 2 * (((a : ℤ) + b + c) - 3 * q) * ((q : ℤ) - 1) := by
        apply mul_nonneg
        · linarith
        · linarith
      nlinarith
  have : ((3 * q.choose 2 : ℕ) : ℤ) ≤ ((a.choose 2 + b.choose 2 + c.choose 2 : ℕ) : ℤ) := by
    linarith
  exact_mod_cast this

theorem collapsedPairs_lower_bound (t : D → Fin 3) :
    3 * ((Fintype.card D / 3).choose 2) ≤ (collapsedPairs t).card := by
  rw [card_collapsedPairs_eq, Fin.sum_univ_three]
  apply convex_aux
  have hs := sum_card_fibre t
  rw [Fin.sum_univ_three] at hs
  omega

theorem collapsedPairs_pos_of_four_le (t : D → Fin 3) (h : 4 ≤ Fintype.card D) :
    1 ≤ (collapsedPairs t).card := by
  obtain ⟨k, hk⟩ := exists_large_fibre t
  have h2 : 2 ≤ (fibre t k).card := by omega
  have hle : (fibre t k).card.choose 2 ≤ ∑ j, ((fibre t j).card).choose 2 :=
    Finset.single_le_sum (f := fun j => ((fibre t j).card).choose 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hc : (2 : ℕ).choose 2 ≤ (fibre t k).card.choose 2 := Nat.choose_le_choose 2 h2
  rw [card_collapsedPairs_eq]
  simp at hc
  omega

theorem three_le_collapsedPairs_of_seven_le (t : D → Fin 3) (h : 7 ≤ Fintype.card D) :
    3 ≤ (collapsedPairs t).card := by
  obtain ⟨k, hk⟩ := exists_large_fibre t
  have h3 : 3 ≤ (fibre t k).card := by omega
  have hle : (fibre t k).card.choose 2 ≤ ∑ j, ((fibre t j).card).choose 2 :=
    Finset.single_le_sum (f := fun j => ((fibre t j).card).choose 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hc : (3 : ℕ).choose 2 ≤ (fibre t k).card.choose 2 := Nat.choose_le_choose 2 h3
  rw [card_collapsedPairs_eq]
  have : (3 : ℕ).choose 2 = 3 := by decide
  omega

end OedipalTriangulationB
