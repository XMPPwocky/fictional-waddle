import Mathlib

/-!
# Oedipal triangulation as pigeonhole on `Fin 3`

Setting: `D` a finite type with `Fintype.card D = n`, and `t : D → Fin 3` an arbitrary map.
An unordered pair of distinct elements of `D` is a 2-element `Finset D`; it is *collapsed*
by `t` when both elements have the same image.

PROVED
* `not_injective_of_card_gt_three` : if `3 < n` then `t` is not injective.
* `exists_large_fibre` : `∃ k, n ≤ (univ.filter (fun d => t d = k)).card * 3`
  (some fibre has at least `⌈n/3⌉` elements).
* `card_collapsedPairs_eq_sum` : the number of collapsed unordered pairs equals
  `∑ k, (card of fibre k).choose 2`.
* `three_mul_choose_le_card_collapsedPairs` : the number of collapsed unordered pairs is
  at least `3 * (n / 3).choose 2` (full target (3), with `n / 3 = ⌊n/3⌋`).
* `one_le_card_collapsedPairs` : if `4 ≤ n`, at least one collapsed pair exists.
* `three_le_card_collapsedPairs` : if `7 ≤ n`, at least three collapsed pairs exist.
  (These two are stated separately because `3 * (n/3).choose 2` is `0` for `n ≤ 5` and
  `3` only from `n = 6`; they are proved directly from the fibre-sum identity.)

INTERPRETED
* `D` is read as a set of desires and `Fin 3` as the triangle daddy–mommy–me. The
  Deleuze–Guattari claim that Oedipal triangulation crushes the multiplicity of desire is
  read as: any assignment of more than three desires to three corners identifies distinct
  desires, some corner absorbs at least a third of them, and the number of identified
  pairs grows quadratically in `n` (at least `3 * C(⌊n/3⌋, 2)`), regardless of `t`.
-/

namespace OedipalTriangulationA

open Finset

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The fibre of `t` over the corner `k`. -/
def fibre (t : D → Fin 3) (k : Fin 3) : Finset D :=
  univ.filter (fun d => t d = k)

/-- Unordered pairs of distinct desires (2-element subsets) sent to a common corner. -/
def collapsedPairs (t : D → Fin 3) : Finset (Finset D) :=
  (univ.powersetCard 2).filter (fun s => ∃ k, ∀ d ∈ s, t d = k)

omit [DecidableEq D] in
theorem not_injective_of_card_gt_three (t : D → Fin 3) (h : 3 < Fintype.card D) :
    ¬ Function.Injective t := by
  intro hinj
  have := Fintype.card_le_of_injective t hinj
  simp at this
  omega

omit [DecidableEq D] in
theorem card_eq_sum_fibre (t : D → Fin 3) :
    Fintype.card D = ∑ k, (fibre t k).card := by
  rw [← Finset.card_univ]
  exact Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (t x))

omit [DecidableEq D] in
theorem card_eq_fibre_three (t : D → Fin 3) :
    Fintype.card D = (fibre t 0).card + (fibre t 1).card + (fibre t 2).card := by
  rw [card_eq_sum_fibre, Fin.sum_univ_three]

omit [DecidableEq D] in
theorem exists_large_fibre (t : D → Fin 3) :
    ∃ k, Fintype.card D ≤ (univ.filter (fun d => t d = k)).card * 3 := by
  have h := card_eq_fibre_three t
  by_contra hc
  push Not at hc
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  simp only [fibre] at h
  omega

theorem collapsedPairs_eq_biUnion (t : D → Fin 3) :
    collapsedPairs t = univ.biUnion (fun k => (fibre t k).powersetCard 2) := by
  ext s
  simp only [collapsedPairs, fibre, mem_filter, mem_powersetCard, mem_biUnion, mem_univ,
    true_and, subset_univ]
  constructor
  · rintro ⟨hs, k, hk⟩
    refine ⟨k, ?_, hs⟩
    intro d hd
    simp [hk d hd]
  · rintro ⟨k, hsub, hs⟩
    refine ⟨hs, k, ?_⟩
    intro d hd
    have := hsub hd
    simpa using this

theorem card_collapsedPairs_eq_sum (t : D → Fin 3) :
    (collapsedPairs t).card = ∑ k, (fibre t k).card.choose 2 := by
  rw [collapsedPairs_eq_biUnion, Finset.card_biUnion]
  · simp [Finset.card_powersetCard]
  · intro k _ l _ hkl
    rw [Function.onFun, Finset.disjoint_left]
    intro s hs hs'
    rw [mem_powersetCard] at hs hs'
    obtain ⟨d, hd⟩ : s.Nonempty := by
      rw [← Finset.card_pos, hs.2]; norm_num
    have h1 := hs.1 hd
    have h2 := hs'.1 hd
    simp only [fibre, mem_filter, mem_univ, true_and] at h1 h2
    exact hkl (h1 ▸ h2)

theorem card_collapsedPairs_eq_three (t : D → Fin 3) :
    (collapsedPairs t).card =
      (fibre t 0).card.choose 2 + (fibre t 1).card.choose 2 + (fibre t 2).card.choose 2 := by
  rw [card_collapsedPairs_eq_sum, Fin.sum_univ_three]

theorem two_mul_choose_two_add (a : ℕ) : 2 * a.choose 2 + a = a * a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

/-- Arithmetic core: `∑ C(aᵢ,2) ≥ 3 C(m,2)` whenever `a₀ + a₁ + a₂ ≥ 3m`. -/
theorem choose_sum_bound (a b c m : ℕ) (h : 3 * m ≤ a + b + c) :
    3 * m.choose 2 ≤ a.choose 2 + b.choose 2 + c.choose 2 := by
  have ha := two_mul_choose_two_add a
  have hb := two_mul_choose_two_add b
  have hc := two_mul_choose_two_add c
  have hm := two_mul_choose_two_add m
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; simp
  · have ha' : ((a : ℤ) - m) ^ 2 ≥ 0 := sq_nonneg _
    have hb' : ((b : ℤ) - m) ^ 2 ≥ 0 := sq_nonneg _
    have hc' : ((c : ℤ) - m) ^ 2 ≥ 0 := sq_nonneg _
    have hz : ((a : ℤ) + b + c - 3 * m) * (2 * m - 1) ≥ 0 := by
      apply mul_nonneg
      · have : (3 * m : ℤ) ≤ a + b + c := by exact_mod_cast h
        linarith
      · have : (1 : ℤ) ≤ m := by exact_mod_cast hpos
        linarith
    have ha'' : (2 * (a.choose 2 : ℤ) + a = a * a) := by exact_mod_cast ha
    have hb'' : (2 * (b.choose 2 : ℤ) + b = b * b) := by exact_mod_cast hb
    have hc'' : (2 * (c.choose 2 : ℤ) + c = c * c) := by exact_mod_cast hc
    have hm'' : (2 * (m.choose 2 : ℤ) + m = m * m) := by exact_mod_cast hm
    have : (3 * m.choose 2 : ℤ) ≤ a.choose 2 + b.choose 2 + c.choose 2 := by
      nlinarith
    exact_mod_cast this

theorem three_mul_choose_le_card_collapsedPairs (t : D → Fin 3) :
    3 * (Fintype.card D / 3).choose 2 ≤ (collapsedPairs t).card := by
  rw [card_collapsedPairs_eq_three]
  apply choose_sum_bound
  rw [← card_eq_fibre_three]
  omega

theorem one_le_card_collapsedPairs (t : D → Fin 3) (h : 4 ≤ Fintype.card D) :
    1 ≤ (collapsedPairs t).card := by
  rw [card_collapsedPairs_eq_three]
  have hn := card_eq_fibre_three t
  have ha := two_mul_choose_two_add (fibre t 0).card
  have hb := two_mul_choose_two_add (fibre t 1).card
  have hc := two_mul_choose_two_add (fibre t 2).card
  generalize (fibre t 0).card = a at *
  generalize (fibre t 1).card = b at *
  generalize (fibre t 2).card = c at *
  by_contra hlt
  push Not at hlt
  have h0 : a.choose 2 = 0 := by omega
  have h1 : b.choose 2 = 0 := by omega
  have h2 : c.choose 2 = 0 := by omega
  rw [h0] at ha; rw [h1] at hb; rw [h2] at hc
  have : a ≤ 1 := by nlinarith
  have : b ≤ 1 := by nlinarith
  have : c ≤ 1 := by nlinarith
  omega

theorem three_le_card_collapsedPairs (t : D → Fin 3) (h : 7 ≤ Fintype.card D) :
    3 ≤ (collapsedPairs t).card := by
  rw [card_collapsedPairs_eq_three]
  have hn := card_eq_fibre_three t
  have ha := two_mul_choose_two_add (fibre t 0).card
  have hb := two_mul_choose_two_add (fibre t 1).card
  have hc := two_mul_choose_two_add (fibre t 2).card
  generalize (fibre t 0).card = a at *
  generalize (fibre t 1).card = b at *
  generalize (fibre t 2).card = c at *
  have key : (2 : ℤ) * (a.choose 2 + b.choose 2 + c.choose 2) ≥ 5 := by
    have ha'' : (2 * (a.choose 2 : ℤ) + a = a * a) := by exact_mod_cast ha
    have hb'' : (2 * (b.choose 2 : ℤ) + b = b * b) := by exact_mod_cast hb
    have hc'' : (2 * (c.choose 2 : ℤ) + c = c * c) := by exact_mod_cast hc
    have hsum : (7 : ℤ) ≤ a + b + c := by exact_mod_cast (hn ▸ h)
    have hq : ((a : ℤ) + b + c - 7) * ((a : ℤ) + b + c + 4) ≥ 0 :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [sq_nonneg ((a : ℤ) - b), sq_nonneg ((b : ℤ) - c), sq_nonneg ((a : ℤ) - c)]
  have : (5 : ℤ) ≤ 2 * ((a.choose 2 + b.choose 2 + c.choose 2 : ℕ) : ℤ) := by
    push_cast; linarith
  omega

end OedipalTriangulationA
