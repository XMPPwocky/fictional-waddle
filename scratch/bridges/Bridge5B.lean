import Mathlib

/-!
# Every winning angel is forced onto every path; the open-loop copy count is exactly `2^(n+1)`

Setting as in `scratch/angels/AngelBinaryTreeA.lean` (definitions `Strategy`, `seen`, `pos`
and the strategy `newestBlockStrategy` are copied verbatim). Nodes are `List Bool`, the devil
is `d : ℕ → List Bool`, `pos σ d (n+1)` is the angel's node after the move of turn `n`.

`PathSurvives d n p :≡ ∀ k ≤ n, ∀ i ≤ k, d i ≠ p.take (k+1)`: a fixed (open-loop) path `p`
avoids every block that was already placed when it stepped onto each of its first `n+1` nodes.

The sibling chain of `w` is `sib w k = w.take k ++ [!(w.getD k false)]`; for `k < w.length`
this is `w.take k ++ [!(w.get k)]`, the sibling of the `(k+1)`-st node of `w`.

## PROVED

* (i) `part_i`: for all `d, n`,
  `#{p : Fin (n+1) → Bool | PathSurvives d n (List.ofFn p)} ≥ 2^(n+1) − Σ_{i ≤ n, i+1 ≤ |d i| ≤ n+1} 2^(n+1−|d i|) ≥ 1`
  (natural-number subtraction); the untruncated forms are `survivors_add_deathMass`
  (`2^(n+1) ≤ #survivors + Σ`) and `deathMass_lt` (`Σ + 1 ≤ 2^(n+1)`).
* (ii) `part_ii`: if every member of `C : Finset (List Bool)` has length `n+1` and
  `C.card < 2^(n+1)`, there is `w` of length `n+1` with `w ∉ C` and the sibling chain `sib w`
  kills every `p ∈ C`; `part_ii_exists` is the `∃ d` form. Key lemma `sib_survives_iff`:
  for `p` of length `n+1`, `PathSurvives (sib w) n p ↔ p = w`.
* `copy_count_exact`: the least size of a set `C` of length-`(n+1)` paths such that for every
  devil some member of `C` survives is exactly `2^(n+1)`.
* (iii) `forced_onto_path`: if `σ` satisfies `∀ d n, ∀ i ≤ n, d i ≠ pos σ d (n+1)`, then for
  every `n` and every `w` of length `n+1`, `pos σ (sib w) (n+1) = w`; `onto` gives
  `Set.range (fun d => pos σ d (n+1)) = {w | w.length = n+1}`. `winning_exists` and
  `newestBlock_onto` show the hypothesis is satisfiable (by `newestBlockStrategy`).
* (iv) With `qU n` uniform `(2^(n+1))⁻¹` on `Fin (n+1) → Bool` and `sInd d n` the survival
  indicator, and `S`, `post`, `KL` as in `scratch/refrigerator/SelectionCarnot.lean`:
  `S_ge`: `S ≥ (2^(n+1))⁻¹`; `KL_eq_log`: `KL = log (1/S)`; `KL_eq`:
  `KL = (n+1) log 2 − log #survivors`; `KL_le`: `KL ≤ (n+1) log 2`;
  `KL_eq_max_iff`: `KL = (n+1) log 2 ↔ #survivors = 1`; `sib_attains_max`: sibling chains
  attain it; `KL_isGreatest`: `(n+1) log 2` is the maximum over `d`;
  `KL_nonneg`, `nil_attains_min`, `KL_isLeast`: the minimum over `d` is `0`, attained by
  `d ≡ []`; `exp_max_fuel`: `exp ((n+1) log 2) = 2^(n+1)`.

## INTERPRETED

* "Open-loop copy": a path fixed in advance, not reacting to the devil. (ii) and
  `copy_count_exact` say `2^(n+1)` such copies are needed and suffice; (iii) says one adaptive
  angel that never loses must be able to end on every one of those `2^(n+1)` paths.
* "Fuel": `log (1/S)`, the selection cost of conditioning the uniform path distribution on
  survival; its maximum over devils is `(n+1) log 2`, and `exp` of it is the copy count.
-/

namespace Bridge5B
open Finset Real Classical

/-! ## Setting (copied from `AngelBinaryTreeA`) -/

/-- A strategy: current node and blocks seen so far `[d 0, …, d k]` ↦ child direction. -/
abbrev Strategy := List Bool → List (List Bool) → Bool

/-- Blocks seen through turn `k`: `[d 0, …, d k]`. -/
def seen (d : ℕ → List Bool) (k : ℕ) : List (List Bool) := (List.range (k + 1)).map d

/-- Angel position before devil move `k` (after `k` angel moves). -/
def pos (σ : Strategy) (d : ℕ → List Bool) : ℕ → List Bool
  | 0 => []
  | k + 1 => pos σ d k ++ [σ (pos σ d k) (seen d k)]

/-- Move to the `true` child iff the newest block lies in the closed subtree of the
`false` child. -/
def newestBlockStrategy : Strategy := fun l B =>
  match B.getLast? with
  | some x => decide (l ++ [false] <+: x)
  | none => false

/-! ## Definitions -/

/-- A fixed path `p` survives the devil `d` through turn `n`. -/
def PathSurvives (d : ℕ → List Bool) (n : ℕ) (p : List Bool) : Prop :=
  ∀ k ≤ n, ∀ i ≤ k, d i ≠ p.take (k + 1)

/-- The sibling chain of `w`: at turn `k`, block the sibling of the `(k+1)`-st node of `w`. -/
def sib (w : List Bool) (k : ℕ) : List Bool := w.take k ++ [!(w.getD k false)]

/-- Surviving paths of length `n+1`, as functions `Fin (n+1) → Bool`. -/
noncomputable def surv (d : ℕ → List Bool) (n : ℕ) : Finset (Fin (n + 1) → Bool) :=
  univ.filter (fun p => PathSurvives d n (List.ofFn p))

/-- Indices of blocks that can hit a path of length `n+1` in time. -/
noncomputable def hitSet (d : ℕ → List Bool) (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun i => i + 1 ≤ (d i).length ∧ (d i).length ≤ n + 1)

/-- `Σ_{i ≤ n, i+1 ≤ |d i| ≤ n+1} 2^(n+1−|d i|)`. -/
noncomputable def deathMass (d : ℕ → List Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ hitSet d n, 2 ^ (n + 1 - (d i).length)

/-! ## (i) Counting survivors -/

lemma card_paths (n : ℕ) : (univ : Finset (Fin (n + 1) → Bool)).card = 2 ^ (n + 1) := by
  simp

lemma card_ext_le (n m : ℕ) (w : List Bool) (hm : m ≤ n + 1) :
    (univ.filter fun p : Fin (n + 1) → Bool => (List.ofFn p).take m = w).card
      ≤ 2 ^ (n + 1 - m) := by
  have h := Finset.card_le_card_of_injOn
    (s := univ.filter fun p : Fin (n + 1) → Bool => (List.ofFn p).take m = w)
    (t := (univ : Finset (Fin (n + 1 - m) → Bool)))
    (fun p j => p ⟨j.1 + m, by omega⟩) (fun _ _ => by simp) ?_
  · simpa using h
  · intro p hp p' hp' hpp
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp hp'
    funext x
    by_cases hx : x.1 < m
    · have h1 := congrArg (fun l => l[x.1]?) hp
      have h2 := congrArg (fun l => l[x.1]?) hp'
      simp only [List.getElem?_take, hx, ite_true, List.getElem?_ofFn, x.2, dite_true] at h1 h2
      have := h1.trans h2.symm
      simpa using this
    · have := congrFun hpp ⟨x.1 - m, by omega⟩
      simp only at this
      have e : (⟨x.1 - m + m, by omega⟩ : Fin (n + 1)) = x := Fin.ext (by simp; omega)
      rwa [e] at this

lemma killed_subset (d : ℕ → List Bool) (n : ℕ) :
    univ.filter (fun p : Fin (n + 1) → Bool => ¬ PathSurvives d n (List.ofFn p)) ⊆
      (hitSet d n).biUnion
        (fun i => univ.filter fun p : Fin (n + 1) → Bool => (List.ofFn p).take (d i).length = d i) := by
  intro p hp
  have hp' := (mem_filter.mp hp).2
  simp only [PathSurvives] at hp'
  push Not at hp'
  obtain ⟨k, hk, i, hi, h⟩ := hp'
  have hlen : (d i).length = k + 1 := by rw [h]; simp; omega
  simp only [mem_biUnion, mem_filter, mem_univ, true_and, hitSet, mem_range]
  exact ⟨i, ⟨by omega, by omega, by omega⟩, by rw [hlen, h]⟩

/-- Untruncated form of (i), first inequality. -/
theorem survivors_add_deathMass (d : ℕ → List Bool) (n : ℕ) :
    2 ^ (n + 1) ≤ (surv d n).card + deathMass d n := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin (n + 1) → Bool))) (fun p => PathSurvives d n (List.ofFn p))
  rw [card_paths] at hsplit
  have hK := (card_le_card (killed_subset d n)).trans card_biUnion_le
  have hS : ∑ i ∈ hitSet d n,
      (univ.filter fun p : Fin (n + 1) → Bool => (List.ofFn p).take (d i).length = d i).card
        ≤ deathMass d n :=
    sum_le_sum fun i hi => card_ext_le n _ _ (by simp [hitSet] at hi; omega)
  unfold surv; omega

lemma geom : ∀ n : ℕ, ∑ i ∈ range (n + 1), 2 ^ (n - i) + 1 = 2 ^ (n + 1)
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ']
    have := geom n
    simp only [Nat.add_sub_add_right, Nat.sub_zero] at *
    rw [pow_succ]; omega

/-- Untruncated form of (i), second inequality. -/
theorem deathMass_lt (d : ℕ → List Bool) (n : ℕ) : deathMass d n + 1 ≤ 2 ^ (n + 1) := by
  have h1 : deathMass d n ≤ ∑ i ∈ hitSet d n, 2 ^ (n - i) :=
    sum_le_sum fun i hi => Nat.pow_le_pow_right (by norm_num) (by simp [hitSet] at hi; omega)
  have h2 : ∑ i ∈ hitSet d n, 2 ^ (n - i) ≤ ∑ i ∈ range (n + 1), 2 ^ (n - i) :=
    sum_le_sum_of_subset (filter_subset _ _)
  have := geom n; omega

/-- (i) as stated. -/
theorem part_i (d : ℕ → List Bool) (n : ℕ) :
    2 ^ (n + 1) - ∑ i ∈ (range (n + 1)).filter
        (fun i => i + 1 ≤ (d i).length ∧ (d i).length ≤ n + 1), 2 ^ (n + 1 - (d i).length)
      ≤ (univ.filter fun p : Fin (n + 1) → Bool => PathSurvives d n (List.ofFn p)).card ∧
    1 ≤ 2 ^ (n + 1) - ∑ i ∈ (range (n + 1)).filter
        (fun i => i + 1 ≤ (d i).length ∧ (d i).length ≤ n + 1), 2 ^ (n + 1 - (d i).length) := by
  have h1 := survivors_add_deathMass d n
  have h2 := deathMass_lt d n
  unfold surv deathMass hitSet at *
  constructor <;> omega

lemma surv_card_pos (d : ℕ → List Bool) (n : ℕ) : 1 ≤ (surv d n).card := by
  have h1 := survivors_add_deathMass d n
  have h2 := deathMass_lt d n
  omega

/-! ## (ii) Sibling chains kill every other path -/

theorem sib_survives_iff (w p : List Bool) (n : ℕ) (hw : w.length = n + 1)
    (hp : p.length = n + 1) : PathSurvives (sib w) n p ↔ p = w := by
  constructor
  · intro h
    by_contra hne
    have hex : ∃ k, k ≤ n ∧ p.take (k + 1) ≠ w.take (k + 1) := ⟨n, le_rfl, by
      rwa [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]⟩
    obtain ⟨k, hk, hmin⟩ : ∃ k, (k ≤ n ∧ p.take (k + 1) ≠ w.take (k + 1)) ∧
        ∀ j < k, ¬ (j ≤ n ∧ p.take (j + 1) ≠ w.take (j + 1)) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
    have hpre : p.take k = w.take k := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0; simp
      · have := hmin (k - 1) (by omega)
        push Not at this
        have := this (by omega)
        rwa [Nat.sub_add_cancel hpos] at this
    have hkp : k < p.length := by omega
    have hkw : k < w.length := by omega
    have hp1 : p.take (k + 1) = p.take k ++ [p[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hkp]; rfl
    have hw1 : w.take (k + 1) = w.take k ++ [w[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hkw]; rfl
    have hne' : p[k] ≠ w[k] := fun e => hk.2 (by rw [hp1, hw1, hpre, e])
    have hsib : sib w k = p.take (k + 1) := by
      rw [hp1, hpre, sib, List.getD_eq_getElem w false hkw]
      congr 2
      revert hne'
      generalize p[k] = a
      generalize w[k] = b
      cases a <;> cases b <;> simp
    exact h k hk.1 k le_rfl hsib
  · rintro rfl k hk i hi heq
    have hl := congrArg List.length heq
    simp only [sib, List.length_append, List.length_take, List.length_singleton] at hl
    have hik : i = k := by omega
    subst hik
    have hpi : i < p.length := by omega
    rw [sib, List.getD_eq_getElem p false hpi, List.take_add_one (l := p) (i := i),
      List.getElem?_eq_getElem hpi] at heq
    have := List.append_cancel_left heq
    simp at this

lemma exists_path_notMem (n : ℕ) (C : Finset (List Bool)) (hcard : C.card < 2 ^ (n + 1)) :
    ∃ w : List Bool, w.length = n + 1 ∧ w ∉ C := by
  have hT : (univ.image (fun p : Fin (n + 1) → Bool => List.ofFn p)).card = 2 ^ (n + 1) := by
    rw [card_image_of_injective _ List.ofFn_injective, card_paths]
  obtain ⟨w, hwT, hwC⟩ := Finset.exists_mem_notMem_of_card_lt_card (hcard.trans_eq hT.symm)
  obtain ⟨p, -, rfl⟩ := mem_image.mp hwT
  exact ⟨_, by simp, hwC⟩

/-- (ii) with the explicit sibling-chain witness. -/
theorem part_ii (n : ℕ) (C : Finset (List Bool)) (hC : ∀ p ∈ C, p.length = n + 1)
    (hcard : C.card < 2 ^ (n + 1)) :
    ∃ w : List Bool, w.length = n + 1 ∧ w ∉ C ∧ ∀ p ∈ C, ¬ PathSurvives (sib w) n p := by
  obtain ⟨w, hw, hwC⟩ := exists_path_notMem n C hcard
  refine ⟨w, hw, hwC, fun p hp hs => ?_⟩
  have := (sib_survives_iff w p n hw (hC p hp)).1 hs
  exact hwC (this ▸ hp)

/-- (ii) as stated. -/
theorem part_ii_exists (n : ℕ) (C : Finset (List Bool)) (hC : ∀ p ∈ C, p.length = n + 1)
    (hcard : C.card < 2 ^ (n + 1)) :
    ∃ d : ℕ → List Bool, ∀ p ∈ C, ¬ PathSurvives d n p := by
  obtain ⟨w, -, -, h⟩ := part_ii n C hC hcard
  exact ⟨sib w, h⟩

/-- The open-loop copy count is exactly `2^(n+1)`. -/
theorem copy_count_exact (n : ℕ) :
    IsLeast {c | ∃ C : Finset (List Bool), (∀ p ∈ C, p.length = n + 1) ∧ C.card = c ∧
      ∀ d : ℕ → List Bool, ∃ p ∈ C, PathSurvives d n p} (2 ^ (n + 1)) := by
  constructor
  · refine ⟨univ.image (fun p : Fin (n + 1) → Bool => List.ofFn p), ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨q, -, rfl⟩ := mem_image.mp hp
      simp
    · rw [card_image_of_injective _ List.ofFn_injective, card_paths]
    · intro d
      obtain ⟨p, hp⟩ := Finset.card_pos.mp (surv_card_pos d n)
      exact ⟨List.ofFn p, mem_image.mpr ⟨p, mem_univ _, rfl⟩, (mem_filter.mp hp).2⟩
  · rintro c ⟨C, hC, rfl, hsurv⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨d, hd⟩ := part_ii_exists n C hC hlt
    obtain ⟨p, hp, hs⟩ := hsurv d
    exact hd p hp hs

/-! ## (iii) Every winning angel is forced onto every path -/

lemma pos_length (σ : Strategy) (d : ℕ → List Bool) : ∀ k, (pos σ d k).length = k
  | 0 => rfl
  | k + 1 => by simp [pos, pos_length σ d k]

lemma pos_take (σ : Strategy) (d : ℕ → List Bool) (k : ℕ) :
    ∀ m, k ≤ m → (pos σ d m).take k = pos σ d k
  | 0, h => by
    obtain rfl : k = 0 := by omega
    rfl
  | m + 1, h => by
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [pos, List.take_append_of_le_length (by rw [pos_length]; omega),
        pos_take σ d k m (by omega)]
    · exact List.take_of_length_le (by rw [pos_length])

/-- (iii): against the sibling chain of `w`, a never-losing angel ends exactly on `w`. -/
theorem forced_onto_path (σ : Strategy)
    (hσ : ∀ (d : ℕ → List Bool) (n : ℕ), ∀ i ≤ n, d i ≠ pos σ d (n + 1))
    (n : ℕ) (w : List Bool) (hw : w.length = n + 1) :
    pos σ (sib w) (n + 1) = w := by
  refine (sib_survives_iff w _ n hw (pos_length _ _ _)).1 ?_
  intro k hk i hi
  rw [pos_take σ _ (k + 1) (n + 1) (by omega)]
  exact hσ (sib w) k i hi

/-- (iii): `d ↦ pos σ d (n+1)` is onto the length-`(n+1)` lists. -/
theorem onto (σ : Strategy)
    (hσ : ∀ (d : ℕ → List Bool) (n : ℕ), ∀ i ≤ n, d i ≠ pos σ d (n + 1)) (n : ℕ) :
    Set.range (fun d => pos σ d (n + 1)) = {w | w.length = n + 1} := by
  ext w
  constructor
  · rintro ⟨d, rfl⟩
    exact pos_length σ d (n + 1)
  · intro hw
    exact ⟨sib w, forced_onto_path σ hσ n w hw⟩

/-! ### The hypothesis of (iii) is satisfiable (proof copied from `AngelBinaryTreeA`) -/

lemma seen_getLast? (d : ℕ → List Bool) (k : ℕ) : (seen d k).getLast? = some (d k) := by
  simp [seen, List.range_succ]

lemma not_both_children (l x : List Bool) (h₁ : l ++ [false] <+: x) (h₂ : l ++ [true] <+: x) :
    False := by
  have hlen : (l ++ [false]).length ≤ (l ++ [true]).length := by simp
  have h := List.prefix_of_prefix_length_le h₁ h₂ hlen
  have heq : l ++ [false] = l ++ [true] := h.eq_of_length (by simp)
  simp at heq

theorem invariant (d : ℕ → List Bool) :
    ∀ k, ∀ i < k, ¬ (pos newestBlockStrategy d k <+: d i) := by
  intro k
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi hpre
    have hstep : pos newestBlockStrategy d (k + 1) =
        pos newestBlockStrategy d k ++
          [decide (pos newestBlockStrategy d k ++ [false] <+: d k)] := by
      simp [pos, newestBlockStrategy, seen_getLast?]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · apply ih i hlt
      exact (List.prefix_append _ _).trans (hstep ▸ hpre)
    · subst heq
      rw [hstep] at hpre
      by_cases hf : pos newestBlockStrategy d i ++ [false] <+: d i
      · simp only [hf, decide_true] at hpre
        exact not_both_children _ _ hf hpre
      · simp only [hf, decide_false] at hpre

theorem winning_exists : ∃ σ : Strategy,
    ∀ (d : ℕ → List Bool) (n : ℕ), ∀ i ≤ n, d i ≠ pos σ d (n + 1) :=
  ⟨newestBlockStrategy, fun d n i hi heq =>
    invariant d (n + 1) i (Nat.lt_succ_of_le hi) (heq ▸ List.prefix_refl _)⟩

theorem newestBlock_onto (n : ℕ) :
    Set.range (fun d => pos newestBlockStrategy d (n + 1)) = {w | w.length = n + 1} :=
  onto newestBlockStrategy (fun d n i hi heq =>
    invariant d (n + 1) i (Nat.lt_succ_of_le hi) (heq ▸ List.prefix_refl _)) n

/-! ## (iv) Fuel -/

section Fuel
variable {ι : Type*} [Fintype ι]

/-- Surviving fraction (as in `SelectionCarnot`). -/
noncomputable def S (q s : ι → ℝ) : ℝ := ∑ i, q i * s i
/-- Post-selection distribution (as in `SelectionCarnot`). -/
noncomputable def post (q s : ι → ℝ) (i : ι) : ℝ := q i * s i / S q s
/-- `D(post ‖ q)` (as in `SelectionCarnot`). -/
noncomputable def KL (q s : ι → ℝ) : ℝ := ∑ i, post q s i * log (post q s i / q i)

lemma term_eq (q s : ι → ℝ) (hq : ∀ i, 0 < q i) (hS : 0 < S q s) (i : ι) :
    post q s i * log (post q s i / q i) = post q s i * (log (s i) - log (S q s)) := by
  unfold post
  by_cases h : s i = 0
  · simp [h]
  · have hqi := (hq i).ne'
    rw [show q i * s i / S q s / q i = s i / S q s by field_simp, log_div h hS.ne']

lemma KL_eq_general (q s : ι → ℝ) (hq : ∀ i, 0 < q i) (hS : 0 < S q s) :
    KL q s = ∑ i, post q s i * log (s i) - log (S q s) := by
  unfold KL
  simp only [term_eq q s hq hS, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have : ∑ i, post q s i = 1 := by
    unfold post; rw [← Finset.sum_div]; exact div_self hS.ne'
  rw [this, one_mul]

lemma truncation_attains (q s : ι → ℝ) (hq : ∀ i, 0 < q i) (hs : ∀ i, s i = 0 ∨ s i = 1)
    (hS : 0 < S q s) : KL q s = log (1 / S q s) := by
  rw [KL_eq_general q s hq hS, one_div, log_inv]
  have : ∑ i, post q s i * log (s i) = 0 :=
    Finset.sum_eq_zero (fun i _ => by rcases hs i with h | h <;> simp [h])
  rw [this]; ring

end Fuel

/-- Uniform distribution `2^-(n+1)` on paths of length `n+1`. -/
noncomputable def qU (n : ℕ) : (Fin (n + 1) → Bool) → ℝ := fun _ => ((2 : ℝ) ^ (n + 1))⁻¹

/-- Survival indicator. -/
noncomputable def sInd (d : ℕ → List Bool) (n : ℕ) : (Fin (n + 1) → Bool) → ℝ :=
  fun p => if PathSurvives d n (List.ofFn p) then 1 else 0

lemma S_eq (d : ℕ → List Bool) (n : ℕ) :
    S (qU n) (sInd d n) = ((surv d n).card : ℝ) / 2 ^ (n + 1) := by
  unfold S qU sInd surv
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  ring

lemma surv_card_le (d : ℕ → List Bool) (n : ℕ) : (surv d n).card ≤ 2 ^ (n + 1) :=
  (card_filter_le _ _).trans_eq (card_paths n)

/-- (iv): `S q s ≥ 2^-(n+1)`. -/
theorem S_ge (d : ℕ → List Bool) (n : ℕ) : ((2 : ℝ) ^ (n + 1))⁻¹ ≤ S (qU n) (sInd d n) := by
  rw [S_eq, inv_eq_one_div]
  have : (1 : ℝ) ≤ (surv d n).card := by exact_mod_cast surv_card_pos d n
  gcongr

lemma S_pos (d : ℕ → List Bool) (n : ℕ) : 0 < S (qU n) (sInd d n) :=
  lt_of_lt_of_le (by positivity) (S_ge d n)

/-- (iv): `KL q s = log (1 / S q s)`. -/
theorem KL_eq_log (d : ℕ → List Bool) (n : ℕ) :
    KL (qU n) (sInd d n) = log (1 / S (qU n) (sInd d n)) :=
  truncation_attains _ _ (fun _ => by unfold qU; positivity)
    (fun p => by unfold sInd; split_ifs <;> simp) (S_pos d n)

theorem KL_eq (d : ℕ → List Bool) (n : ℕ) :
    KL (qU n) (sInd d n) = (n + 1) * log 2 - log ((surv d n).card) := by
  have hc : (0 : ℝ) < (surv d n).card := by exact_mod_cast surv_card_pos d n
  rw [KL_eq_log, S_eq, one_div_div, log_div (by positivity) hc.ne', log_pow]
  push_cast; ring

/-- (iv): `KL q s ≤ (n+1) log 2`. -/
theorem KL_le (d : ℕ → List Bool) (n : ℕ) : KL (qU n) (sInd d n) ≤ (n + 1) * log 2 := by
  rw [KL_eq]
  have : (1 : ℝ) ≤ (surv d n).card := by exact_mod_cast surv_card_pos d n
  have := log_nonneg this
  linarith

/-- (iv): the bound is attained iff exactly one path survives. -/
theorem KL_eq_max_iff (d : ℕ → List Bool) (n : ℕ) :
    KL (qU n) (sInd d n) = (n + 1) * log 2 ↔ (surv d n).card = 1 := by
  rw [KL_eq]
  have hc : (1 : ℝ) ≤ (surv d n).card := by exact_mod_cast surv_card_pos d n
  constructor
  · intro h
    have h0 : log ((surv d n).card : ℝ) = 0 := by linarith
    rcases Real.log_eq_zero.mp h0 with h | h | h
    · linarith
    · exact_mod_cast h
    · linarith
  · intro h
    rw [h]; simp

lemma surv_sib (w : List Bool) (n : ℕ) (hw : w.length = n + 1) : (surv (sib w) n).card = 1 := by
  obtain ⟨p0, hp0⟩ : ∃ p0 : Fin (n + 1) → Bool, List.ofFn p0 = w :=
    ⟨fun i => w[i.1]'(by omega), List.ext_getElem (by simp [hw]) (fun i _ _ => by rw [List.getElem_ofFn])⟩
  rw [Finset.card_eq_one]
  refine ⟨p0, ?_⟩
  ext p
  simp only [surv, mem_filter, mem_univ, true_and, mem_singleton]
  rw [sib_survives_iff w _ n hw (by simp), ← hp0]
  exact ⟨fun h => List.ofFn_injective h, fun h => h ▸ rfl⟩

/-- (iv): sibling chains attain the maximum. -/
theorem sib_attains_max (w : List Bool) (n : ℕ) (hw : w.length = n + 1) :
    KL (qU n) (sInd (sib w) n) = (n + 1) * log 2 :=
  (KL_eq_max_iff _ n).2 (surv_sib w n hw)

/-- (iv): `max_d KL q s = (n+1) log 2`. -/
theorem KL_isGreatest (n : ℕ) :
    IsGreatest (Set.range fun d : ℕ → List Bool => KL (qU n) (sInd d n)) ((n + 1) * log 2) :=
  ⟨⟨sib (List.replicate (n + 1) false), sib_attains_max _ n (by simp)⟩,
    by rintro _ ⟨d, rfl⟩; exact KL_le d n⟩

theorem KL_nonneg (d : ℕ → List Bool) (n : ℕ) : 0 ≤ KL (qU n) (sInd d n) := by
  rw [KL_eq]
  have hc : (1 : ℝ) ≤ (surv d n).card := by exact_mod_cast surv_card_pos d n
  have hle : ((surv d n).card : ℝ) ≤ 2 ^ (n + 1) := by exact_mod_cast surv_card_le d n
  have := log_le_log (by linarith) hle
  rw [log_pow] at this
  push_cast at this
  linarith

/-- (iv): `d ≡ []` kills nothing, so `KL = 0`. -/
theorem nil_attains_min (n : ℕ) : KL (qU n) (sInd (fun _ => []) n) = 0 := by
  have hall : surv (fun _ => []) n = univ := by
    apply Finset.filter_true_of_mem
    intro p _ k hk i _ h
    have := congrArg List.length h
    simp at this
  rw [KL_eq, hall, card_paths]
  push_cast
  rw [log_pow]; push_cast; ring

/-- (iv): `min_d KL q s = 0`. -/
theorem KL_isLeast (n : ℕ) :
    IsLeast (Set.range fun d : ℕ → List Bool => KL (qU n) (sInd d n)) 0 :=
  ⟨⟨fun _ => [], nil_attains_min n⟩, by rintro _ ⟨d, rfl⟩; exact KL_nonneg d n⟩

/-- The exponential of the maximal fuel is the open-loop copy count. -/
theorem exp_max_fuel (n : ℕ) : Real.exp ((n + 1) * log 2) = 2 ^ (n + 1) := by
  rw [show ((n : ℝ) + 1) * log 2 = log (2 ^ (n + 1)) by rw [log_pow]; push_cast; ring,
    exp_log (by positivity)]

end Bridge5B
