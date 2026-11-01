import Mathlib

/-!
# Every winning angel is forced onto every path; the open-loop copy count is 2^(n+1)

Setting: the angel/devil game on the rooted binary tree of
`lean/scratch/angels/AngelBinaryTreeA.lean`; the definitions `Strategy`, `seen`, `pos`,
`newestBlockStrategy` are repeated verbatim. The selection quantities `S`, `post`, `KL` are
repeated verbatim from `lean/scratch/refrigerator/SelectionCarnot.lean`.

`PathSurvives d n p :≡ ∀ k ≤ n, ∀ i ≤ k, d i ≠ p.take (k+1)`: an open-loop walker that follows
the fixed path `p` is never standing on a block placed at or before the current turn.
The sibling chain of `w` is `sib w k = w.take k ++ [!(w.getD k false)]`, which for `k < |w|`
is `w.take k ++ [!(w.get k)]` (`sib_apply`).

## PROVED

* (i) `part_i`, `part_i_int`: for all `d n`,
  `#{p : Fin (n+1) → Bool | PathSurvives d n (List.ofFn p)} ≥ 2^(n+1) − killSum d n ≥ 1`, where
  `killSum d n = Σ_{i ≤ n, i+1 ≤ |d i| ≤ n+1} 2^(n+1−|d i|)` (in `ℤ`; the `ℕ` form is
  `2^(n+1) ≤ card + killSum` and `killSum + 1 ≤ 2^(n+1)`).
* (ii) `part_ii`: for `C : Finset (List Bool)` with all members of length `n+1` and
  `C.card < 2^(n+1)` there is `d` with `∀ p ∈ C, ¬ PathSurvives d n p`; `part_ii_witness`: for
  any `w ∉ C` of length `n+1`, `d = sib w` works. `sib_survives_iff`: for lists of length `n+1`,
  `PathSurvives (sib w) n p ↔ p = w`.
* `open_loop_copy_count`: the least size of a set of length-`(n+1)` paths containing a survivor
  against every devil is exactly `2^(n+1)` (`IsLeast`).
* (iii) `part_iii`: if `σ` satisfies `∀ d n, ∀ i ≤ n, d i ≠ pos σ d (n+1)`, then for every `n`
  and every `w` of length `n+1`, `pos σ (sib w) (n+1) = w`; `part_iii_onto`:
  `Set.range (fun d => pos σ d (n+1)) = {w | w.length = n+1}`. `newestBlock_wins` shows the
  hypothesis is satisfiable, and `newestBlock_onto` instantiates the conclusion.
* (iv) With `unif n = fun _ => 2^−(n+1)` on `Fin (n+1) → Bool` and `survInd d n` the survival
  indicator: `S_ge` (`S ≥ 2^−(n+1)`), `KL_eq_log` (`KL = log (1/S)`), `KL_le`
  (`KL ≤ (n+1) log 2`), `KL_nonneg`, `KL_eq_max_iff` (`KL = (n+1) log 2 ↔` exactly one path
  survives, as `card = 1` and as `∃!`), `KL_sib` (sibling chains attain it), `KL_max`
  (`IsGreatest` of the range over `d` is `(n+1) log 2`), `KL_min` (`IsLeast` is `0`, attained
  by `d ≡ []`), `exp_max_fuel` (`exp ((n+1) log 2) = 2^(n+1)`).

## INTERPRETED

* The open-loop copies are the paths `p`; a devil `d` is fixed in advance and the copies do not
  react to it. "Fuel" is `KL (unif n) (survInd d n) = log (1/S)`, the selection cost of keeping
  only surviving copies. No claim is made about shared clocks or bargaining.
-/

namespace Bridge5A
open Finset Real

/-! ### Game setting (verbatim from `AngelBinaryTreeA`) -/

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

/-- The newest-block strategy satisfies the winning hypothesis of (iii). -/
theorem newestBlock_wins :
    ∀ (d : ℕ → List Bool) (n : ℕ), ∀ i ≤ n, d i ≠ pos newestBlockStrategy d (n + 1) :=
  fun d n i hi heq => invariant d (n + 1) i (Nat.lt_succ_of_le hi) (heq ▸ List.prefix_refl _)

/-! ### Open-loop survival -/

/-- The fixed path `p` survives the devil `d` through turn `n`. -/
def PathSurvives (d : ℕ → List Bool) (n : ℕ) (p : List Bool) : Prop :=
  ∀ k ≤ n, ∀ i ≤ k, d i ≠ p.take (k + 1)

instance (d : ℕ → List Bool) (n : ℕ) (p : List Bool) : Decidable (PathSurvives d n p) := by
  unfold PathSurvives; infer_instance

/-- Surviving paths of length `n+1`, indexed by `Fin (n+1) → Bool`. -/
def survivors (d : ℕ → List Bool) (n : ℕ) : Finset (Fin (n + 1) → Bool) :=
  univ.filter fun p => PathSurvives d n (List.ofFn p)

/-- Indices `i ≤ n` with `i + 1 ≤ |d i| ≤ n + 1`. -/
def killIdx (d : ℕ → List Bool) (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter fun i => i + 1 ≤ (d i).length ∧ (d i).length ≤ n + 1

/-- `Σ_{i ≤ n, i+1 ≤ |d i| ≤ n+1} 2^(n+1−|d i|)`. -/
def killSum (d : ℕ → List Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ killIdx d n, 2 ^ (n + 1 - (d i).length)

lemma card_univ_paths (n : ℕ) : (univ : Finset (Fin (n + 1) → Bool)).card = 2 ^ (n + 1) := by
  simp

lemma prefix_card (n : ℕ) (x : List Bool) (hx : x.length ≤ n + 1) :
    (univ.filter fun p : Fin (n + 1) → Bool => x <+: List.ofFn p).card
      ≤ 2 ^ (n + 1 - x.length) := by
  have key : (univ.filter fun p : Fin (n + 1) → Bool => x <+: List.ofFn p).card ≤
      (univ : Finset (Fin (n + 1 - x.length) → Bool)).card := by
    refine Finset.card_le_card_of_injOn
      (fun p j => p ⟨x.length + j.1, by omega⟩) (fun _ _ => by simp) ?_
    intro p hp p' hp' heq
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp hp'
    funext t
    obtain ⟨t, htlt⟩ := t
    by_cases ht : t < x.length
    · have h1 := hp.getElem ht
      have h2 := hp'.getElem ht
      simp only [List.getElem_ofFn] at h1 h2
      rw [← h1, h2]
    · have h := congrFun heq ⟨t - x.length, by omega⟩
      have e : x.length + (t - x.length) = t := by omega
      simp only [e] at h
      exact h
  simpa using key

lemma dead_mem (d : ℕ → List Bool) (n : ℕ) (p : Fin (n + 1) → Bool)
    (h : ¬ PathSurvives d n (List.ofFn p)) : ∃ i ∈ killIdx d n, d i <+: List.ofFn p := by
  unfold PathSurvives at h
  push Not at h
  obtain ⟨k, hk, i, hi, he⟩ := h
  have hlen : (d i).length = k + 1 := by
    rw [he, List.length_take, List.length_ofFn]; omega
  refine ⟨i, ?_, he ▸ List.take_prefix _ _⟩
  simp only [killIdx, mem_filter, mem_range]
  omega

lemma geom (m : ℕ) : ∑ j ∈ range m, 2 ^ j + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, pow_succ]; omega

lemma geom_rev (m : ℕ) : ∑ i ∈ range (m + 1), 2 ^ (m - i) + 1 = 2 ^ (m + 1) := by
  have h := Finset.sum_range_reflect (fun j => 2 ^ j) (m + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [h]
  exact geom (m + 1)

/-- (i), `ℕ` form. -/
theorem part_i (d : ℕ → List Bool) (n : ℕ) :
    2 ^ (n + 1) ≤ (survivors d n).card + killSum d n ∧ killSum d n + 1 ≤ 2 ^ (n + 1) := by
  constructor
  · have hsplit := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin (n + 1) → Bool))) (fun p => PathSurvives d n (List.ofFn p))
    rw [card_univ_paths] at hsplit
    have hdead : (univ.filter fun p : Fin (n + 1) → Bool =>
        ¬ PathSurvives d n (List.ofFn p)).card ≤ killSum d n := by
      calc _ ≤ ((killIdx d n).biUnion fun i =>
              univ.filter fun p : Fin (n + 1) → Bool => d i <+: List.ofFn p).card := by
            apply card_le_card
            intro p hp
            simp only [mem_filter, mem_univ, true_and] at hp
            obtain ⟨i, hi, hpre⟩ := dead_mem d n p hp
            exact mem_biUnion.2 ⟨i, hi, by simp only [mem_filter, mem_univ, true_and]; exact hpre⟩
        _ ≤ ∑ i ∈ killIdx d n,
              (univ.filter fun p : Fin (n + 1) → Bool => d i <+: List.ofFn p).card :=
            card_biUnion_le
        _ ≤ killSum d n := by
            apply sum_le_sum
            intro i hi
            simp only [killIdx, mem_filter] at hi
            exact prefix_card n (d i) hi.2.2
    unfold survivors
    omega
  · have h1 : killSum d n ≤ ∑ i ∈ range (n + 1), 2 ^ (n - i) := by
      calc killSum d n ≤ ∑ i ∈ killIdx d n, 2 ^ (n - i) := by
            apply sum_le_sum
            intro i hi
            simp only [killIdx, mem_filter, mem_range] at hi
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)
    have h2 := geom_rev n
    omega

/-- (i), as stated: `#survivors ≥ 2^(n+1) − killSum ≥ 1` in `ℤ`. -/
theorem part_i_int (d : ℕ → List Bool) (n : ℕ) :
    (2 : ℤ) ^ (n + 1) - killSum d n ≤ (survivors d n).card ∧
      1 ≤ (2 : ℤ) ^ (n + 1) - killSum d n := by
  obtain ⟨h1, h2⟩ := part_i d n
  have h1' := (Nat.cast_le (α := ℤ)).2 h1
  have h2' := (Nat.cast_le (α := ℤ)).2 h2
  push_cast at h1' h2'
  constructor <;> linarith

lemma survivors_card_pos (d : ℕ → List Bool) (n : ℕ) : 1 ≤ (survivors d n).card := by
  have := part_i d n
  omega

lemma survivors_card_le (d : ℕ → List Bool) (n : ℕ) : (survivors d n).card ≤ 2 ^ (n + 1) :=
  (card_filter_le _ _).trans (card_univ_paths n).le

/-! ### Sibling chains -/

/-- The sibling chain of `w`: at turn `k` block the sibling of `w.take (k+1)`. -/
def sib (w : List Bool) : ℕ → List Bool := fun k => w.take k ++ [!(w.getD k false)]

lemma sib_apply (w : List Bool) (k : ℕ) (hk : k < w.length) :
    sib w k = w.take k ++ [!(w.get ⟨k, hk⟩)] := by
  simp [sib, List.getElem?_eq_getElem hk]

lemma sib_survives (w : List Bool) (n : ℕ) (hw : w.length = n + 1) :
    PathSurvives (sib w) n w := by
  intro k hk i hi heq
  have hlen := congrArg List.length heq
  simp only [sib, List.length_append, List.length_take, List.length_singleton] at hlen
  have hik : i = k := by omega
  subst hik
  have hlt : i < w.length := by omega
  rw [List.take_add_one, List.getElem?_eq_getElem hlt] at heq
  simp only [sib, List.getD_eq_getElem _ _ hlt, Option.toList_some] at heq
  have h := List.append_cancel_left heq
  simp at h

lemma dies_of_ne (w p : List Bool) (n : ℕ) (hw : w.length = n + 1) (hp : p.length = n + 1)
    (hne : p ≠ w) : ¬ PathSurvives (sib w) n p := by
  classical
  have hex : ∃ j, p.getD j false ≠ w.getD j false := by
    by_contra hall
    push Not at hall
    apply hne
    apply List.ext_getElem (by omega)
    intro j h1 h2
    have := hall j
    rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
  obtain ⟨k, hk, hmin⟩ : ∃ k, p.getD k false ≠ w.getD k false ∧
      ∀ j < k, ¬ (p.getD j false ≠ w.getD j false) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hkn : k ≤ n := by
    by_contra h
    apply hk
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  have htake : p.take k = w.take k := by
    apply List.ext_getElem (by simp only [List.length_take]; omega)
    intro j h1 h2
    simp only [List.getElem_take]
    have hj : j < k := by simp only [List.length_take] at h1; omega
    have := hmin j hj
    push Not at this
    rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this
  intro hsurv
  apply hsurv k hkn k le_rfl
  have hpk : k < p.length := by omega
  rw [List.take_add_one, List.getElem?_eq_getElem hpk, htake]
  simp only [sib, Option.toList_some]
  rw [List.getD_eq_getElem _ _ hpk] at hk
  congr 2
  generalize p[k] = a at hk ⊢
  generalize w.getD k false = b at hk ⊢
  cases a <;> cases b <;> simp_all

/-- For lists of length `n+1`, the sibling chain of `w` lets exactly `w` survive. -/
theorem sib_survives_iff (w : List Bool) (n : ℕ) (hw : w.length = n + 1) (p : List Bool)
    (hp : p.length = n + 1) : PathSurvives (sib w) n p ↔ p = w := by
  constructor
  · intro h
    by_contra hne
    exact dies_of_ne w p n hw hp hne h
  · rintro rfl
    exact sib_survives p n hw

/-! ### (ii) Fewer than `2^(n+1)` open-loop copies can all be killed -/

/-- (ii), explicit witness: any `w ∉ C` of length `n+1` gives the killing devil `sib w`. -/
theorem part_ii_witness (n : ℕ) (C : Finset (List Bool)) (hC : ∀ p ∈ C, p.length = n + 1)
    (w : List Bool) (hw : w.length = n + 1) (hwC : w ∉ C) :
    ∀ p ∈ C, ¬ PathSurvives (sib w) n p := by
  intro p hp hs
  have := (sib_survives_iff w n hw p (hC p hp)).1 hs
  exact hwC (this ▸ hp)

theorem exists_not_mem (n : ℕ) (C : Finset (List Bool)) (hcard : C.card < 2 ^ (n + 1)) :
    ∃ w : List Bool, w.length = n + 1 ∧ w ∉ C := by
  by_contra h
  push Not at h
  have hsub : (univ : Finset (Fin (n + 1) → Bool)).image List.ofFn ⊆ C := by
    intro x hx
    obtain ⟨f, -, rfl⟩ := mem_image.1 hx
    exact h _ (by simp)
  have := card_le_card hsub
  rw [card_image_of_injective _ List.ofFn_injective, card_univ_paths] at this
  omega

/-- (ii). -/
theorem part_ii (n : ℕ) (C : Finset (List Bool)) (hC : ∀ p ∈ C, p.length = n + 1)
    (hcard : C.card < 2 ^ (n + 1)) : ∃ d : ℕ → List Bool, ∀ p ∈ C, ¬ PathSurvives d n p := by
  obtain ⟨w, hw, hwC⟩ := exists_not_mem n C hcard
  exact ⟨sib w, part_ii_witness n C hC w hw hwC⟩

/-- The least number of length-`(n+1)` open-loop copies that always contain a survivor is
exactly `2^(n+1)`. -/
theorem open_loop_copy_count (n : ℕ) :
    IsLeast {m : ℕ | ∃ C : Finset (List Bool), (∀ p ∈ C, p.length = n + 1) ∧ C.card = m ∧
      ∀ d : ℕ → List Bool, ∃ p ∈ C, PathSurvives d n p} (2 ^ (n + 1)) := by
  constructor
  · refine ⟨(univ : Finset (Fin (n + 1) → Bool)).image List.ofFn, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨f, -, rfl⟩ := mem_image.1 hp
      simp
    · rw [card_image_of_injective _ List.ofFn_injective, card_univ_paths]
    · intro d
      obtain ⟨f, hf⟩ := Finset.card_pos.1 (survivors_card_pos d n)
      simp only [survivors, mem_filter, mem_univ, true_and] at hf
      exact ⟨List.ofFn f, mem_image.2 ⟨f, mem_univ _, rfl⟩, hf⟩
  · rintro m ⟨C, hC, rfl, hsurv⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨d, hd⟩ := part_ii n C hC hlt
    obtain ⟨p, hp, hs⟩ := hsurv d
    exact hd p hp hs

/-! ### (iii) A winning angel is forced onto every path -/

lemma pos_length (σ : Strategy) (d : ℕ → List Bool) (k : ℕ) : (pos σ d k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pos, ih]

lemma pos_prefix (σ : Strategy) (d : ℕ → List Bool) {k m : ℕ} (h : k ≤ m) :
    pos σ d k <+: pos σ d m := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih => exact ih.trans (List.prefix_append _ _)

lemma pos_take (σ : Strategy) (d : ℕ → List Bool) {k n : ℕ} (h : k ≤ n) :
    (pos σ d (n + 1)).take (k + 1) = pos σ d (k + 1) := by
  have := pos_prefix σ d (Nat.succ_le_succ h)
  rw [List.prefix_iff_eq_take, pos_length] at this
  exact this.symm

/-- A winning angel's actual path survives as an open-loop path. -/
theorem winning_survives (σ : Strategy)
    (hσ : ∀ (d : ℕ → List Bool) (n : ℕ), ∀ i ≤ n, d i ≠ pos σ d (n + 1))
    (d : ℕ → List Bool) (n : ℕ) : PathSurvives d n (pos σ d (n + 1)) := by
  intro k hk i hi
  rw [pos_take σ d hk]
  exact hσ d k i hi

/-- (iii). -/
theorem part_iii (σ : Strategy)
    (hσ : ∀ (d : ℕ → List Bool) (n : ℕ), ∀ i ≤ n, d i ≠ pos σ d (n + 1))
    (n : ℕ) (w : List Bool) (hw : w.length = n + 1) : pos σ (sib w) (n + 1) = w :=
  (sib_survives_iff w n hw _ (pos_length _ _ _)).1 (winning_survives σ hσ _ n)

/-- (iii), onto form. -/
theorem part_iii_onto (σ : Strategy)
    (hσ : ∀ (d : ℕ → List Bool) (n : ℕ), ∀ i ≤ n, d i ≠ pos σ d (n + 1)) (n : ℕ) :
    Set.range (fun d : ℕ → List Bool => pos σ d (n + 1)) = {w | w.length = n + 1} := by
  ext w
  constructor
  · rintro ⟨d, rfl⟩
    exact pos_length σ d (n + 1)
  · intro hw
    exact ⟨sib w, part_iii σ hσ n w hw⟩

theorem newestBlock_onto (n : ℕ) :
    Set.range (fun d : ℕ → List Bool => pos newestBlockStrategy d (n + 1)) =
      {w | w.length = n + 1} :=
  part_iii_onto newestBlockStrategy newestBlock_wins n

/-! ### (iv) Selection fuel (definitions verbatim from `SelectionCarnot`) -/

section Fuel
variable {ι : Type*} [Fintype ι]

noncomputable def S (q s : ι → ℝ) : ℝ := ∑ i, q i * s i
noncomputable def post (q s : ι → ℝ) (i : ι) : ℝ := q i * s i / S q s
noncomputable def KL (q s : ι → ℝ) : ℝ := ∑ i, post q s i * log (post q s i / q i)

lemma term_eq (q s : ι → ℝ) (hq : ∀ i, 0 < q i) (hS : 0 < S q s) (i : ι) :
    post q s i * log (post q s i / q i) = post q s i * (log (s i) - log (S q s)) := by
  unfold post
  by_cases h : s i = 0
  · simp [h]
  · have hqi := (hq i).ne'
    rw [show q i * s i / S q s / q i = s i / S q s by field_simp, log_div h hS.ne']

lemma KL_eq (q s : ι → ℝ) (hq : ∀ i, 0 < q i) (hS : 0 < S q s) :
    KL q s = ∑ i, post q s i * log (s i) - log (S q s) := by
  unfold KL
  simp only [term_eq q s hq hS, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have : ∑ i, post q s i = 1 := by
    unfold post; rw [← Finset.sum_div]; exact div_self hS.ne'
  rw [this, one_mul]

theorem truncation_attains (q s : ι → ℝ) (hq : ∀ i, 0 < q i) (hs : ∀ i, s i = 0 ∨ s i = 1)
    (hS : 0 < S q s) : KL q s = log (1 / S q s) := by
  rw [KL_eq q s hq hS, one_div, log_inv]
  have : ∑ i, post q s i * log (s i) = 0 :=
    Finset.sum_eq_zero (fun i _ => by rcases hs i with h | h <;> simp [h])
  rw [this]; ring

end Fuel

/-- Uniform distribution `2^−(n+1)` on paths of length `n+1`. -/
noncomputable def unif (n : ℕ) : (Fin (n + 1) → Bool) → ℝ := fun _ => ((2 : ℝ) ^ (n + 1))⁻¹

/-- Survival indicator of the devil `d` through turn `n`. -/
noncomputable def survInd (d : ℕ → List Bool) (n : ℕ) : (Fin (n + 1) → Bool) → ℝ :=
  fun p => if PathSurvives d n (List.ofFn p) then 1 else 0

lemma S_eq (d : ℕ → List Bool) (n : ℕ) :
    S (unif n) (survInd d n) = (survivors d n).card / (2 : ℝ) ^ (n + 1) := by
  simp only [S, unif, survInd, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, survivors,
    div_eq_mul_inv]

theorem S_ge (d : ℕ → List Bool) (n : ℕ) :
    ((2 : ℝ) ^ (n + 1))⁻¹ ≤ S (unif n) (survInd d n) := by
  rw [S_eq, inv_eq_one_div]
  gcongr
  exact_mod_cast survivors_card_pos d n

theorem KL_eq_log (d : ℕ → List Bool) (n : ℕ) :
    KL (unif n) (survInd d n) = log (1 / S (unif n) (survInd d n)) := by
  apply truncation_attains
  · intro i; simp only [unif]; positivity
  · intro i; simp only [survInd]; split_ifs <;> simp
  · exact lt_of_lt_of_le (by positivity) (S_ge d n)

lemma KL_formula (d : ℕ → List Bool) (n : ℕ) :
    KL (unif n) (survInd d n) = (n + 1) * log 2 - log ((survivors d n).card : ℝ) := by
  have hN : (0 : ℝ) < (survivors d n).card := by exact_mod_cast survivors_card_pos d n
  rw [KL_eq_log, S_eq, one_div, inv_div, log_div (by positivity) hN.ne', log_pow]
  push_cast
  ring

theorem KL_le (d : ℕ → List Bool) (n : ℕ) : KL (unif n) (survInd d n) ≤ (n + 1) * log 2 := by
  rw [KL_formula]
  have : 0 ≤ log ((survivors d n).card : ℝ) :=
    Real.log_nonneg (by exact_mod_cast survivors_card_pos d n)
  linarith

theorem KL_nonneg (d : ℕ → List Bool) (n : ℕ) : 0 ≤ KL (unif n) (survInd d n) := by
  rw [KL_formula]
  have hN : (0 : ℝ) < (survivors d n).card := by exact_mod_cast survivors_card_pos d n
  have hle : ((survivors d n).card : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
    exact_mod_cast survivors_card_le d n
  have := Real.log_le_log hN hle
  rw [log_pow] at this
  push_cast at this
  linarith

lemma card_eq_one_iff (d : ℕ → List Bool) (n : ℕ) :
    (survivors d n).card = 1 ↔ ∃! p : Fin (n + 1) → Bool, PathSurvives d n (List.ofFn p) := by
  rw [Finset.card_eq_one]
  simp only [Finset.eq_singleton_iff_unique_mem, survivors, mem_filter, mem_univ, true_and]
  exact Iff.rfl

/-- Maximal fuel is attained iff exactly one path survives. -/
theorem KL_eq_max_iff (d : ℕ → List Bool) (n : ℕ) :
    KL (unif n) (survInd d n) = (n + 1) * log 2 ↔ (survivors d n).card = 1 := by
  rw [KL_formula]
  constructor
  · intro h
    have h0 : log ((survivors d n).card : ℝ) = 0 := by linarith
    have hpos := survivors_card_pos d n
    rcases Real.log_eq_zero.1 h0 with h | h | h
    · have : (survivors d n).card = 0 := by exact_mod_cast h
      omega
    · exact_mod_cast h
    · have : (0 : ℝ) ≤ (survivors d n).card := Nat.cast_nonneg _
      linarith
  · intro h
    rw [h]
    simp

theorem KL_eq_max_iff_unique (d : ℕ → List Bool) (n : ℕ) :
    KL (unif n) (survInd d n) = (n + 1) * log 2 ↔
      ∃! p : Fin (n + 1) → Bool, PathSurvives d n (List.ofFn p) := by
  rw [KL_eq_max_iff, card_eq_one_iff]

lemma sib_unique (w : List Bool) (n : ℕ) (hw : w.length = n + 1) :
    ∃! p : Fin (n + 1) → Bool, PathSurvives (sib w) n (List.ofFn p) := by
  obtain ⟨f, hf⟩ : ∃ f : Fin (n + 1) → Bool, List.ofFn f = w :=
    ⟨fun j => w[j.1]'(by omega), by
      apply List.ext_getElem (by simp [hw])
      intro j h1 h2
      rw [List.getElem_ofFn]⟩
  refine ⟨f, ?_, ?_⟩
  · show PathSurvives (sib w) n (List.ofFn f)
    rw [hf]; exact sib_survives w n hw
  · intro g hg
    have := (sib_survives_iff w n hw _ (List.length_ofFn)).1 hg
    exact List.ofFn_injective (this.trans hf.symm)

/-- Sibling chains attain the maximal fuel. -/
theorem KL_sib (w : List Bool) (n : ℕ) (hw : w.length = n + 1) :
    KL (unif n) (survInd (sib w) n) = (n + 1) * log 2 :=
  (KL_eq_max_iff_unique _ n).2 (sib_unique w n hw)

/-- `max_d KL = (n+1) log 2`. -/
theorem KL_max (n : ℕ) :
    IsGreatest (Set.range fun d : ℕ → List Bool => KL (unif n) (survInd d n))
      ((n + 1) * log 2) :=
  ⟨⟨sib (List.replicate (n + 1) false), KL_sib _ n (List.length_replicate)⟩,
    by rintro _ ⟨d, rfl⟩; exact KL_le d n⟩

lemma nil_kills_nothing (n : ℕ) (p : Fin (n + 1) → Bool) :
    PathSurvives (fun _ => []) n (List.ofFn p) := by
  intro k hk i _ h
  have := congrArg List.length h
  simp only [List.length_nil, List.length_take, List.length_ofFn] at this
  omega

/-- `min_d KL = 0`, attained by `d ≡ []`. -/
theorem KL_min (n : ℕ) :
    IsLeast (Set.range fun d : ℕ → List Bool => KL (unif n) (survInd d n)) 0 := by
  refine ⟨⟨fun _ => [], ?_⟩, by rintro _ ⟨d, rfl⟩; exact KL_nonneg d n⟩
  show KL (unif n) (survInd (fun _ => []) n) = 0
  have hcard : (survivors (fun _ => []) n).card = 2 ^ (n + 1) := by
    rw [← card_univ_paths n]
    congr 1
    exact Finset.filter_true_of_mem (fun p _ => nil_kills_nothing n p)
  rw [KL_formula, hcard]
  push_cast
  rw [log_pow]
  push_cast
  ring

/-- `exp (max fuel) = 2^(n+1)`, the open-loop copy count. -/
theorem exp_max_fuel (n : ℕ) : Real.exp ((n + 1) * log 2) = 2 ^ (n + 1) := by
  rw [show ((n : ℝ) + 1) * log 2 = log ((2 : ℝ) ^ (n + 1)) by rw [log_pow]; push_cast; ring,
    Real.exp_log (by positivity)]

end Bridge5A
