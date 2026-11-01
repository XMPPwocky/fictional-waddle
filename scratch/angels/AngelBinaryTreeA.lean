import Mathlib

/-!
# Angel and devil on the infinite rooted binary tree

## The game

* Nodes are `List Bool`; the root is `[]`; the children of `l` are `l ++ [false]` and
  `l ++ [true]`. The closed subtree of `c` is `{x | c <+: x}` (prefix order).
* The devil is an arbitrary sequence `d : ℕ → List Bool`; `d k` may be any node.
* Turn `k = 0, 1, 2, …`: first the devil blocks `d k`; then the angel, at `pos k`
  (with `pos 0 = []`), moves to a child of `pos k`. After turn `k` the blocked set is
  `{d 0, …, d k}`. The angel loses at turn `k` if the child it moves to lies in
  `{d 0, …, d k}` (in particular if both children are blocked).
* A strategy `σ : List Bool → List (List Bool) → Bool` maps the current node and the list
  `[d 0, …, d k]` of blocks seen so far to the chosen child direction. Thus the move at
  turn `k` depends only on `d 0, …, d k`, never on future devil moves.
* `pos σ d (k+1) = pos σ d k ++ [σ (pos σ d k) [d 0, …, d k]]`.

"The angel position after `n` moves" is read as the position after the move of turn `n`,
i.e. `pos σ d (n+1)`, which must avoid `{d 0, …, d n}`.

## PROVED

* `angel_wins`: there is a strategy `σ` such that for every devil sequence `d` and every
  `n`, `pos σ d (n+1)` is a child of `pos σ d n` and `pos σ d (n+1) ∉ {d 0, …, d n}`
  (stated both as `∀ i ≤ n, d i ≠ pos σ d (n+1)` and as non-membership in the list
  `(List.range (n+1)).map d`).
* `invariant`: for the strategy used, before devil move `k`, no block `d i` (`i < k`) lies in
  the closed subtree of `pos k`; in particular none lies in either closed child subtree.
* `literal_index_fails`: under the alternative reading `pos σ d n ∉ {d 0, …, d n}` the claim
  is false for every strategy (the devil blocks the root at turn 0), so that reading is not
  what is proved.

## INTERPRETED

* The strategy used is: move to `l ++ [true]` iff the newest block `d k` lies in the closed
  subtree of `l ++ [false]`, else move to `l ++ [false]`. Under the invariant, the
  child-subtree block counts are each at most one and this rule is exactly
  "move to the child whose closed subtree contains fewer blocks" (ties to `false`);
  the proof uses the newest-block form directly.
-/

namespace AngelBinaryTreeA

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

/-- Invariant: before devil move `k`, no earlier block lies in the closed subtree of the
angel's node. -/
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

/-- Consequence of the invariant: no earlier block lies in either closed child subtree. -/
theorem invariant_children (d : ℕ → List Bool) (k : ℕ) (b : Bool) :
    ∀ i < k, ¬ (pos newestBlockStrategy d k ++ [b] <+: d i) := fun i hi h =>
  invariant d k i hi ((List.prefix_append _ _).trans h)

/-- The angel has a strategy that never loses. -/
theorem angel_wins : ∃ σ : Strategy, ∀ (d : ℕ → List Bool) (n : ℕ),
    (∃ b : Bool, pos σ d (n + 1) = pos σ d n ++ [b]) ∧
    (∀ i ≤ n, d i ≠ pos σ d (n + 1)) ∧
    pos σ d (n + 1) ∉ (List.range (n + 1)).map d := by
  refine ⟨newestBlockStrategy, fun d n => ⟨⟨_, rfl⟩, ?_, ?_⟩⟩
  · intro i hi heq
    exact invariant d (n + 1) i (Nat.lt_succ_of_le hi) (heq ▸ List.prefix_refl _)
  · intro hmem
    obtain ⟨i, hi, heq⟩ := List.mem_map.mp hmem
    rw [List.mem_range] at hi
    exact invariant d (n + 1) i hi (heq ▸ List.prefix_refl _)

/-- The alternative index reading `pos σ d n ∉ {d 0, …, d n}` fails for every strategy. -/
theorem literal_index_fails : ¬ ∃ σ : Strategy, ∀ (d : ℕ → List Bool) (n : ℕ),
    ∀ i ≤ n, d i ≠ pos σ d n := by
  rintro ⟨σ, h⟩
  exact h (fun _ => []) 0 0 le_rfl rfl

end AngelBinaryTreeA
