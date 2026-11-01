import Mathlib

/-!
# Angel and devil on the infinite rooted binary tree

Game. Nodes are `List Bool`; the root is `[]`; the children of `l` are `l ++ [false]`
and `l ++ [true]`. The devil's play is an arbitrary sequence `d : ℕ → List Bool`.
Turn `n` (for `n = 0, 1, 2, …`): first the devil blocks node `d n`; then the angel,
having seen exactly the blocks `seen d n = [d 0, …, d n]`, moves from its current
node to one of its two children. A strategy is a map `σ : List (List Bool) → Bool`
from the list of blocks seen so far to the chosen child bit; the angel's position
after the moves of turns `0, …, n-1` is `pos σ d n` (with `pos σ d 0 = []`).
The angel loses at turn `n` if the node it moves to is blocked, i.e. lies in
`seen d n`.

PROVED.
* `angel_wins`: there is a strategy `σ` such that for every devil sequence `d` and every
  `n`, the node reached by the move of turn `n`, `pos σ d (n + 1)`, is not in
  `{d 0, …, d n}`.
* `angel_wins_closed_subtree`: the same strategy keeps a stronger invariant: for every
  `n` and every `j < n`, the current node `pos σ d n` is not a prefix of `d j`
  (the closed subtree of the current node contains no block placed so far).
* `root_can_be_blocked`: the reading "the position after `n` moves avoids
  `{d 0, …, d n}`" with `n = 0` fails for every strategy (the devil may block the root
  on turn 0); this is why the target is indexed by the move of turn `n`.

INTERPRETED.
* "After n moves, unblocked (not in {d 0, …, d n})" is read as: the node reached by the
  move of turn `n` (the `(n+1)`-st move, made after the block `d n`) is not in
  `{d 0, …, d n}`. Blocks placed later on nodes the angel has already left are
  irrelevant.
* The strategy sees only the list of blocks so far (its own position is recomputed
  from that list), which is a special case of strategies that also see the position.
* Strategy used: move to `false` unless some block seen so far lies in the closed
  subtree of the `false` child, in which case move to `true`. Under the invariant only
  the newest block can lie below the current node, so this agrees with "move to the
  child whose closed subtree contains fewer blocks".
-/

namespace AngelBinaryTreeB

/-- Nodes of the rooted binary tree. -/
abbrev Node := List Bool

/-- The blocks seen at turn `n`, after the devil's move: `[d 0, …, d n]`. -/
def seen (d : ℕ → Node) (n : ℕ) : List Node := (List.range (n + 1)).map d

/-- An angel strategy: from the blocks seen so far, the bit of the child to move to. -/
abbrev Strategy := List Node → Bool

/-- Angel position after the moves of turns `0, …, n-1`. -/
def pos (σ : Strategy) (d : ℕ → Node) : ℕ → Node
  | 0 => []
  | n + 1 => pos σ d n ++ [σ (seen d n)]

/-- From node `p` with blocks `L`: go to `true` iff some block lies in the closed
subtree of `p ++ [false]`. -/
def choose (p : Node) (L : List Node) : Bool :=
  decide (∃ b ∈ L, p ++ [false] <+: b)

/-- Recompute the angel's position after `k` moves from a list of blocks. -/
def replay (L : List Node) : ℕ → Node
  | 0 => []
  | k + 1 => replay L k ++ [choose (replay L k) (L.take (k + 1))]

/-- The angel strategy. -/
def angel : Strategy := fun L => choose (replay L (L.length - 1)) L

lemma replay_congr : ∀ (k : ℕ) (L M : List Node), L.take k = M.take k →
    replay L k = replay M k
  | 0, _, _, _ => rfl
  | k + 1, L, M, h => by
    have hk : L.take k = M.take k := by
      have := congrArg (List.take k) h
      simpa [List.take_take] using this
    simp only [replay, replay_congr k L M hk, h]

lemma seen_length (d : ℕ → Node) (n : ℕ) : (seen d n).length = n + 1 := by
  simp [seen]

lemma take_seen (d : ℕ → Node) (k n : ℕ) (h : k ≤ n + 1) :
    (seen d n).take k = (List.range k).map d := by
  rw [seen, ← List.map_take, List.take_range, Nat.min_eq_left h]

lemma pos_angel (d : ℕ → Node) : ∀ k, pos angel d k = replay (seen d k) k
  | 0 => rfl
  | k + 1 => by
    have h1 : replay (seen d (k + 1)) k = replay (seen d k) k :=
      replay_congr k _ _ (by rw [take_seen d k (k + 1) (by omega),
        take_seen d k k (by omega)])
    have h2 : (seen d (k + 1)).take (k + 1) = seen d k := by
      rw [take_seen d (k + 1) (k + 1) (by omega)]; rfl
    simp only [pos, replay, angel, seen_length, Nat.add_sub_cancel, pos_angel d k, h1, h2]

lemma pos_angel_succ (d : ℕ → Node) (k : ℕ) :
    pos angel d (k + 1) = pos angel d k ++ [choose (pos angel d k) (seen d k)] := by
  simp only [pos, angel, seen_length, Nat.add_sub_cancel, pos_angel d k]

lemma mem_seen {d : ℕ → Node} {n : ℕ} {b : Node} :
    b ∈ seen d n ↔ ∃ j ≤ n, d j = b := by
  simp [seen]

lemma not_both (p r s : Node) : p ++ [true] ++ r ≠ p ++ [false] ++ s := by
  intro h
  simp only [List.append_assoc, List.append_cancel_left_eq, List.singleton_append,
    List.cons.injEq] at h
  exact Bool.noConfusion h.1

lemma prefix_excl {p b : Node} (ht : p ++ [true] <+: b) (hf : p ++ [false] <+: b) :
    False := by
  obtain ⟨r, hr⟩ := ht
  obtain ⟨s, hs⟩ := hf
  exact not_both p r s (hr.trans hs.symm)

/-- The closed subtree of the current node contains no block placed before the
current turn. -/
theorem angel_wins_closed_subtree (d : ℕ → Node) :
    ∀ n, ∀ j < n, ¬ pos angel d n <+: d j
  | 0 => fun j hj => absurd hj (Nat.not_lt_zero j)
  | k + 1 => by
    intro j hj hpre
    have IH := angel_wins_closed_subtree d k
    rw [pos_angel_succ] at hpre
    set p := pos angel d k
    have hp : p <+: d j := (List.prefix_append p _).trans hpre
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | rfl
    · exact IH j hjk hp
    · cases hc : choose p (seen d j) with
      | false =>
        rw [hc] at hpre
        have : ¬ ∃ b ∈ seen d j, p ++ [false] <+: b := by
          simpa [choose] using hc
        exact this ⟨d j, mem_seen.mpr ⟨j, le_rfl, rfl⟩, hpre⟩
      | true =>
        rw [hc] at hpre
        have : ∃ b ∈ seen d j, p ++ [false] <+: b := by
          simpa [choose] using hc
        obtain ⟨b, hb, hfb⟩ := this
        obtain ⟨i, hi, rfl⟩ := mem_seen.mp hb
        rcases Nat.lt_or_eq_of_le hi with hik | rfl
        · exact IH i hik ((List.prefix_append p _).trans hfb)
        · exact prefix_excl hpre hfb

/-- The angel never loses: the node reached by the move of turn `n` is not among the
blocks `d 0, …, d n`. -/
theorem angel_wins :
    ∃ σ : Strategy, ∀ (d : ℕ → Node) (n : ℕ), pos σ d (n + 1) ∉ seen d n := by
  refine ⟨angel, fun d n hmem => ?_⟩
  obtain ⟨j, hj, hdj⟩ := mem_seen.mp hmem
  exact angel_wins_closed_subtree d (n + 1) j (Nat.lt_succ_of_le hj)
    (hdj ▸ List.prefix_refl _)

/-- Under the literal indexing "position after `n` moves avoids `{d 0, …, d n}`",
`n = 0` already fails: the devil may block the root on turn 0. -/
theorem root_can_be_blocked :
    ∀ σ : Strategy, ∃ d : ℕ → Node, pos σ d 0 ∈ seen d 0 :=
  fun _ => ⟨fun _ => [], by simp [pos, seen]⟩

end AngelBinaryTreeB
