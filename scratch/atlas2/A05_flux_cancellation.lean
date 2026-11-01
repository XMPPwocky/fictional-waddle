import Mathlib

/-!
# A05 — Attention-flux cancellation

A *path* is a `List α` of cells (`α` any type with `DecidableEq`). Consecutive cells are
allowed to be equal (a self-step counts as both an exit and an entry of that cell, so it
cancels and does not affect any divergence).

The steps of a path `p` are the pairs `(p[i], p[i+1])`, realised as `p.zip p.tail`.

* `exits c p`   = number of steps whose source is `c`  (= #{i < length-1 | p[i] = c}).
* `entries c p` = number of steps whose target is `c`  (= #{i < length-1 | p[i+1] = c}).
* `divergence c p = exits c p - entries c p : ℤ`.

**Proved in this file (no `sorry`):** for a nonempty path,
`divergence c p = [c = head] - [c = last]`, plus the corollaries listed below.

**Interpretation (not proved, just the reading):** a path through cells is a unit "flux"
line; every interior visit is matched by an entry and an exit, so the only sources/sinks of
flux are the path endpoints. Closed paths (head = last) are divergence-free.
-/

set_option linter.unusedSectionVars false

namespace A05

variable {α : Type*} [DecidableEq α]

/-- The steps of a path: consecutive pairs `(p[i], p[i+1])`. -/
def steps (p : List α) : List (α × α) := p.zip p.tail

/-- Number of steps leaving cell `c`. -/
def exits (c : α) (p : List α) : ℕ := (steps p).countP (fun s => s.1 = c)

/-- Number of steps entering cell `c`. -/
def entries (c : α) (p : List α) : ℕ := (steps p).countP (fun s => s.2 = c)

/-- Net outflow (as an integer) of cell `c` along path `p`. -/
def divergence (c : α) (p : List α) : ℤ := (exits c p : ℤ) - entries c p

/-! ### Structural helper lemmas (not part of the stated interface) -/

@[simp] lemma steps_nil : steps ([] : List α) = [] := rfl

@[simp] lemma steps_single (a : α) : steps [a] = [] := rfl

@[simp] lemma steps_cons_cons (a b : α) (t : List α) :
    steps (a :: b :: t) = (a, b) :: steps (b :: t) := rfl

lemma exits_cons_cons (c a b : α) (t : List α) :
    exits c (a :: b :: t) = exits c (b :: t) + (if a = c then 1 else 0) := by
  simp [exits, List.countP_cons]

lemma entries_cons_cons (c a b : α) (t : List α) :
    entries c (a :: b :: t) = entries c (b :: t) + (if b = c then 1 else 0) := by
  simp [entries, List.countP_cons]

/-- Sanity check: the step list has `length - 1` entries, i.e. it is indexed by `i < length-1`. -/
theorem steps_length (p : List α) : (steps p).length = p.length - 1 := by
  simp [steps]

/-- Sanity check: the `i`-th step is `(p[i], p[i+1])`. -/
theorem steps_getElem? (p : List α) (i : ℕ) (hi : i + 1 < p.length) :
    (steps p)[i]? = some (p[i], p[i+1]) := by
  simp [steps, List.getElem?_zip_eq_some]

/-- Index form of `exits`: the number of `i < length - 1` with `p[i] = c`. -/
theorem exits_eq_card (c : α) (p : List α) :
    exits c p = ((Finset.range (p.length - 1)).filter (fun i => p[i]? = some c)).card := by
  rw [Finset.card_filter]
  induction p with
  | nil => simp [exits]
  | cons a t ih =>
    cases t with
    | nil => simp [exits]
    | cons b t =>
      rw [exits_cons_cons, ih]
      simp only [List.length_cons, Nat.add_sub_cancel] at *
      rw [Finset.sum_range_succ']
      simp [List.getElem?_cons_succ]

/-- Index form of `entries`: the number of `i < length - 1` with `p[i+1] = c`. -/
theorem entries_eq_card (c : α) (p : List α) :
    entries c p = ((Finset.range (p.length - 1)).filter (fun i => p[i+1]? = some c)).card := by
  rw [Finset.card_filter]
  induction p with
  | nil => simp [entries]
  | cons a t ih =>
    cases t with
    | nil => simp [entries]
    | cons b t =>
      rw [entries_cons_cons, ih]
      simp only [List.length_cons, Nat.add_sub_cancel] at *
      rw [Finset.sum_range_succ']
      simp [List.getElem?_cons_succ]


/-- Key step: prepending a cell `a` to a nonempty path `t` adds one exit at `a` and one
entry at `head t`. -/
theorem divergence_cons (c a : α) (t : List α) (ht : t ≠ []) :
    divergence c (a :: t) = ((if a = c then 1 else 0) - (if t.head ht = c then 1 else 0))
      + divergence c t := by
  obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil ht
  simp only [divergence, exits_cons_cons, entries_cons_cons, List.head_cons]
  by_cases h1 : a = c <;> by_cases h2 : b = c <;> simp [h1, h2] <;> ring

/-- **Flux cancellation.** For a nonempty path, the divergence at every cell is
`[c = head] - [c = last]`. -/
theorem divergence_eq (p : List α) (hp : p ≠ []) (c : α) :
    divergence c p =
      (if c = p.head hp then 1 else 0) - (if c = p.getLast hp then 1 else 0) := by
  induction p with
  | nil => exact absurd rfl hp
  | cons a t ih =>
    rcases eq_or_ne t [] with rfl | ht
    · simp only [divergence, exits, entries, steps_single, List.countP_nil, List.head_cons,
        List.getLast_singleton, Nat.cast_zero]
      by_cases h : c = a <;> simp [h]
    · rw [divergence_cons c a t ht, ih ht, List.getLast_cons ht]
      simp only [List.head_cons]
      simp only [eq_comm (a := c)]
      ring


/-- The empty path has zero divergence everywhere. -/
theorem divergence_nil (c : α) : divergence c ([] : List α) = 0 := by
  simp [divergence, exits, entries]

/-- Corollary: total divergence over a finite cell type is zero. -/
theorem sum_divergence [Fintype α] (p : List α) :
    ∑ c, divergence c p = 0 := by
  rcases eq_or_ne p [] with rfl | hp
  · simp [divergence_nil]
  · simp only [divergence_eq p hp, Finset.sum_sub_distrib]
    simp

/-- Corollary: a closed path (head = last) is divergence-free at every cell. -/
theorem divergence_closed (p : List α) (hp : p ≠ []) (hcl : p.head hp = p.getLast hp)
    (c : α) : divergence c p = 0 := by
  rw [divergence_eq p hp, hcl, sub_self]

/-- Corollary (open path): the head has divergence `+1`. -/
theorem divergence_head_open (p : List α) (hp : p ≠ []) (hop : p.head hp ≠ p.getLast hp) :
    divergence (p.head hp) p = 1 := by
  rw [divergence_eq p hp]
  simp [hop]

/-- Corollary (open path): the last cell has divergence `-1`. -/
theorem divergence_last_open (p : List α) (hp : p ≠ []) (hop : p.head hp ≠ p.getLast hp) :
    divergence (p.getLast hp) p = -1 := by
  rw [divergence_eq p hp]
  simp [Ne.symm hop]

/-- Corollary (open path): every other cell has divergence `0`. -/
theorem divergence_other (p : List α) (hp : p ≠ []) (c : α)
    (h1 : c ≠ p.head hp) (h2 : c ≠ p.getLast hp) : divergence c p = 0 := by
  rw [divergence_eq p hp]
  simp [h1, h2]

/-- Corollary (open path): exactly the head is a source and exactly the last is a sink:
`divergence c p = 1 ↔ c = head` and `divergence c p = -1 ↔ c = last`. -/
theorem divergence_open_iff (p : List α) (hp : p ≠ []) (hop : p.head hp ≠ p.getLast hp)
    (c : α) :
    (divergence c p = 1 ↔ c = p.head hp) ∧ (divergence c p = -1 ↔ c = p.getLast hp) := by
  rw [divergence_eq p hp]
  by_cases h1 : c = p.head hp
  · subst h1; simp [hop]
  · by_cases h2 : c = p.getLast hp
    · subst h2; simp [h1]
    · simp [h1, h2]

/-- Bonus: total exits over a finite cell type equals the number of steps. -/
theorem sum_exits [Fintype α] (p : List α) : ∑ c, exits c p = p.length - 1 := by
  induction p with
  | nil => simp [exits]
  | cons a t ih =>
    cases t with
    | nil => simp [exits]
    | cons b t =>
      simp only [exits_cons_cons, Finset.sum_add_distrib, ih]
      simp

/-! ### Adversarial-review additions -/

/-- Concrete instance of `divergence_eq`: the open path `0 → 1 → 2 → 1` in `Fin 3`.
Head `0` is the source (`+1`), last `1` is the sink (`-1`), and `2` (visited in the
interior, entered once and exited once) has divergence `0`. -/
example : divergence (0 : Fin 3) [0, 1, 2, 1] = 1 ∧ divergence (1 : Fin 3) [0, 1, 2, 1] = -1 ∧
    divergence (2 : Fin 3) [0, 1, 2, 1] = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [divergence_eq _ (by simp)] <;> decide

/-- Concrete instance, closed path with a self-step: `0 → 0 → 1 → 0` has zero divergence
at every cell (checked by direct evaluation, independent of the theorem). -/
example : ∀ c : Fin 2, divergence c [0, 0, 1, 0] = 0 := by decide

/-- **Generalization (discrete Stokes / telescoping).** For any potential `f : α → G` into an
additive commutative group, the sum over the steps of the drop `f source - f target` equals
`f head - f last`. `divergence_eq` is the special case where `f` is the indicator of one cell
`c` (with `G = ℤ`), since `exits - entries` is the sum over steps of
`[source = c] - [target = c]`; this file proves the general statement but does not formally
derive `divergence_eq` from it. -/
theorem steps_telescope {G : Type*} [AddCommGroup G] (f : α → G) (p : List α) (hp : p ≠ []) :
    ((steps p).map (fun s => f s.1 - f s.2)).sum = f (p.head hp) - f (p.getLast hp) := by
  induction p with
  | nil => exact absurd rfl hp
  | cons a t ih =>
    rcases eq_or_ne t [] with rfl | ht
    · simp
    · obtain ⟨b, t', rfl⟩ := List.exists_cons_of_ne_nil ht
      rw [steps_cons_cons, List.map_cons, List.sum_cons, ih ht, List.getLast_cons ht]
      simp only [List.head_cons]
      abel

/-- Concrete instance of `steps_telescope` with `f = id` on `ℤ`: along `3 → 7 → 2 → 10`,
the summed drops equal `3 - 10`. -/
example : ((steps ([3, 7, 2, 10] : List ℤ)).map (fun s => id s.1 - id s.2)).sum = 3 - 10 :=
  steps_telescope id [3, 7, 2, 10] (by simp)

end A05
