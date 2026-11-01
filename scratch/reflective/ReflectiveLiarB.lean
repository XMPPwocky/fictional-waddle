import Mathlib

/-!
# A toy reflective oracle facing the liar machine

The oracle is queried "is P(M outputs 1) > p?" and answers yes with probability `r`.
Consistency with the true probability `q = P(M outputs 1)` requires
`r = 1` if `q > p`, `r = 0` if `q < p`, and `r` arbitrary in `[0,1]` if `q = p`.
The liar machine outputs 1 exactly when the oracle answers no, so `q = 1 - r`.

PROVED
* `reflective_iff_half` / `reflective_set_half`: for threshold `1/2`, the pairs
  `(q, r) ∈ [0,1]²` that are oracle-consistent and satisfy the liar equation are
  exactly `(1/2, 1/2)`.
* `no_deterministic_half`: for threshold `1/2`, no `r ∈ {0,1}` is part of a consistent
  liar pair (for any `q`, with no range assumption on `q`).
* `no_deterministic`: the same for every threshold `p ∈ (0,1)`.
* `reflective_iff` / `reflective_set`: for threshold `p ∈ (0,1)`, the consistent liar
  pairs in `[0,1]²` are exactly `(p, 1 - p)`.

INTERPRETED
* "Consistent" is formalized as `Consistent p q r := (p < q → r = 1) ∧ (q < p → r = 0)`;
  the case `q = p` imposes no constraint beyond `r ∈ [0,1]`, which is part of `Reflective`.
* The liar machine is the equation `q = 1 - r`.
-/

namespace ReflectiveLiarB

/-- Oracle answer probability `r` is consistent with the true probability `q` for the
query "is P > p?". -/
def Consistent (p q r : ℝ) : Prop :=
  (p < q → r = 1) ∧ (q < p → r = 0)

/-- The liar machine outputs 1 exactly when the oracle answers no. -/
def Liar (q r : ℝ) : Prop :=
  q = 1 - r

/-- A reflective (consistent) pair for the liar machine at threshold `p`. -/
def Reflective (p q r : ℝ) : Prop :=
  q ∈ Set.Icc (0 : ℝ) 1 ∧ r ∈ Set.Icc (0 : ℝ) 1 ∧ Consistent p q r ∧ Liar q r

/-- Consistency plus the liar equation forces `q = p`, for any `p ∈ (0,1)`. -/
theorem q_eq_p {p q r : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hc : Consistent p q r) (hl : Liar q r) : q = p := by
  unfold Consistent at hc
  unfold Liar at hl
  rcases lt_trichotomy q p with h | h | h
  · have := hc.2 h; subst this; linarith
  · exact h
  · have := hc.1 h; subst this; linarith

/-- (3) For threshold `p ∈ (0,1)`, the reflective pairs are exactly `(p, 1 - p)`. -/
theorem reflective_iff {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (q r : ℝ) :
    Reflective p q r ↔ q = p ∧ r = 1 - p := by
  constructor
  · rintro ⟨_, _, hc, hl⟩
    have hq := q_eq_p hp0 hp1 hc hl
    unfold Liar at hl
    exact ⟨hq, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨⟨hp0.le, hp1.le⟩, ⟨by linarith, by linarith⟩, ⟨fun h => absurd h (lt_irrefl _),
      fun h => absurd h (lt_irrefl _)⟩, by unfold Liar; ring⟩

/-- (3), set form. -/
theorem reflective_set {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    {x : ℝ × ℝ | Reflective p x.1 x.2} = {(p, 1 - p)} := by
  ext ⟨q, r⟩
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  exact reflective_iff hp0 hp1 q r

/-- (1) For threshold `1/2`, the only reflective pair is `(1/2, 1/2)`: a fair coin. -/
theorem reflective_iff_half (q r : ℝ) :
    Reflective (1 / 2) q r ↔ q = 1 / 2 ∧ r = 1 / 2 := by
  rw [reflective_iff (by norm_num) (by norm_num)]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; norm_num⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; norm_num⟩

/-- (1), set form. -/
theorem reflective_set_half :
    {x : ℝ × ℝ | Reflective (1 / 2) x.1 x.2} = {((1 : ℝ) / 2, (1 : ℝ) / 2)} := by
  ext ⟨q, r⟩
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  exact reflective_iff_half q r

/-- (2), general threshold: no deterministic answer `r ∈ {0,1}` is consistent with the
liar, for any `q`. -/
theorem no_deterministic {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (q r : ℝ)
    (hr : r = 0 ∨ r = 1) : ¬ (Consistent p q r ∧ Liar q r) := by
  rintro ⟨hc, hl⟩
  have hq := q_eq_p hp0 hp1 hc hl
  unfold Liar at hl
  rcases hr with rfl | rfl <;> linarith

/-- (2) For threshold `1/2`, no deterministic answer `r ∈ {0,1}` is consistent. -/
theorem no_deterministic_half (q r : ℝ) (hr : r = 0 ∨ r = 1) :
    ¬ (Consistent (1 / 2) q r ∧ Liar q r) :=
  no_deterministic (by norm_num) (by norm_num) q r hr

/-- (2), stated for reflective pairs: no reflective pair at threshold `1/2` has
`r ∈ {0,1}`. -/
theorem no_deterministic_reflective_half (q r : ℝ) (hr : r = 0 ∨ r = 1) :
    ¬ Reflective (1 / 2) q r := fun h =>
  no_deterministic_half q r hr ⟨h.2.2.1, h.2.2.2⟩

end ReflectiveLiarB
