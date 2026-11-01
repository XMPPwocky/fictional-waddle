import Mathlib

/-!
# A toy reflective oracle facing the liar machine

The oracle is queried "is P(M outputs 1) > p?" and answers yes with probability `r ∈ [0,1]`.
Writing `q = P(M outputs 1)`, the oracle answer is *consistent* (reflective) when
`q > p → r = 1` and `q < p → r = 0`; at `q = p` any `r ∈ [0,1]` is allowed.
The liar machine outputs 1 exactly when the oracle answers no, so `q = 1 - r`.

PROVED
* `liar_half_iff`: for `q, r ∈ [0,1]`, threshold `1/2`, consistency plus the liar equation
  `q = 1 - r` hold iff `(q, r) = (1/2, 1/2)`.
* `liar_half_exists_unique`: the consistent pair in `[0,1]²` exists and is unique.
* `no_deterministic_answer`: if `r = 0` or `r = 1`, no `q` satisfies consistency
  (threshold `1/2`) together with `q = 1 - r`.
* `liar_threshold_iff`: for `p ∈ (0,1)` and `q, r ∈ [0,1]`, consistency at threshold `p`
  plus `q = 1 - r` hold iff `q = p ∧ r = 1 - p`.
* `liar_threshold_exists_unique`: existence and uniqueness of that pair in `[0,1]²`.
* `no_deterministic_answer_threshold`: the deterministic-answer impossibility at any
  threshold `p ∈ (0,1)`.

INTERPRETED
* The oracle's randomized answer is represented only by its yes-probability `r`, and the
  liar machine only by its output-1 probability `q`; the machine/oracle semantics are
  encoded by the two real constraints `Consistent p q r` and `q = 1 - r`.
-/

namespace ReflectiveLiarA

/-- Reflective consistency of an oracle answering the query "P(M outputs 1) > p?" with
yes-probability `r`, when the true probability is `q`. At `q = p` it imposes nothing. -/
def Consistent (p q r : ℝ) : Prop :=
  (p < q → r = 1) ∧ (q < p → r = 0)

/-- The liar machine outputs 1 exactly when the oracle says no. -/
def Liar (q r : ℝ) : Prop := q = 1 - r

/-- The unit interval as a predicate. -/
def InUnit (x : ℝ) : Prop := 0 ≤ x ∧ x ≤ 1

theorem liar_threshold_iff (p q r : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (_hq : InUnit q) (_hr : InUnit r) :
    (Consistent p q r ∧ Liar q r) ↔ (q = p ∧ r = 1 - p) := by
  constructor
  · rintro ⟨⟨h1, h2⟩, hl⟩
    unfold Liar at hl
    have hqp : q = p := by
      rcases lt_trichotomy p q with h | h | h
      · have := h1 h; rw [this] at hl; linarith
      · exact h.symm
      · have := h2 h; rw [this] at hl; linarith
    exact ⟨hqp, by linarith⟩
  · rintro ⟨hq, hr⟩
    refine ⟨⟨fun h => by linarith, fun h => by linarith⟩, ?_⟩
    unfold Liar; linarith

theorem liar_threshold_exists_unique (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃! qr : ℝ × ℝ, InUnit qr.1 ∧ InUnit qr.2 ∧ Consistent p qr.1 qr.2 ∧ Liar qr.1 qr.2 := by
  refine ⟨(p, 1 - p), ⟨⟨hp0.le, hp1.le⟩, ⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
  · exact (liar_threshold_iff p p (1 - p) hp0 hp1 ⟨hp0.le, hp1.le⟩
      ⟨by linarith, by linarith⟩).2 ⟨rfl, rfl⟩
  · rintro ⟨q, r⟩ ⟨hq, hr, h⟩
    obtain ⟨h1, h2⟩ := (liar_threshold_iff p q r hp0 hp1 hq hr).1 h
    simp [h1, h2]

theorem no_deterministic_answer_threshold (p q r : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hdet : r = 0 ∨ r = 1) : ¬ (Consistent p q r ∧ Liar q r) := by
  rintro ⟨⟨h1, h2⟩, hl⟩
  unfold Liar at hl
  rcases hdet with h | h
  · subst h
    have hq : q = 1 := by linarith
    have := h1 (by linarith); norm_num at this
  · subst h
    have hq : q = 0 := by linarith
    have := h2 (by linarith); norm_num at this

theorem liar_half_iff (q r : ℝ) (hq : InUnit q) (hr : InUnit r) :
    (Consistent (1/2) q r ∧ Liar q r) ↔ (q = 1/2 ∧ r = 1/2) := by
  rw [liar_threshold_iff (1/2) q r (by norm_num) (by norm_num) hq hr]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; norm_num⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; norm_num⟩

theorem liar_half_exists_unique :
    ∃! qr : ℝ × ℝ, InUnit qr.1 ∧ InUnit qr.2 ∧ Consistent (1/2) qr.1 qr.2 ∧ Liar qr.1 qr.2 := by
  refine ⟨(1/2, 1/2), ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
  · exact (liar_half_iff (1/2) (1/2) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩).2 ⟨rfl, rfl⟩
  · rintro ⟨q, r⟩ ⟨hq, hr, h⟩
    obtain ⟨h1, h2⟩ := (liar_half_iff q r hq hr).1 h
    simp [h1, h2]

theorem no_deterministic_answer (q r : ℝ) (hdet : r = 0 ∨ r = 1) :
    ¬ (Consistent (1/2) q r ∧ Liar q r) :=
  no_deterministic_answer_threshold (1/2) q r (by norm_num) (by norm_num) hdet

end ReflectiveLiarA
