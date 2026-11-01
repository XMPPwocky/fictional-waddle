import Mathlib

/-!
# S1: Stochastic-computing AND and the Fréchet bounds

Two bits `a, b` with joint table `p00 p01 p10 p11` (nonnegative reals summing to 1),
`p = P(a=1) = p10 + p11`, `q = P(b=1) = p01 + p11`, and `P(a AND b) = p11`.

**Proved** (pure real algebra on the 2×2 table):
1. Fréchet bounds `max 0 (p+q-1) ≤ p11 ≤ min p q`.
2. Covariance identity `p11 - p*q = p00*p11 - p01*p10`, hence
   `p11 = p*q ↔ p00*p11 = p01*p10` (independence of the 2×2 table).
3. Every value in the Fréchet interval is attained by some table with marginals `p, q`;
   in particular the comonotone (`min p q`) and antitone (`max 0 (p+q-1)`) couplings.
   Combined with (1): the achievable AND outputs are *exactly* the Fréchet interval
   (`and_range_iff`).
4. Identical copies (`p01 = p10 = 0`) give `P(a AND a) = p` (idempotence), independence
   with equal marginals gives `p^2`, and these differ unless `p ∈ {0,1}`.

**Interpretation** (not formalised): an AND gate multiplies probability streams exactly when
they are uncorrelated (Gaines 1969, stochastic computing); correlation moves the output
anywhere in the Fréchet interval.
-/

namespace SC.Frechet

/-- A joint distribution of two bits: four nonnegative reals summing to 1. -/
def IsTable (p00 p01 p10 p11 : ℝ) : Prop :=
  0 ≤ p00 ∧ 0 ≤ p01 ∧ 0 ≤ p10 ∧ 0 ≤ p11 ∧ p00 + p01 + p10 + p11 = 1

/-- (1, lower) Fréchet lower bound: `max 0 (p + q - 1) ≤ P(a ∧ b)`. -/
theorem frechet_lower {p00 p01 p10 p11 : ℝ} (h : IsTable p00 p01 p10 p11) :
    max 0 ((p10 + p11) + (p01 + p11) - 1) ≤ p11 := by
  obtain ⟨_, _, _, h3, hs⟩ := h
  exact max_le h3 (by linarith)

/-- (1, upper) Fréchet upper bound: `P(a ∧ b) ≤ min p q`. -/
theorem frechet_upper {p00 p01 p10 p11 : ℝ} (h : IsTable p00 p01 p10 p11) :
    p11 ≤ min (p10 + p11) (p01 + p11) := by
  obtain ⟨_, h1, h2, _, _⟩ := h
  exact le_min (by linarith) (by linarith)

/-- (2, identity) The covariance of the two bits equals the 2×2 cross-product difference. -/
theorem cov_eq_cross {p00 p01 p10 p11 : ℝ} (h : IsTable p00 p01 p10 p11) :
    p11 - (p10 + p11) * (p01 + p11) = p00 * p11 - p01 * p10 := by
  obtain ⟨_, _, _, _, hs⟩ := h
  linear_combination (-p11) * hs

/-- (2, trivial form) AND multiplies iff the covariance vanishes. -/
theorem and_mul_iff_cov_zero (p00 p01 p10 p11 : ℝ) :
    p11 = (p10 + p11) * (p01 + p11) ↔ p11 - (p10 + p11) * (p01 + p11) = 0 := by
  exact sub_eq_zero.symm

/-- (2) AND multiplies the marginals iff the 2×2 table is independent (`p00 p11 = p01 p10`). -/
theorem and_mul_iff_indep {p00 p01 p10 p11 : ℝ} (h : IsTable p00 p01 p10 p11) :
    p11 = (p10 + p11) * (p01 + p11) ↔ p00 * p11 = p01 * p10 := by
  rw [← sub_eq_zero, cov_eq_cross h, sub_eq_zero]

/-- (3, general) Every value in the Fréchet interval is the AND probability of some joint table
with the prescribed marginals. -/
theorem frechet_interval_attained {p q r : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : max 0 (p + q - 1) ≤ r) (hr1 : r ≤ min p q) :
    ∃ p00 p01 p10 p11 : ℝ, IsTable p00 p01 p10 p11 ∧
      p10 + p11 = p ∧ p01 + p11 = q ∧ p11 = r := by
  have a1 := le_max_left 0 (p + q - 1)
  have a2 := le_max_right 0 (p + q - 1)
  have b1 := min_le_left p q
  have b2 := min_le_right p q
  refine ⟨1 - p - q + r, q - r, p - r, r, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, rfl⟩ <;>
    linarith

/-- (3, upper attained) Comonotone coupling: `P(a ∧ b) = min p q`. -/
theorem comonotone_attains {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ p00 p01 p10 p11 : ℝ, IsTable p00 p01 p10 p11 ∧
      p10 + p11 = p ∧ p01 + p11 = q ∧ p11 = min p q := by
  exact frechet_interval_attained hp0 hp1 hq0 hq1
    (max_le (le_min hp0 hq0) (le_min (by linarith) (by linarith))) le_rfl

/-- (3, lower attained) Antitone coupling: `P(a ∧ b) = max 0 (p + q - 1)`. -/
theorem antitone_attains {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ p00 p01 p10 p11 : ℝ, IsTable p00 p01 p10 p11 ∧
      p10 + p11 = p ∧ p01 + p11 = q ∧ p11 = max 0 (p + q - 1) := by
  exact frechet_interval_attained hp0 hp1 hq0 hq1 le_rfl
    (max_le (le_min hp0 hq0) (le_min (by linarith) (by linarith)))

/-- (3, independent attained) The product coupling: `P(a ∧ b) = p q`. -/
theorem product_attains {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ p00 p01 p10 p11 : ℝ, IsTable p00 p01 p10 p11 ∧
      p10 + p11 = p ∧ p01 + p11 = q ∧ p11 = p * q := by
  refine frechet_interval_attained hp0 hp1 hq0 hq1 ?_ ?_
  · exact max_le (mul_nonneg hp0 hq0)
      (by nlinarith [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hq1)])
  · exact le_min (mul_le_of_le_one_right hp0 hq1) (mul_le_of_le_one_left hq0 hp1)

/-- (3, up: exact range) The set of AND probabilities achievable with marginals `p, q ∈ [0,1]`
is *exactly* the Fréchet interval `[max 0 (p+q-1), min p q]`: the bounds of (1) are sharp and
nothing between them is excluded. Combines `frechet_lower`, `frechet_upper` and
`frechet_interval_attained` into one iff. -/
theorem and_range_iff {p q r : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∃ p00 p01 p10 p11 : ℝ, IsTable p00 p01 p10 p11 ∧
      p10 + p11 = p ∧ p01 + p11 = q ∧ p11 = r) ↔
      (max 0 (p + q - 1) ≤ r ∧ r ≤ min p q) := by
  constructor
  · rintro ⟨p00, p01, p10, p11, h, rfl, rfl, rfl⟩
    exact ⟨frechet_lower h, frechet_upper h⟩
  · rintro ⟨h1, h2⟩
    exact frechet_interval_attained hp0 hp1 hq0 hq1 h1 h2

/-- (4) Identical copies (`a = b` a.s.): `P(a ∧ a) = p` (idempotence of AND). -/
theorem identical_copies {p00 p01 p10 p11 : ℝ} (h01 : p01 = 0) (h10 : p10 = 0) :
    p11 = p10 + p11 ∧ p01 + p11 = p10 + p11 := by
  subst h01 h10
  simp

/-- (4) Independence with equal marginals `p = q` gives `P(a ∧ b) = p^2`. -/
theorem independent_equal_marginals {p00 p01 p10 p11 : ℝ} (h : IsTable p00 p01 p10 p11)
    (hind : p00 * p11 = p01 * p10) (heq : p10 + p11 = p01 + p11) :
    p11 = (p10 + p11) ^ 2 := by
  have hpq := (and_mul_iff_indep h).2 hind
  calc p11 = (p10 + p11) * (p01 + p11) := hpq
    _ = (p10 + p11) ^ 2 := by rw [← heq, sq]

/-- (4) Identical copies are not independent unless the bit is deterministic:
for `a = b` a.s., `P(a ∧ a) = p^2 ↔ p = 0 ∨ p = 1`. -/
theorem identical_eq_sq_iff {p00 p01 p10 p11 : ℝ} (h01 : p01 = 0) (h10 : p10 = 0) :
    p11 = (p10 + p11) ^ 2 ↔ (p10 + p11 = 0 ∨ p10 + p11 = 1) := by
  subst h01 h10
  simp only [zero_add]
  constructor
  · intro hs
    have : p11 * (p11 - 1) = 0 := by linear_combination -hs
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h) <;> subst h <;> norm_num

/-! ### Concrete instantiations (non-vacuity checks) -/

/-- The uniform table is a genuine table, and it is independent. -/
example : IsTable (1/4) (1/4) (1/4) (1/4) ∧ (1/4 : ℝ) * (1/4) = (1/4) * (1/4) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, rfl⟩ <;> norm_num

/-- The table `(0.1, 0.2, 0.3, 0.4)`: `p = 0.7`, `q = 0.6`, so `0.3 ≤ P(a∧b) = 0.4 ≤ 0.6`;
AND does not multiply (`0.4 ≠ 0.42`), matching `p00 p11 = 0.04 ≠ 0.06 = p01 p10`. -/
example : max 0 ((3/10 + 4/10) + (2/10 + 4/10) - 1 : ℝ) ≤ 4/10 ∧
    (4/10 : ℝ) ≤ min (3/10 + 4/10) (2/10 + 4/10) ∧
    ¬ ((4/10 : ℝ) = (3/10 + 4/10) * (2/10 + 4/10)) := by
  have h : IsTable (1/10 : ℝ) (2/10) (3/10) (4/10) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num
  refine ⟨frechet_lower h, frechet_upper h, ?_⟩
  rw [and_mul_iff_indep h]; norm_num

/-- Fair bits `p = q = 1/2`: AND can output `1/4` (independent), `1/2` (comonotone) and
`0` (antitone), but never `3/4`. -/
example :
    (∃ p00 p01 p10 p11 : ℝ, IsTable p00 p01 p10 p11 ∧
      p10 + p11 = 1/2 ∧ p01 + p11 = 1/2 ∧ p11 = 1/4) ∧
    (∃ p00 p01 p10 p11 : ℝ, IsTable p00 p01 p10 p11 ∧
      p10 + p11 = 1/2 ∧ p01 + p11 = 1/2 ∧ p11 = 1/2) ∧
    (∃ p00 p01 p10 p11 : ℝ, IsTable p00 p01 p10 p11 ∧
      p10 + p11 = 1/2 ∧ p01 + p11 = 1/2 ∧ p11 = 0) ∧
    ¬ (∃ p00 p01 p10 p11 : ℝ, IsTable p00 p01 p10 p11 ∧
      p10 + p11 = 1/2 ∧ p01 + p11 = 1/2 ∧ p11 = 3/4) := by
  have h0 : (0 : ℝ) ≤ 1/2 := by norm_num
  have h1 : (1/2 : ℝ) ≤ 1 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := product_attains h0 h1 h0 h1; norm_num at this ⊢; exact this
  · have := comonotone_attains h0 h1 h0 h1; norm_num at this ⊢; exact this
  · have := antitone_attains h0 h1 h0 h1; norm_num at this ⊢; exact this
  · rw [and_range_iff h0 h1 h0 h1]; norm_num

end SC.Frechet
