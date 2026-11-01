import Mathlib

/-!
# Survival, squares, signs, and the power of cancellation

Part G: conditioning a killed process on survival (the Doob h-transform), the square that two-sided
conditioning produces, and why every state other than the ground state needs signs.

Part T: postselection on signed (quasi-probability) weights. Write the postselected mass as
`a - b` with `a, b ≥ 0` the positive and negative path masses. Its conditional negativity is
`(a + b) / (a - b)`.
* T1: if the conditional negativity is at most `M`, relative-error estimates of the path masses give
  the postselected ratio to additive error `2 ε M (1 + M)`. (With Stockmeyer approximate counting this
  places polynomial conditional negativity inside BPP^NP; that step is cited, not formalised.)
* T2: the test with masses `(a + b)^2` and `(a - b)^2`, run over scales `2^i`, decides the sign of any
  gap `δ` with `2^-p ≤ |δ| ≤ 1`; the postselected mass is always positive, and a positive filler
  outside the event keeps the global negativity at most 2. (This is the arithmetic core of placing PP
  inside signed postselection with bounded global negativity; closure of GapP under sums and products
  is cited, not formalised.)
-/

open Matrix Finset

namespace SignedPostselection

/-! ## Part G -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The survival-conditioned kernel: the Doob h-transform of a killed kernel `Q` by an
eigenvector `h` with `Q h = λ h`. -/
noncomputable def htrans (Q : Matrix n n ℝ) (h : n → ℝ) (lam : ℝ) : Matrix n n ℝ :=
  Matrix.of fun x y => Q x y * h y / (lam * h x)

omit [DecidableEq n] in
lemma row_eq (Q : Matrix n n ℝ) (h : n → ℝ) (lam : ℝ) (heig : Q *ᵥ h = lam • h) (x : n) :
    ∑ y, Q x y * h y = lam * h x := by
  have := congrFun heig x
  simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using this

omit [DecidableEq n] in
/-- **G1.** Conditioning on survival gives a genuine Markov chain: nonnegative entries, rows sum to 1. -/
theorem htrans_stochastic (Q : Matrix n n ℝ) (hQ0 : ∀ x y, 0 ≤ Q x y) (h : n → ℝ) (lam : ℝ)
    (hlam : 0 < lam) (hpos : ∀ x, 0 < h x) (heig : Q *ᵥ h = lam • h) (x : n) :
    (∀ y, 0 ≤ htrans Q h lam x y) ∧ ∑ y, htrans Q h lam x y = 1 := by
  refine ⟨fun y => ?_, ?_⟩
  · simp only [htrans, Matrix.of_apply]
    exact div_nonneg (mul_nonneg (hQ0 x y) (hpos y).le) (mul_pos hlam (hpos x)).le
  · simp only [htrans, Matrix.of_apply]
    rw [← Finset.sum_div, row_eq Q h lam heig x]
    exact div_self (mul_ne_zero hlam.ne' (hpos x).ne')

omit [DecidableEq n] in
/-- **G2.** Two-sided conditioning gives the square: for a symmetric killed kernel, `h²` is
stationary for the survival-conditioned chain. -/
theorem htrans_stationary_sq (Q : Matrix n n ℝ) (hQ : Q.IsSymm) (h : n → ℝ) (lam : ℝ)
    (hlam : 0 < lam) (hpos : ∀ x, 0 < h x) (heig : Q *ᵥ h = lam • h) (y : n) :
    ∑ x, h x ^ 2 * htrans Q h lam x y = h y ^ 2 := by
  have hterm : ∀ x, h x ^ 2 * htrans Q h lam x y = (h y / lam) * (Q y x * h x) := by
    intro x
    simp only [htrans, Matrix.of_apply]
    rw [hQ.apply y x]
    have hx0 := (hpos x).ne'
    have hl0 := hlam.ne'
    field_simp
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum, row_eq Q h lam heig y]
  have hl0 := hlam.ne'
  field_simp

omit [DecidableEq n] in
/-- **G3.** Excited states need signs: an eigenvector of a symmetric matrix for any eigenvalue other
than that of a positive eigenvector takes both strictly positive and strictly negative values. -/
theorem excited_has_both_signs (Q : Matrix n n ℝ) (hQ : Q.IsSymm) (h v : n → ℝ) (lam mu : ℝ)
    (hpos : ∀ x, 0 < h x) (heig : Q *ᵥ h = lam • h) (hv : Q *ᵥ v = mu • v) (hne : mu ≠ lam)
    (hv0 : v ≠ 0) : (∃ x, 0 < v x) ∧ (∃ x, v x < 0) := by
  have hdot : h ⬝ᵥ v = 0 := by
    have h1 : (Q *ᵥ h) ⬝ᵥ v = h ⬝ᵥ (Q *ᵥ v) := by
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hQ.eq,
        dotProduct_comm]
    rw [heig, hv, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h1
    have h2 : (lam - mu) * (h ⬝ᵥ v) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3).symm hne
    · exact h3
  have hex : ∃ x, v x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv0 (funext hc)
  obtain ⟨x0, hx0⟩ := hex
  rw [dotProduct] at hdot
  constructor
  · by_contra hc
    push_neg at hc
    have hlt : ∑ x, h x * v x < ∑ x : n, (0 : ℝ) :=
      Finset.sum_lt_sum (fun x _ => mul_nonpos_of_nonneg_of_nonpos (hpos x).le (hc x))
        ⟨x0, Finset.mem_univ _, mul_neg_of_pos_of_neg (hpos x0) (lt_of_le_of_ne (hc x0) hx0)⟩
    rw [Finset.sum_const_zero] at hlt
    linarith
  · by_contra hc
    push_neg at hc
    have hlt : ∑ x : n, (0 : ℝ) < ∑ x, h x * v x :=
      Finset.sum_lt_sum (fun x _ => mul_nonneg (hpos x).le (hc x))
        ⟨x0, Finset.mem_univ _, mul_pos (hpos x0) (lt_of_le_of_ne (hc x0) (Ne.symm hx0))⟩
    rw [Finset.sum_const_zero] at hlt
    linarith

/-! ## Part T -/

/-- **T1a.** Bounded cancellation lets relative error survive subtraction. -/
theorem cancel_bound (a b ah bh M ε : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hD : 0 < a - b)
    (hM : a + b ≤ M * (a - b)) (hε : 0 ≤ ε)
    (hah : |ah - a| ≤ ε * a) (hbh : |bh - b| ≤ ε * b) :
    |(ah - bh) - (a - b)| ≤ ε * M * (a - b) := by
  obtain ⟨h1, h2⟩ := abs_le.mp hah
  obtain ⟨h3, h4⟩ := abs_le.mp hbh
  have hab : ε * a + ε * b ≤ ε * M * (a - b) := by nlinarith [mul_le_mul_of_nonneg_left hM hε]
  rw [abs_le]
  constructor <;> linarith

/-- **T1b.** The postselected ratio is stable: with conditional negativity at most `M` and relative
error `ε` on every path mass (`εM ≤ 1/2`), the ratio `(a₁ - b₁) / (a - b)` for a sub-event is
recovered to additive error `2 ε M (1 + M)`. -/
theorem ratio_stable (a b a1 b1 ah bh a1h b1h M ε : ℝ)
    (ha1 : 0 ≤ a1) (hb1 : 0 ≤ b1) (ha1a : a1 ≤ a) (hb1b : b1 ≤ b) (hD : 0 < a - b)
    (hM : a + b ≤ M * (a - b)) (hε : 0 ≤ ε) (hεM : ε * M ≤ 1 / 2)
    (hah : |ah - a| ≤ ε * a) (hbh : |bh - b| ≤ ε * b)
    (ha1h : |a1h - a1| ≤ ε * a1) (hb1h : |b1h - b1| ≤ ε * b1) :
    |(a1h - b1h) / (ah - bh) - (a1 - b1) / (a - b)| ≤ 2 * ε * M * (1 + M) := by
  have hDD := cancel_bound a b ah bh M ε (by linarith) (by linarith) hD hM hε hah hbh
  set D := a - b with hDdef
  set Dh := ah - bh with hDhdef
  set N := a1 - b1 with hNdef
  set Nh := a1h - b1h with hNhdef
  have hM1 : 1 ≤ M := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hNN : |Nh - N| ≤ ε * M * D := by
    obtain ⟨h1, h2⟩ := abs_le.mp ha1h
    obtain ⟨h3, h4⟩ := abs_le.mp hb1h
    have : ε * a1 + ε * b1 ≤ ε * M * D := by
      nlinarith [mul_nonneg hε (sub_nonneg.mpr ha1a), mul_nonneg hε (sub_nonneg.mpr hb1b),
        mul_le_mul_of_nonneg_left hM hε]
    rw [abs_le]
    constructor <;> linarith
  have hN : |N| ≤ M * D := by
    rw [abs_le]
    constructor <;> linarith
  have hhalf : ε * M * D ≤ D / 2 := by nlinarith [mul_le_mul_of_nonneg_right hεM hD.le]
  have hDh : D / 2 ≤ Dh := by
    obtain ⟨h1, _⟩ := abs_le.mp hDD
    linarith
  have hDhpos : 0 < Dh := by linarith
  rw [div_sub_div _ _ hDhpos.ne' hD.ne', abs_div, abs_of_pos (mul_pos hDhpos hD),
    div_le_iff₀ (mul_pos hDhpos hD)]
  have key : Nh * D - Dh * N = (Nh - N) * D - N * (Dh - D) := by ring
  rw [key]
  have e1 : |(Nh - N) * D| ≤ ε * M * D * D := by
    rw [abs_mul, abs_of_pos hD]
    exact mul_le_mul_of_nonneg_right hNN hD.le
  have e2 : |N * (Dh - D)| ≤ M * D * (ε * M * D) := by
    rw [abs_mul]
    exact mul_le_mul hN hDD (abs_nonneg _) (by positivity)
  obtain ⟨f1, f2⟩ := abs_le.mp e1
  obtain ⟨f3, f4⟩ := abs_le.mp e2
  have hsq : D * D ≤ 2 * (Dh * D) := by nlinarith
  have hc : 0 ≤ ε * M * (1 + M) := by positivity
  have hfin : ε * M * D * D + M * D * (ε * M * D) ≤ 2 * ε * M * (1 + M) * (Dh * D) := by
    have := mul_le_mul_of_nonneg_left hsq hc
    nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- The postselected acceptance probability of the two-outcome test with masses `(a+b)²`, `(a-b)²`. -/
noncomputable def accP (a b : ℝ) : ℝ := (a + b) ^ 2 / ((a + b) ^ 2 + (a - b) ^ 2)

/-- **T2a.** The postselected mass is always positive, so the postselection promise holds. -/
theorem post_mass_pos (a b : ℝ) (ha : a ≠ 0) : 0 < (a + b) ^ 2 + (a - b) ^ 2 := by
  have : 0 < a ^ 2 := by positivity
  nlinarith [sq_nonneg b]

/-- **T2b.** A non-positive gap never pushes acceptance above 1/2. -/
theorem accP_le_half (a b : ℝ) (ha : 0 < a) (hb : b ≤ 0) : accP a b ≤ 1 / 2 := by
  rw [accP, div_le_iff₀ (post_mass_pos a b ha.ne')]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.le hb]

/-- **T2c.** A gap at the right scale pushes acceptance to at least 9/10. -/
theorem accP_ge (a b : ℝ) (ha : 0 < a) (h1 : a / 2 ≤ b) (h2 : b ≤ 2 * a) : 9 / 10 ≤ accP a b := by
  rw [accP, le_div_iff₀ (post_mass_pos a b ha.ne')]
  nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h1)]

/-- **T2d.** Some power of two brings any gap with `2^-p ≤ |δ| ≤ 1` into `[1, 2]`. -/
theorem exists_scale (p : ℕ) (δ : ℝ) (hlo : (2 : ℝ)⁻¹ ^ p ≤ |δ|) (hhi : |δ| ≤ 1) :
    ∃ i ≤ p, 1 ≤ (2 : ℝ) ^ i * |δ| ∧ (2 : ℝ) ^ i * |δ| ≤ 2 := by
  classical
  have hp : 1 ≤ (2 : ℝ) ^ p * |δ| := by
    have h1 : (2 : ℝ) ^ p * (2 : ℝ)⁻¹ ^ p = 1 := by rw [← mul_pow]; norm_num
    calc (1 : ℝ) = 2 ^ p * 2⁻¹ ^ p := h1.symm
      _ ≤ 2 ^ p * |δ| := by gcongr
  have hex : ∃ i : ℕ, 1 ≤ (2 : ℝ) ^ i * |δ| := ⟨p, hp⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hp, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero, one_mul]
    linarith
  · have hnot := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    push_neg at hnot
    have hsplit : (2 : ℝ) ^ Nat.find hex = 2 * 2 ^ (Nat.find hex - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hsplit]
    nlinarith [abs_nonneg δ]

/-- **T2e.** The scaled test decides the sign of the gap: a positive gap passes 9/10 at some scale
`i ≤ p`; a negative gap stays at or below 1/2 at every scale. -/
theorem sign_decided (p : ℕ) (δ : ℝ) (hlo : (2 : ℝ)⁻¹ ^ p ≤ |δ|) (hhi : |δ| ≤ 1) :
    (0 < δ → ∃ i ≤ p, 9 / 10 ≤ accP 1 (2 ^ i * δ)) ∧
      (δ < 0 → ∀ i : ℕ, accP 1 (2 ^ i * δ) ≤ 1 / 2) := by
  constructor
  · intro hδ
    obtain ⟨i, hi, h1, h2⟩ := exists_scale p δ hlo hhi
    rw [abs_of_pos hδ] at h1 h2
    exact ⟨i, hi, accP_ge 1 _ one_pos (by linarith) (by linarith)⟩
  · intro hδ i
    exact accP_le_half 1 _ one_pos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hδ.le)

/-- **T2f.** A positive filler outside the postselected event bounds the global negativity by 2,
however much cancellation the event contains: `L` is the event's path-level mass, `m` its net mass. -/
theorem global_negativity_le_two (F L m : ℝ) (hm : 0 < m) (hmL : m ≤ L) (hF : L ≤ F) :
    (F + L) / (F + m) ≤ 2 := by
  rw [div_le_iff₀ (by linarith)]
  linarith

end SignedPostselection
