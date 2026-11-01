import Mathlib

/-!
# Echoes, spinor signs, and what shared seeds can and cannot correlate

* Q1 `chsh_deterministic`: for outputs in `[−1, 1]`, `|ab + ab' + a'b − a'b'| ≤ 2`.
* Q2 `chsh_shared_seed`: any mixture over a shared seed `λ` (copies in logical time, the "Law" cell) obeys CHSH ≤ 2.
  Shared randomness alone can never produce the "impossible" anticorrelations.
* Q3 `tsirelson_attained`: the spin-½ singlet, `E = −cos(θa − θb)`, at angles `0, π/2, π/4, −π/4`, reaches
  `|CHSH| = 2√2 > 2`.
* Q4 `postselection_reaches_four`: with postselection that may depend on the settings, every setting pair is served by
  SOME deterministic shared-seed strategy matching the PR box `E(x, y) = (−1)^{xy}` (CHSH = 4) …
* Q5 `no_single_seed_is_pr`: … but no single seed serves all four. The excess over 2 is made entirely by selection.
* Q6 `dirichlet_image`: with an even Green's function `G`, the field of a source at `y` plus a NEGATED image at `−y`
  vanishes on the wall `x = 0`. The echo is a sign-flipped copy from the mirror world.
* Q7 `spinor_sign`: a spin-½ phase `e^{iθ/2}` at `θ = 2π` is `−1`.
-/

namespace EchoesAndBounds

open Real

/-- **Q1.** -/
theorem chsh_deterministic (a a' b b' : ℝ) (ha : |a| ≤ 1) (ha' : |a'| ≤ 1) (hb : |b| ≤ 1) (hb' : |b'| ≤ 1) :
    |a * b + a * b' + a' * b - a' * b'| ≤ 2 := by
  have hb2 : |b + b'| + |b - b'| ≤ 2 := by
    have h1 := abs_le.mp hb; have h2 := abs_le.mp hb'
    rcases abs_cases (b + b') with ⟨e1, _⟩ | ⟨e1, _⟩ <;> rcases abs_cases (b - b') with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
      rw [e1, e2] <;> linarith
  calc |a * b + a * b' + a' * b - a' * b'| = |a * (b + b') + a' * (b - b')| := by
        rw [show a * b + a * b' + a' * b - a' * b' = a * (b + b') + a' * (b - b') by ring]
    _ ≤ |a * (b + b')| + |a' * (b - b')| := abs_add_le _ _
    _ = |a| * |b + b'| + |a'| * |b - b'| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * |b + b'| + 1 * |b - b'| := by gcongr
    _ ≤ 2 := by linarith

/-- **Q2.** -/
theorem chsh_shared_seed {Λ : Type*} [Fintype Λ] (w : Λ → ℝ) (hw : ∀ l, 0 ≤ w l) (hs : ∑ l, w l = 1)
    (A A' B B' : Λ → ℝ) (hA : ∀ l, |A l| ≤ 1) (hA' : ∀ l, |A' l| ≤ 1) (hB : ∀ l, |B l| ≤ 1) (hB' : ∀ l, |B' l| ≤ 1) :
    |∑ l, w l * (A l * B l + A l * B' l + A' l * B l - A' l * B' l)| ≤ 2 := by
  calc |∑ l, w l * (A l * B l + A l * B' l + A' l * B l - A' l * B' l)|
        ≤ ∑ l, |w l * (A l * B l + A l * B' l + A' l * B l - A' l * B' l)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, w l * 2 := by
        apply Finset.sum_le_sum; intro l _
        rw [abs_mul, abs_of_nonneg (hw l)]
        exact mul_le_mul_of_nonneg_left (chsh_deterministic _ _ _ _ (hA l) (hA' l) (hB l) (hB' l)) (hw l)
    _ = 2 := by rw [← Finset.sum_mul, hs, one_mul]

/-- **Q3.** -/
theorem tsirelson_attained :
    |(-cos (0 - π / 4)) + (-cos (0 - (-(π / 4)))) + (-cos (π / 2 - π / 4)) - (-cos (π / 2 - (-(π / 4))))|
      = 2 * √2 := by
  have h1 : cos (0 - π / 4) = √2 / 2 := by rw [zero_sub, cos_neg, cos_pi_div_four]
  have h2 : cos (0 - (-(π / 4))) = √2 / 2 := by rw [zero_sub, neg_neg, cos_pi_div_four]
  have h3 : cos (π / 2 - π / 4) = √2 / 2 := by rw [show π / 2 - π / 4 = π / 4 by ring, cos_pi_div_four]
  have h4 : cos (π / 2 - (-(π / 4))) = -(√2 / 2) := by
    rw [show π / 2 - (-(π / 4)) = π - π / 4 by ring, cos_pi_sub, cos_pi_div_four]
  rw [h1, h2, h3, h4]
  rw [show -(√2 / 2) + -(√2 / 2) + -(√2 / 2) - -(-(√2 / 2)) = -(2 * √2) by ring, abs_neg]
  exact abs_of_nonneg (by positivity)

/-- The PR box. -/
def pr (x y : Bool) : ℝ := if x && y then -1 else 1

/-- **Q4.** -/
theorem postselection_reaches_four :
    pr false false + pr false true + pr true false - pr true true = 4 ∧
      ∀ x y : Bool, ∃ a b : Bool → ℝ, (∀ i, a i = 1 ∨ a i = -1) ∧ (∀ i, b i = 1 ∨ b i = -1) ∧ a x * b y = pr x y := by
  refine ⟨by simp [pr]; norm_num, ?_⟩
  intro x y
  have hpm : pr x y = 1 ∨ pr x y = -1 := by unfold pr; split_ifs <;> simp
  exact ⟨fun _ => pr x y, fun _ => 1, fun _ => hpm, fun _ => Or.inl rfl, by ring⟩

/-- **Q5.** -/
theorem no_single_seed_is_pr : ¬ ∃ a b : Bool → ℝ, (∀ i, a i = 1 ∨ a i = -1) ∧ (∀ i, b i = 1 ∨ b i = -1) ∧
    ∀ x y : Bool, a x * b y = pr x y := by
  rintro ⟨a, b, ha, hb, h⟩
  have sq : ∀ v : ℝ, (v = 1 ∨ v = -1) → v ^ 2 = 1 := by rintro v (rfl | rfl) <;> norm_num
  have key : (a false * b false) * (a false * b true) * (a true * b false) * (a true * b true)
      = pr false false * pr false true * pr true false * pr true true := by rw [h, h, h, h]
  have lhs : (a false * b false) * (a false * b true) * (a true * b false) * (a true * b true)
      = (a false) ^ 2 * (a true) ^ 2 * ((b false) ^ 2 * (b true) ^ 2) := by ring
  rw [lhs, sq _ (ha false), sq _ (ha true), sq _ (hb false), sq _ (hb true)] at key
  simp [pr] at key
  norm_num at key

/-- **Q6.** -/
theorem dirichlet_image (G : ℝ → ℝ) (hG : ∀ r, G (-r) = G r) (y : ℝ) : G (0 - y) - G (0 + y) = 0 := by
  rw [zero_sub, zero_add, hG, sub_self]

/-- **Q7.** -/
theorem spinor_sign : Complex.exp (Complex.I * (2 * π) / 2) = -1 := by
  rw [show Complex.I * (2 * (π : ℂ)) / 2 = (π : ℂ) * Complex.I by ring]
  exact Complex.exp_pi_mul_I

end EchoesAndBounds
