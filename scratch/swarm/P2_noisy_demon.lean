import Mathlib

/-!
# P2: a noisy Maxwell demon is a binary symmetric channel

Szilard engine, one cycle. The particle's side `X : Bool` is uniform. The demon measures it and records
`Y : Bool`, which equals `X` with probability `1 - ε` and is flipped with probability `ε` (`0 < ε < 1`).
So the joint law is `p x y = (1 - ε)/2` if `x = y` and `ε/2` otherwise (`bscJoint ε`).

**Proved here** (logs natural, `MI` copied verbatim from `scratch/KellyInformation.lean`):
* `bsc_MI` : `MI (bscJoint ε) = log 2 - h ε`, with `h ε = -ε log ε - (1-ε) log (1-ε)`.
* `h_eq_binEntropy` : our `h` is Mathlib's `Real.binEntropy`.
* `bsc_MI_lt` / `bsc_MI_strictAntiOn` : the information is strictly decreasing in the error rate on
  `(0, 1/2]`.
* `bsc_MI_half` : a coin-flip demon (`ε = 1/2`) has `MI = 0`.
* `bsc_MI_pos` : any demon with `0 < ε < 1/2` has strictly positive information.
* `bsc_MI_all` : (added by the second agent) the identity `bsc_MI` holds for every real `ε`. At `ε = 0, 1`
  it gives `MI = log 2`, using Mathlib's `log 0 = 0`. Outside `[0,1]` it is only an algebraic identity.

**Interpreted only, not formalized** (Sagawa–Ueda 2008/2010, generalized second law with feedback):
extractable work per cycle `W ≤ kT · I(X;Y)`. Combined with `bsc_MI`, a stochastically approximated demon
that errs with rate `ε` extracts at most `kT (log 2 - h ε)` per cycle, which shrinks strictly as `ε` grows
to `1/2`, and a coin-flip demon extracts nothing. No thermodynamics appears in this file; the physical
bound is a citation, only the information-theoretic identities are theorems.
-/

open Finset Real

namespace P2NoisyDemon

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Marginals and mutual information of a joint distribution on `X × Y` (copied from KellyInformation). -/
noncomputable def margX (p : X → Y → ℝ) (x : X) : ℝ := ∑ y, p x y
noncomputable def margY (p : X → Y → ℝ) (y : Y) : ℝ := ∑ x, p x y
noncomputable def MI (p : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, p x y * log (p x y / (margX p x * margY p y))

/-- Joint law of (particle side, demon record) for a binary symmetric channel with flip rate `ε`. -/
noncomputable def bscJoint (ε : ℝ) : Bool → Bool → ℝ :=
  fun x y => if x = y then (1 - ε) / 2 else ε / 2

/-- Binary entropy in nats, written out as in the task statement. -/
noncomputable def h (ε : ℝ) : ℝ := -ε * log ε - (1 - ε) * log (1 - ε)

/-- `bscJoint ε` is a strictly positive probability distribution for `0 < ε < 1`. -/
theorem bscJoint_pos {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (x y : Bool) : 0 < bscJoint ε x y := by
  unfold bscJoint
  split_ifs <;> linarith

theorem bscJoint_sum (ε : ℝ) : ∑ x, ∑ y, bscJoint ε x y = 1 := by
  simp only [Fintype.sum_bool, bscJoint]
  norm_num
  ring

/-- The particle's side is uniform, and so is the demon's record. -/
theorem bsc_margX (ε : ℝ) (x : Bool) : margX (bscJoint ε) x = 1 / 2 := by
  unfold margX bscJoint
  cases x <;> simp only [Fintype.sum_bool] <;> norm_num <;> ring

theorem bsc_margY (ε : ℝ) (y : Bool) : margY (bscJoint ε) y = 1 / 2 := by
  unfold margY bscJoint
  cases y <;> simp only [Fintype.sum_bool] <;> norm_num <;> ring

/-- Our `h` coincides with Mathlib's binary entropy. -/
theorem h_eq_binEntropy (ε : ℝ) : h ε = Real.binEntropy ε := by
  simp only [h, Real.binEntropy, Real.log_inv]
  ring

/-- **Main identity.** `I(X;Y) = log 2 - h(ε)` for the noisy demon. -/
theorem bsc_MI {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) : MI (bscJoint ε) = log 2 - h ε := by
  have h1 : (1 - ε) ≠ 0 := by linarith
  have h0 : ε ≠ 0 := hε0.ne'
  have e1 : (1 - ε) / 2 / (1 / 2 * (1 / 2)) = 2 * (1 - ε) := by field_simp
  have e2 : ε / 2 / (1 / 2 * (1 / 2)) = 2 * ε := by field_simp
  unfold MI
  simp only [bsc_margX, bsc_margY, Fintype.sum_bool, bscJoint]
  simp only [ite_true, Bool.true_eq_false, Bool.false_eq_true, ite_false, e1, e2]
  rw [Real.log_mul two_ne_zero h1, Real.log_mul two_ne_zero h0]
  unfold h
  ring

/-- **Coin-flip demon.** At `ε = 1/2` the record carries no information. -/
theorem bsc_MI_half : MI (bscJoint (1 / 2)) = 0 := by
  rw [bsc_MI (by norm_num) (by norm_num), h_eq_binEntropy, one_div, Real.binEntropy_two_inv, sub_self]

/-- **Monotonicity.** A noisier demon (on `(0, 1/2]`) has strictly less information. -/
theorem bsc_MI_lt {ε ε' : ℝ} (hε' : 0 < ε') (hlt : ε' < ε) (hε : ε ≤ 1 / 2) :
    MI (bscJoint ε) < MI (bscJoint ε') := by
  have hε0 : 0 < ε := hε'.trans hlt
  rw [bsc_MI hε0 (by linarith), bsc_MI hε' (by linarith), h_eq_binEntropy, h_eq_binEntropy]
  have := Real.binEntropy_strictMonoOn (a := ε') (b := ε)
    ⟨hε'.le, by rw [← one_div]; linarith⟩ ⟨hε0.le, by rw [← one_div]; exact hε⟩ hlt
  linarith

theorem bsc_MI_strictAntiOn : StrictAntiOn (fun ε => MI (bscJoint ε)) (Set.Ioc 0 (1 / 2)) := by
  intro a ha b hb hab
  exact bsc_MI_lt ha.1 hab hb.2

/-- Any better-than-chance demon has strictly positive information. -/
theorem bsc_MI_pos {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) : 0 < MI (bscJoint ε) := by
  have := bsc_MI_lt hε0 hε le_rfl
  rwa [bsc_MI_half] at this

/-- **Generalization ("up").** The identity `MI (bscJoint ε) = log 2 - h ε` holds for *every* real `ε`,
with no hypothesis. At the endpoints `ε = 0` (perfect demon, `MI = log 2`) and `ε = 1` (perfectly
anti-correlated demon, also `MI = log 2`) it holds because Mathlib sets `log 0 = 0`. That matches the
information-theoretic convention `0 · log 0 = 0`. For `ε ∉ [0, 1]`, `bscJoint ε` is not a probability
distribution, so there the statement is only an algebraic identity about Mathlib's `log` (which satisfies
`log x = log |x|`). It has no probabilistic meaning. -/
theorem bsc_MI_all (ε : ℝ) : MI (bscJoint ε) = log 2 - h ε := by
  have key : ∀ t : ℝ, t / 2 * log (t / 2 / (1 / 2 * (1 / 2))) = t / 2 * log 2 + t / 2 * log t := by
    intro t
    have e : t / 2 / (1 / 2 * (1 / 2)) = 2 * t := by ring
    rw [e]
    by_cases ht : t = 0
    · simp [ht]
    · rw [Real.log_mul two_ne_zero ht]; ring
  unfold MI
  simp only [bsc_margX, bsc_margY, Fintype.sum_bool, bscJoint]
  simp only [ite_true, Bool.true_eq_false, Bool.false_eq_true, ite_false, key]
  unfold h
  ring

/-- Concrete instances: the hypotheses of the main theorems are satisfiable (`ε = 1/4`, `ε' = 1/8`). -/
example : MI (bscJoint (1 / 4)) = log 2 - h (1 / 4) := bsc_MI (by norm_num) (by norm_num)
example : MI (bscJoint (1 / 4)) < MI (bscJoint (1 / 8)) := bsc_MI_lt (by norm_num) (by norm_num) (by norm_num)
example : 0 < MI (bscJoint (1 / 4)) := bsc_MI_pos (by norm_num) (by norm_num)
/-- A perfect demon (`ε = 0`) gets the full `log 2` nats: one bit. -/
example : MI (bscJoint 0) = log 2 := by rw [bsc_MI_all]; simp [h]

end P2NoisyDemon
