import Mathlib

/-!
# Every pattern is selected by something; only private randomization says by what

The heuristic: "any pattern happens because it's selected for by something, maybe retrocausally in my counterfactual
anti-self". Split into finite, exact statements:

* A1 `selection_universal`: any change of distribution `p → q` (with `q ≪ p`) is one selection step. The fitness is the
  likelihood ratio, and the change in any trait mean is the covariance of that fitness with the trait (Price, no
  transmission term). A1' `selection_fitness_unique`: on the support the fitness is unique.
* A2 `postselection_is_selection`: conditioning the present on a future event is selection with fitness
  `h x = P(future ∈ E | x)`: the backward message, i.e. how well my counterfactual continuations do.
* B1 `tag_reads_average_effect`: correlating any outcome with a private fair coin returns exactly the average causal
  effect of flipping that coin, with any nonlinearity (discrete Stein / first Fourier coefficient).
* B2 `common_cause_invisible`, B3 `tag_corr_add`, B3' `independent_injection_invisible`: the tag is blind to anything not
  caused by the coin, and additive. So only injections that depend on the coin (spoofers) can bias it.
* B4 `law_without_channel`: a shared seed makes you perfectly predictable from my seed while my private tag reads zero.
* C1 `hamilton_from_shared_seed`: with wiggles δ = α·s + β·ξ (s shared with kin, ξ private), the policy-level selection
  gradient is α²·b − c·(α² + β²) (Hamilton's rule with r = the shared-seed fraction α²), while the private-tag gradient
  sees only −c·β.
* C2 `antithetic_reads_curvature`: an antithetic pair of wiggles reads R + a·σ² = R + ½σ²R'' on any quadratic:
  selection under wiggles already sees the Hessian.
* D1 `no_tag_no_self`: with a deterministic policy, a world where my actions do nothing (it echoes itself) produces the
  pathwise-identical trajectory.
-/

open Finset

namespace SelectionUniversal

variable {α : Type*} [Fintype α]

/-- Expectation of `z` under weights `p`. -/
def E (p z : α → ℝ) : ℝ := ∑ x, p x * z x

/-- Covariance of `w` and `z` under weights `p`. -/
def Cov (p w z : α → ℝ) : ℝ := E p (fun x => w x * z x) - E p w * E p z

/-- **A1.** Every change of distribution is one selection step: the fitness is the likelihood ratio, and every trait mean
moves by its covariance with that fitness. -/
theorem selection_universal (p q : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hq1 : ∑ x, q x = 1) (hac : ∀ x, p x = 0 → q x = 0) :
    ∃ w : α → ℝ, (∀ x, 0 ≤ w x) ∧ E p w = 1 ∧ (∀ x, q x = p x * w x) ∧
      ∀ z : α → ℝ, E q z - E p z = Cov p w z := by
  classical
  let w : α → ℝ := fun x => if p x = 0 then 0 else q x / p x
  have key : ∀ x, p x * w x = q x := by
    intro x; simp only [w]; split_ifs with h
    · simp [h, hac x h]
    · field_simp
  have hE : E p w = 1 := by simp only [E, key]; exact hq1
  refine ⟨w, ?_, hE, fun x => (key x).symm, ?_⟩
  · intro x; simp only [w]; split_ifs
    · exact le_refl _
    · exact div_nonneg (hq x) (hp x)
  · intro z
    have h2 : E p (fun x => w x * z x) = E q z := by
      simp only [E]; apply sum_congr rfl; intro x _; rw [← mul_assoc, key]
    simp only [Cov, h2, hE]; ring

/-- **A1'.** On the support of `p`, the selecting fitness is unique. -/
theorem selection_fitness_unique (p q w w' : α → ℝ) (hw : ∀ x, q x = p x * w x) (hw' : ∀ x, q x = p x * w' x)
    (x : α) (hx : p x ≠ 0) : w x = w' x := by
  exact mul_left_cancel₀ hx ((hw x).symm.trans (hw' x))

/-- **A2.** Postselection is selection by the future. With joint weights `p x * K x y` (present `x`, future `y`),
conditioning on the future landing in `F` moves every trait mean of the present by its covariance with the normalized
backward message `h x / Z`, where `h x = ∑ y ∈ F, K x y`. -/
theorem postselection_is_selection {β : Type*} [Fintype β] (p : α → ℝ) (hp1 : ∑ x, p x = 1) (K : α → β → ℝ)
    (F : Finset β) (hZ : 0 < ∑ x, p x * ∑ y ∈ F, K x y) (z : α → ℝ) :
    (∑ x, (∑ y ∈ F, p x * K x y) * z x) / (∑ x, ∑ y ∈ F, p x * K x y) - E p z
      = Cov p (fun x => (∑ y ∈ F, K x y) / (∑ x', p x' * ∑ y ∈ F, K x' y)) z := by
  have hZne : (∑ x, p x * ∑ y ∈ F, K x y) ≠ 0 := ne_of_gt hZ
  have hden : ∑ x, ∑ y ∈ F, p x * K x y = ∑ x, p x * ∑ y ∈ F, K x y := by simp [Finset.mul_sum]
  have hnum : ∑ x, (∑ y ∈ F, p x * K x y) * z x = ∑ x, p x * (∑ y ∈ F, K x y) * z x := by
    apply sum_congr rfl; intro x _; rw [Finset.mul_sum]
  have hw1 : ∑ x, p x * ((∑ y ∈ F, K x y) / (∑ x', p x' * ∑ y ∈ F, K x' y)) = 1 := by
    rw [show ∑ x, p x * ((∑ y ∈ F, K x y) / (∑ x', p x' * ∑ y ∈ F, K x' y))
        = (∑ x, p x * ∑ y ∈ F, K x y) / (∑ x', p x' * ∑ y ∈ F, K x' y) by
          rw [Finset.sum_div]; apply sum_congr rfl; intro x _; ring]
    exact div_self hZne
  have hwz : ∑ x, p x * ((∑ y ∈ F, K x y) / (∑ x', p x' * ∑ y ∈ F, K x' y) * z x)
      = (∑ x, p x * (∑ y ∈ F, K x y) * z x) / (∑ x', p x' * ∑ y ∈ F, K x' y) := by
    rw [Finset.sum_div]; apply sum_congr rfl; intro x _; ring
  simp only [Cov, E]
  rw [hden, hnum, hw1, hwz]; ring

/-- The sign of a fair coin. -/
def sg (b : Bool) : ℝ := if b then 1 else -1

variable {Ω : Type*} [Fintype Ω]

/-- Correlation of an outcome `y coin world` with my private fair coin; the world has weights `μ`, independent of the coin. -/
noncomputable def tagCorr (μ : Ω → ℝ) (y : Bool → Ω → ℝ) : ℝ := ∑ ω, ∑ b : Bool, (μ ω / 2) * (y b ω * sg b)

/-- **B1.** Correlation with a private fair coin equals the average causal effect of flipping it, exactly, for any
nonlinear outcome. -/
theorem tag_reads_average_effect (μ : Ω → ℝ) (y : Bool → Ω → ℝ) :
    tagCorr μ y = ∑ ω, μ ω * ((y true ω - y false ω) / 2) := by
  unfold tagCorr; apply sum_congr rfl; intro ω _
  simp [Fintype.sum_bool, sg]; ring

/-- **B2.** Anything the coin does not cause is invisible to the tag, however it depends on the rest of the world. -/
theorem common_cause_invisible (μ : Ω → ℝ) (y : Ω → ℝ) : tagCorr μ (fun _ ω => y ω) = 0 := by
  rw [tag_reads_average_effect]; simp

/-- **B3.** The tag reading is additive, so an injected signal `s` adds its own reading. -/
theorem tag_corr_add (μ : Ω → ℝ) (y s : Bool → Ω → ℝ) :
    tagCorr μ (fun b ω => y b ω + s b ω) = tagCorr μ y + tagCorr μ s := by
  rw [tag_reads_average_effect, tag_reads_average_effect, tag_reads_average_effect, ← sum_add_distrib]
  apply sum_congr rfl; intro ω _; ring

/-- **B3'.** An injection that does not depend on my coin cannot bias my self-map; only one that knows the coin can. -/
theorem independent_injection_invisible (μ : Ω → ℝ) (y : Bool → Ω → ℝ) (s : Ω → ℝ) :
    tagCorr μ (fun b ω => y b ω + s ω) = tagCorr μ y := by
  rw [tag_reads_average_effect, tag_reads_average_effect]
  apply sum_congr rfl; intro ω _; ring

/-- **B4.** Law without a channel: you act on our shared seed `d`. You are perfectly predictable from my seed (the
covariance is 1), yet my private tag reads zero effect. -/
theorem law_without_channel :
    tagCorr (fun _ : Bool => (1 : ℝ) / 2) (fun _ d => sg d) = 0 ∧
      ∑ d : Bool, ∑ b : Bool, ((1 : ℝ) / 2 / 2) * (sg d * sg d) = 1 := by
  refine ⟨common_cause_invisible _ _, ?_⟩
  simp [Fintype.sum_bool, sg]; norm_num

/-- **C1.** Hamilton's rule from shared seeds. My wiggle is `α·s + β·ξi`, my kin's is `α·s + β·ξj` (s shared; ξi, ξj
private; all fair coins); my payoff is `-c·(mine) + b·(kin's)`. The policy-level selection gradient (covariance with my
whole wiggle) is `α²·b − c·(α² + β²)`; the private-tag gradient is `−c·β`: it never sees the kin benefit. -/
theorem hamilton_from_shared_seed (a β b c : ℝ) :
    (∑ s : Bool, ∑ ξi : Bool, ∑ ξj : Bool, (1 / 8 : ℝ) *
        ((-c * (a * sg s + β * sg ξi) + b * (a * sg s + β * sg ξj)) * (a * sg s + β * sg ξi)))
      = a ^ 2 * b - c * (a ^ 2 + β ^ 2) ∧
    (∑ s : Bool, ∑ ξi : Bool, ∑ ξj : Bool, (1 / 8 : ℝ) *
        ((-c * (a * sg s + β * sg ξi) + b * (a * sg s + β * sg ξj)) * sg ξi)) = -c * β := by
  constructor <;> simp [Fintype.sum_bool, sg] <;> ring

/-- **C2.** Selection under an antithetic wiggle reads the curvature: on a quadratic, the average over ±σ is
`R θ + a·σ²` (= R + ½σ²R''). -/
theorem antithetic_reads_curvature (a b c θ σ : ℝ) :
    ((a * (θ + σ) ^ 2 + b * (θ + σ) + c) + (a * (θ - σ) ^ 2 + b * (θ - σ) + c)) / 2
      = (a * θ ^ 2 + b * θ + c) + a * σ ^ 2 := by
  ring

/-- The closed loop `y (t+1) = h · g (y t) + w (t+1)` with a deterministic policy `g`. -/
def traj (h : ℝ) (g : ℝ → ℝ) (w : ℕ → ℝ) (y0 : ℝ) : ℕ → ℝ
  | 0 => y0
  | t + 1 => h * g (traj h g w y0 t) + w (t + 1)

/-- **D1.** No tag, no self: a world where my actions have no effect (`h = 0`) and the noise echoes the original loop
reproduces the trajectory exactly, for every realization. -/
theorem no_tag_no_self (h : ℝ) (g : ℝ → ℝ) (w : ℕ → ℝ) (y0 : ℝ) (t : ℕ) :
    traj 0 g (fun k => match k with
      | 0 => w 0
      | j + 1 => w (j + 1) + h * g (traj h g w y0 j)) y0 t = traj h g w y0 t := by
  cases t with
  | zero => simp [traj]
  | succ k => simp [traj]; ring

/-! ## The knot: Heaven ↔ Abyss through True Neutral

Coordinates `(σ, κ)`: legibility (Law > 0 > Chaos) and credit (Good > 0 > Evil). Heaven = (+,+), Abyss = (−,−),
Hell = (+,−), Elysium = (−,+), True Neutral = (0,0). The "charge" `sign(σ·κ)` is + on Heaven/Abyss, − on Hell/Elysium. -/

/-- Helper: a nonnegative product puts the point in a closed same-sign quadrant. -/
lemma quad_of_mul_nonneg {x y : ℝ} (h : 0 ≤ x * y) : (0 ≤ x ∧ 0 ≤ y) ∨ (x ≤ 0 ∧ y ≤ 0) := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · exact Or.inl ⟨hx, hy⟩
  · have h0 : x * y = 0 := le_antisymm (by nlinarith) h
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact Or.inr ⟨h1.le, hy⟩
    · exact Or.inl ⟨hx, h1.ge⟩
  · have h0 : x * y = 0 := le_antisymm (by nlinarith) h
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact Or.inl ⟨h1.ge, hy⟩
    · exact Or.inr ⟨hx, h1.le⟩
  · exact Or.inr ⟨hx, hy⟩

/-- **E1.** A path that never flips the charge (`σ·κ ≥ 0` throughout) and runs from closed-Heaven to closed-Abyss must
pass exactly through True Neutral. -/
theorem charge_conserving_path_hits_neutral (γ : ℝ → ℝ × ℝ) (hγ : ContinuousOn γ (Set.Icc 0 1))
    (h0 : 0 ≤ (γ 0).1 ∧ 0 ≤ (γ 0).2) (h1 : (γ 1).1 ≤ 0 ∧ (γ 1).2 ≤ 0)
    (hq : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (γ t).1 * (γ t).2) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t = 0 := by
  have hA : IsClosed {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} :=
    (isClosed_le continuous_const continuous_fst).inter (isClosed_le continuous_const continuous_snd)
  have hB : IsClosed {p : ℝ × ℝ | p.1 ≤ 0 ∧ p.2 ≤ 0} :=
    (isClosed_le continuous_fst continuous_const).inter (isClosed_le continuous_snd continuous_const)
  have cA := hγ.preimage_isClosed_of_isClosed isClosed_Icc hA
  have cB := hγ.preimage_isClosed_of_isClosed isClosed_Icc hB
  obtain ⟨t, ht, ⟨_, htA⟩, ⟨_, htB⟩⟩ := (isPreconnected_closed_iff.1 isPreconnected_Icc) _ _ cA cB
    (by
      intro t ht
      rcases quad_of_mul_nonneg (hq t ht) with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr ⟨ht, h⟩)
    ⟨0, ⟨le_refl 0, zero_le_one⟩, ⟨le_refl 0, zero_le_one⟩, h0⟩
    ⟨1, ⟨zero_le_one, le_refl 1⟩, ⟨zero_le_one, le_refl 1⟩, h1⟩
  refine ⟨t, ht, Prod.ext ?_ ?_⟩
  · simpa using le_antisymm htB.1 htA.1
  · simpa using le_antisymm htB.2 htA.2

/-- **E2.** Knotted out: if True Neutral is lethal (fitness `f 0 = 0`) and a path must stay viable (`f > 0`), no
charge-conserving path joins Heaven to the Abyss. -/
theorem knotted_out (f : ℝ × ℝ → ℝ) (hf : f 0 = 0) (γ : ℝ → ℝ × ℝ) (hγ : ContinuousOn γ (Set.Icc 0 1))
    (h0 : 0 ≤ (γ 0).1 ∧ 0 ≤ (γ 0).2) (h1 : (γ 1).1 ≤ 0 ∧ (γ 1).2 ≤ 0)
    (hq : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (γ t).1 * (γ t).2) :
    ¬ ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < f (γ t) := by
  intro hall
  obtain ⟨t, ht, h⟩ := charge_conserving_path_hits_neutral γ hγ h0 h1 hq
  have := hall t ht
  rw [h, hf] at this
  exact lt_irrefl 0 this

/-- **E3.** An odd loop blocks the free mirror. A sublattice relabelling `J i j ↦ τ i * J i j * τ j` (`τ = ±1`) maps
every coupling of a triangle to its negative (ferro ↔ antiferro, Heaven ↔ Abyss) only if the loop product vanishes.
On a frustrated triangle (nonzero product) no relabelling turns Heaven into the Abyss. -/
theorem odd_loop_blocks_mirror (τ : Fin 3 → ℝ) (hτ : ∀ i, τ i ^ 2 = 1) (J01 J12 J20 : ℝ)
    (hJ : J01 * J12 * J20 ≠ 0) :
    ¬ (τ 0 * J01 * τ 1 = -J01 ∧ τ 1 * J12 * τ 2 = -J12 ∧ τ 2 * J20 * τ 0 = -J20) := by
  rintro ⟨h1, h2, h3⟩
  apply hJ
  have e : (τ 0 * J01 * τ 1) * (τ 1 * J12 * τ 2) * (τ 2 * J20 * τ 0) = -(J01 * J12 * J20) := by
    rw [h1, h2, h3]; ring
  have e2 : (τ 0 * J01 * τ 1) * (τ 1 * J12 * τ 2) * (τ 2 * J20 * τ 0)
      = (τ 0 ^ 2) * (τ 1 ^ 2) * (τ 2 ^ 2) * (J01 * J12 * J20) := by ring
  rw [e2, hτ 0, hτ 1, hτ 2] at e
  linarith

end SelectionUniversal
