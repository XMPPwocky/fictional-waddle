import Mathlib

/-!
# Collider cost of nonlocality

Notes: `notes/COLLIDER_NONLOCALITY.md`. Numerics: `toys/collider_nonlocality/`.

A two-party Bell scenario has finite input types `X`, `Y` and finite output types `A`, `B`.
A box is `p : A → B → X → Y → ℝ`, read as `p a b x y = P(a, b | x, y)`.
An abort or no-click is modelled by `Option`, with `none` meaning no click.

Status in Lean (no `sorry` anywhere in this file).

PROVED (unconditional):
* `lossy_local_mono`: a party can turn clicks into no-clicks locally. The hypotheses `hA`, `hB`
  are not needed.
* `mix_asymmetric`: mix the two one-sided models, then add shared double no-clicks. The
  hypotheses `hp`, `hns` are not needed.
* Closure lemmas used by both: `isLocal_congr`, `isLocal_add_smul`, `isLocal_detBox`,
  `sum_alice_signedLocal`, `isLocal_aliceConst`.

CONDITIONAL:
* `xor_garg_mermin_envelope_of`: the Garg–Mermin envelope, proved from the two named hypotheses
  `FirstCommonClick X Y Bool Bool` and `XorNegativityLeInvEff X Y`.

STATED AS `Prop`, NOT PROVED HERE (each `def` keeps the original statement exactly):
* `FirstCommonClick`: proved on paper in the notes (repeat the lossy model; each party keeps its
  first click).
* `GuessOneSided`: proved on paper (Bob clicks only when his input equals a shared guess).
* `TwoInputEff`: proved on paper (cell-counting over rectangles, plus `GuessOneSided`).
* `XorNegativityLeInvEff`: proved on paper (correlators: `[-1,1]^X = conv {±1}^X`).
* `LLRNegativityBound`: a known theorem (Laplante–Lerays–Roland, arXiv:1203.4155, Thm 7).
* `NegativityLeInvEffConjecture`: CONJECTURE. Supported by LP-exact numerics; no counterexample
  found.
-/

open Finset BigOperators

namespace ColliderNonlocality

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]

/-- A behaviour ("box"): `p a b x y = P(a, b | x, y)`. -/
abbrev Box (X Y A B : Type*) := A → B → X → Y → ℝ

/-- Nonnegative entries, normalized for every input pair. -/
def IsBox (p : Box X Y A B) : Prop :=
  (∀ a b x y, 0 ≤ p a b x y) ∧ ∀ x y, ∑ a, ∑ b, p a b x y = 1

/-- No-signalling: Alice's marginal does not depend on `y`, and Bob's does not depend on `x`. -/
def NoSignal (p : Box X Y A B) : Prop :=
  (∀ a x y y', ∑ b, p a b x y = ∑ b, p a b x y') ∧
  (∀ b x x' y, ∑ a, p a b x y = ∑ a, p a b x' y)

/-- The deterministic local box of the strategies `f : X → A` and `g : Y → B`. -/
def detBox (f : X → A) (g : Y → B) : Box X Y A B :=
  fun a b x y => if f x = a ∧ g y = b then 1 else 0

/-- `q` is a signed weighting of the deterministic boxes that sums to `p` (Al-Safi–Short). -/
def SignedLocal (p : Box X Y A B) (q : (X → A) × (Y → B) → ℝ) : Prop :=
  ∀ a b x y, p a b x y = ∑ s, q s * detBox s.1 s.2 a b x y

/-- Local: a signed local decomposition whose weights are all nonnegative. -/
def IsLocal (p : Box X Y A B) : Prop :=
  ∃ q, SignedLocal p q ∧ ∀ s, 0 ≤ q s

/-- Negativity `M*(p) = min ‖q‖₁` over signed local decompositions. This is DKLR's `ν̃` and
LLR's `ν`. -/
noncomputable def negativity (p : Box X Y A B) : ℝ :=
  sInf {m | ∃ q, SignedLocal p q ∧ ∑ s, |q s| = m}

/-- Local fraction (EPR2): the largest `λ` such that `p = λ L + (1-λ) R`, where `L` is a local box and
`R` is a no-signalling box. -/
noncomputable def localFraction (p : Box X Y A B) : ℝ :=
  sSup {l | 0 ≤ l ∧ l ≤ 1 ∧ ∃ L R : Box X Y A B, IsBox L ∧ IsLocal L ∧ IsBox R ∧ NoSignal R ∧
    ∀ a b x y, p a b x y = l * L a b x y + (1 - l) * R a b x y}

/-- The click-click part of a partial deterministic strategy pair, where `none` means abort. -/
def partialBox (f : X → Option A) (g : Y → Option B) : Box X Y A B :=
  fun a b x y => if f x = some a ∧ g y = some b then 1 else 0

/-- Joint-abort ("pure collider") model with success probability `ζ`. A probability `μ` over
partial deterministic strategy pairs (shared randomness; each abort depends only on the party's own
input) must make the click-click part equal to `ζ • p` for every input pair. Hence
P(both click | x,y) = ζ, and conditioned on both clicking the output is `p`. The one-sided events are
unconstrained. This is LLR's zero-communication protocol with abort; `eff = 1/ζ_max`. -/
def JointAbort (p : Box X Y A B) (ζ : ℝ) : Prop :=
  ∃ μ : (X → Option A) × (Y → Option B) → ℝ, (∀ s, 0 ≤ μ s) ∧ ∑ s, μ s = 1 ∧
    ∀ a b x y, ∑ s, μ s * partialBox s.1 s.2 a b x y = ζ * p a b x y

/-- The standard lossy box. Detectors click independently with probabilities `ηA` and `ηB`. When
only one party clicks, it outputs its marginal of `p`, read at the same input pair; for no-signalling
`p` that is the marginal. Outcome `none` is "no click". -/
def lossy (p : Box X Y A B) (ηA ηB : ℝ) : Box X Y (Option A) (Option B) :=
  fun oa ob x y =>
    match oa, ob with
    | some a, some b => ηA * ηB * p a b x y
    | some a, none   => ηA * (1 - ηB) * ∑ b, p a b x y
    | none,   some b => (1 - ηA) * ηB * ∑ a, p a b x y
    | none,   none   => (1 - ηA) * (1 - ηB)

/-! ## Closure lemmas for `IsLocal` -/

set_option linter.unusedSectionVars false

theorem isLocal_congr {p p' : Box X Y A B} (h : ∀ a b x y, p a b x y = p' a b x y)
    (hp : IsLocal p) : IsLocal p' := by
  obtain ⟨q, hq, hq0⟩ := hp
  exact ⟨q, fun a b x y => (h a b x y).symm.trans (hq a b x y), hq0⟩

/-- Nonnegative combinations of local boxes are local. -/
theorem isLocal_add_smul {p₁ p₂ : Box X Y A B} (h₁ : IsLocal p₁) (h₂ : IsLocal p₂) {c₁ c₂ : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    IsLocal (fun a b x y => c₁ * p₁ a b x y + c₂ * p₂ a b x y) := by
  obtain ⟨q₁, hq₁, hq₁0⟩ := h₁
  obtain ⟨q₂, hq₂, hq₂0⟩ := h₂
  refine ⟨fun s => c₁ * q₁ s + c₂ * q₂ s, fun a b x y => ?_, fun s =>
    add_nonneg (mul_nonneg hc₁ (hq₁0 s)) (mul_nonneg hc₂ (hq₂0 s))⟩
  show c₁ * p₁ a b x y + c₂ * p₂ a b x y = ∑ s, (c₁ * q₁ s + c₂ * q₂ s) * detBox s.1 s.2 a b x y
  rw [hq₁ a b x y, hq₂ a b x y, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- A deterministic box is local. -/
theorem isLocal_detBox (f : X → A) (g : Y → B) : IsLocal (detBox f g) := by
  classical
  refine ⟨fun s => if s = (f, g) then 1 else 0, fun a b x y => ?_, fun s => by
    dsimp only; split_ifs <;> norm_num⟩
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Summing a signed local decomposition over Alice's outputs keeps only Bob's indicator. -/
theorem sum_alice_signedLocal {p : Box X Y A B} {q : (X → A) × (Y → B) → ℝ}
    (hq : SignedLocal p q) (b : B) (x : X) (y : Y) :
    ∑ a, p a b x y = ∑ s, q s * (if s.2 y = b then 1 else 0) := by
  have hq' : ∀ a, p a b x y = ∑ s, q s * detBox s.1 s.2 a b x y := fun a => hq a b x y
  simp only [hq', detBox]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  simp only [ite_and, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- If `P` is local, so is the box in which Alice always outputs `a₀` and Bob keeps his marginal
of `P`. -/
theorem isLocal_aliceConst {P : Box X Y A B} (hP : IsLocal P) (a₀ : A) :
    IsLocal (fun a b x y => if a = a₀ then ∑ a', P a' b x y else 0) := by
  classical
  obtain ⟨q, hq, hq0⟩ := hP
  refine ⟨fun s => if s.1 = (fun _ => a₀) then ∑ f, q (f, s.2) else 0, fun a b x y => ?_,
    fun s => by
      dsimp only
      split_ifs
      · exact Finset.sum_nonneg fun f _ => hq0 _
      · exact le_refl _⟩
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (fun _ : X => a₀)
    (fun f _ hf => Finset.sum_eq_zero fun g _ => by simp [hf])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp only [↓reduceIte]
  split_ifs with ha
  · rw [sum_alice_signedLocal hq b x y, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp [detBox, ha]
  · refine (Finset.sum_eq_zero fun g _ => ?_).symm
    have : a₀ ≠ a := Ne.symm ha
    simp [detBox, this]

/-- Monotonicity. If the lossy box is local at `(ηA, ηB)`, it is local at `(t ηA, ηB)` for every
`t ∈ [0,1]`. Alice turns each click into a no-click with probability `1-t`, independently of
everything else. -/
theorem lossy_local_mono (p : Box X Y A B) (hp : IsBox p) (ηA ηB t : ℝ)
    (hA : 0 ≤ ηA ∧ ηA ≤ 1) (hB : 0 ≤ ηB ∧ ηB ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (hloc : IsLocal (lossy p ηA ηB)) : IsLocal (lossy p (t * ηA) ηB) := by
  refine isLocal_congr ?_ (isLocal_add_smul hloc (isLocal_aliceConst hloc none) ht.1
    (sub_nonneg.mpr ht.2))
  intro oa ob x y
  have hn : ∑ a, ∑ b, p a b x y = 1 := hp.2 x y
  cases oa with
  | none =>
    cases ob with
    | none =>
      simp only [lossy, Fintype.sum_option, ↓reduceIte, ← Finset.mul_sum, hn]
      ring
    | some b =>
      simp only [lossy, Fintype.sum_option, ↓reduceIte, ← Finset.mul_sum]
      ring
  | some a =>
    cases ob with
    | none => simp [lossy]; ring
    | some b => simp [lossy]; ring

/-- FIRST COMMON CLICK (stated, not proved here). Suppose the lossy box is local at `(ηA, ηB)`.
Then `p` has a joint-abort model with success `ηA ηB / (ηA + ηB - ηA ηB)`, which is
P(both click | not both silent). On paper: run independent copies; each party outputs its first
click; the attempt succeeds when both first clicks fall in the same copy. Only P(cc) and P(⊥⊥),
both input-independent, enter. Truncating to finitely many copies and using closedness of the
(finite) LP gives exact attainment. -/
def FirstCommonClick (X Y A B : Type*) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] : Prop :=
  ∀ (p : Box X Y A B), IsBox p → ∀ (ηA ηB : ℝ), (0 < ηA ∧ ηA ≤ 1) → (0 < ηB ∧ ηB ≤ 1) →
    IsLocal (lossy p ηA ηB) → JointAbort p (ηA * ηB / (ηA + ηB - ηA * ηB))

/-- MIXING CONVERSE. If both one-sided lossy boxes `(1, ζ)` and `(ζ, 1)` are local, then the
symmetric lossy box at `η = 2ζ/(1+ζ)` is local. Proof: mix the two halves 1/2 : 1/2, then add a
shared "both silent" event with probability `((1-ζ)/(1+ζ))²`. -/
theorem mix_asymmetric (p : Box X Y A B) (hp : IsBox p) (hns : NoSignal p) (ζ : ℝ)
    (hζ : 0 < ζ ∧ ζ ≤ 1)
    (h1 : IsLocal (lossy p 1 ζ)) (h2 : IsLocal (lossy p ζ 1)) :
    IsLocal (lossy p (2 * ζ / (1 + ζ)) (2 * ζ / (1 + ζ))) := by
  have hpos : 0 < 1 + ζ := by linarith
  have hc : 0 ≤ 2 * ζ / (1 + ζ) ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
  have hw : 0 ≤ ((1 - ζ) / (1 + ζ)) ^ 2 := sq_nonneg _
  refine isLocal_congr ?_ (isLocal_add_smul h1
    (isLocal_add_smul h2 (isLocal_detBox (fun _ : X => (none : Option A))
      (fun _ : Y => (none : Option B))) hc hw) hc zero_le_one)
  intro oa ob x y
  cases oa with
  | none =>
    cases ob with
    | none => simp only [lossy, detBox, and_self, ↓reduceIte]; field_simp; ring
    | some b => simp [lossy, detBox]; field_simp; ring
  | some a =>
    cases ob with
    | none => simp [lossy, detBox]; field_simp; ring
    | some b => simp [lossy, detBox]; field_simp; ring

/-- GUESS PROTOCOL, one-sided (stated, not proved here). Let `p = λ L + (1-λ) R`, with `L` local,
`R` a no-signalling box, and `L` having the same Alice marginals as `p`. Then the one-sided lossy
box `(1, ζ)` is local, where `ζ = 1/(m - (m-1) λ)` and `m = |Y|`. Proof on paper: with weight
`λζ`, run `L` with Bob always clicking. With the remaining weight, Bob clicks iff `y` equals a
shared uniform guess `g`; Alice samples from `R(·|x,g)` jointly with the shared `b`. With `λ = 0`
(`L` arbitrary), this gives the universal bound `η_B ≥ 1/|Y|`. -/
def GuessOneSided (X Y A B : Type*) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] : Prop :=
  ∀ (p L R : Box X Y A B), IsBox p → NoSignal p → (IsBox L ∧ IsLocal L) → (IsBox R ∧ NoSignal R) →
    ∀ (l : ℝ), (0 ≤ l ∧ l ≤ 1) →
    (∀ a b x y, p a b x y = l * L a b x y + (1 - l) * R a b x y) →
    (∀ a x y, ∑ b, L a b x y = ∑ b, p a b x y) → 0 < Fintype.card Y →
    IsLocal (lossy p 1 (1 / ((Fintype.card Y : ℝ) - ((Fintype.card Y : ℝ) - 1) * l)))

/-- TWO INPUTS EACH, outputs arbitrary (stated, not proved here). The joint-abort success never
exceeds `1/(2 - LF)`, and this value is achieved (by the guess protocol). So `eff(p) = 2 - LF(p)`
exactly. The bound comes from counting cells: every rectangle other than the full one covers at
most 2 of the 4 input cells. -/
def TwoInputEff (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] : Prop :=
  ∀ (p : Box (Fin 2) (Fin 2) A B), IsBox p → NoSignal p →
    JointAbort p (1 / (2 - localFraction p)) ∧
    ∀ ζ, JointAbort p ζ → ζ ≤ 1 / (2 - localFraction p)

/-- Uniform marginals for binary outputs. -/
def UniformMarginals (p : Box X Y Bool Bool) : Prop :=
  (∀ a x y, ∑ b, p a b x y = 1 / 2) ∧ (∀ b x y, ∑ a, p a b x y = 1 / 2)

/-- XOR CASE (stated, not proved here): negativity ≤ inverse joint efficiency, for binary boxes
with uniform marginals and any number of inputs. Proof on paper: the correlator of a partial
strategy is `α βᵀ` with `α ∈ {-1,0,1}^X`, which lies in `[-1,1]^X = conv {±1}^X`. Hence `ζ E` is
a local correlator, so `ν(E) ≤ 1/ζ`. Also `M*(p) = max(1, ν(E))` (DKLR Thm 4, together with sign
flips and a global symmetrization). -/
def XorNegativityLeInvEff (X Y : Type*) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] :
    Prop :=
  ∀ (p : Box X Y Bool Bool), IsBox p → NoSignal p → UniformMarginals p →
    ∀ (ζ : ℝ), 0 < ζ → JointAbort p ζ → negativity p ≤ 1 / ζ

theorem negativity_nonneg (p : Box X Y A B) : 0 ≤ negativity p := by
  apply Real.sInf_nonneg
  rintro m ⟨q, _, rfl⟩
  exact Finset.sum_nonneg fun s _ => abs_nonneg _

/-- GARG–MERMIN ENVELOPE for XOR boxes, CONDITIONAL on `FirstCommonClick X Y Bool Bool` and
`XorNegativityLeInvEff X Y`. If the symmetric lossy box is local at `η`, then
`η ≤ 2/(1+M*)`. Equivalently, every efficiency above `2/(1+M*)` gives a valid
detection-loophole-free witness. For 2-input uniform-marginal binary boxes this is an equality
with `M* = S/2`, which is Larsson's `4/(2+S)`. The equality is stated separately in the notes and
not here. -/
theorem xor_garg_mermin_envelope_of (hFCC : FirstCommonClick X Y Bool Bool)
    (hXOR : XorNegativityLeInvEff X Y)
    (p : Box X Y Bool Bool) (hp : IsBox p) (hns : NoSignal p)
    (hu : UniformMarginals p) (η : ℝ) (hη : 0 < η ∧ η ≤ 1)
    (hloc : IsLocal (lossy p η η)) :
    η ≤ 2 / (1 + negativity p) := by
  obtain ⟨hη0, hη1⟩ := hη
  have hJ := hFCC p hp η η ⟨hη0, hη1⟩ ⟨hη0, hη1⟩ hloc
  have h2η : 0 < 2 - η := by linarith
  have hζ : η * η / (η + η - η * η) = η / (2 - η) := by
    rw [show η + η - η * η = η * (2 - η) by ring]
    field_simp
  rw [hζ] at hJ
  have hM := hXOR p hp hns hu (η / (2 - η)) (div_pos hη0 h2η) hJ
  rw [one_div_div] at hM
  have hM0 := negativity_nonneg p
  rw [le_div_iff₀ (by linarith)]
  have : negativity p * η ≤ 2 - η := by
    rwa [le_div_iff₀ hη0] at hM
  nlinarith

/-- KNOWN (Laplante–Lerays–Roland, ICALP 2012, arXiv:1203.4155, Thm 7), stated, not proved here:
`ν ≤ 2 eff`, i.e. `negativity p ≤ 2/ζ`. A literature check reported that the proof gives
`2 eff - 1`; we have not re-derived that, so the stated form is used here. -/
def LLRNegativityBound (X Y A B : Type*) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] : Prop :=
  ∀ (p : Box X Y A B), IsBox p → NoSignal p →
    ∀ (ζ : ℝ), 0 < ζ → JointAbort p ζ → negativity p ≤ 2 / ζ

/-- CONJECTURE (LP-exact numerics, no counterexample): `ν ≤ eff` for every no-signalling box.
Postselection can always be traded for negativity at no loss. Equality fails in general: CGLMP-3
and some 3322 boxes give strict inequality. -/
def NegativityLeInvEffConjecture (X Y A B : Type*) [Fintype X] [Fintype Y] [Fintype A]
    [Fintype B] [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] : Prop :=
  ∀ (p : Box X Y A B), IsBox p → NoSignal p →
    ∀ (ζ : ℝ), 0 < ζ → JointAbort p ζ → negativity p ≤ 1 / ζ

end ColliderNonlocality
