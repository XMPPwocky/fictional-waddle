import Mathlib

/-!
# Barato–Seifert coherence bound: statements only, as `Prop`s (nothing here is proved in Lean)

No `sorry`: each statement is a `def ... : Prop` that keeps the original statement exactly and
claims no proof. Nothing in this file is proved in Lean.

Convention: `Q i j` (i ≠ j) is the jump rate i → j; rows sum to zero. Eigenvalues are those of
`Q.map ofReal` acting on column vectors (right eigenvectors). `Qᵀ` (the Barato–Seifert `L`) has
the same spectrum.

* S1 `GeneratorSector` (STATED, NOT PROVED HERE): every eigenvalue satisfies |Im μ| ≤ cot(π/N)·|Re μ|. This is the A → ∞
  limit of the Barato–Seifert bound. It is classical (Dmitriev–Dynkin 1945/46 via P = I + εQ). Our
  notes give a short direct proof.
* S2 `GeneratorSectorHull` (STATED, NOT PROVED HERE): the refinement where N is replaced by the number m of extreme points
  of the convex hull of the eigenvector's components. Our notes prove it. (Novelty unchecked; it is
  probably folklore.)
* S3 `BaratoSeifertBound` (STATED, NOT PROVED HERE): the full bound with cycle affinities. Proved by Ohga, Ito and Kolchinsky,
  PRL 131, 077101 (2023). We did NOT prove it here; it is stated as a formalisation target.
-/

open Matrix Complex

namespace BaratoSeifert

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A continuous-time Markov generator: off-diagonal rates are nonnegative and rows sum to zero. -/
def IsGenerator (Q : Matrix ι ι ℝ) : Prop :=
  (∀ i j, i ≠ j → 0 ≤ Q i j) ∧ ∀ i, ∑ j, Q i j = 0

/-- S1 (sector lemma), stated as a `Prop`, not proved here. Every complex eigenvalue `μ` of an `N`-state generator satisfies
`|Im μ| ≤ cot(π/N) |Re μ|`. There is no irreducibility hypothesis. -/
def GeneratorSector (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (Q : Matrix ι ι ℝ), IsGenerator Q → 2 ≤ Fintype.card ι →
    ∀ (μ : ℂ) (v : ι → ℂ), v ≠ 0 → (Q.map ((↑) : ℝ → ℂ)) *ᵥ v = μ • v →
    |μ.im| ≤ Real.cot (Real.pi / Fintype.card ι) * |μ.re|

/-- S2 (convex-hull refinement), stated as a `Prop`, not proved here. Assume a strictly positive stationary vector exists (true for
every irreducible generator). Then the bound holds with `N` replaced by the number `m` of extreme
points of `conv {v i}` ⊆ ℂ ≅ ℝ². For `m ≤ 2` the right side is `0` (in Lean `cot (π/1) = 0` and
`cot (π/2) = 0`), so the statement then says `μ` is real. -/
def GeneratorSectorHull (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (Q : Matrix ι ι ℝ), IsGenerator Q →
    ∀ (q : ι → ℝ), (∀ i, 0 < q i) → q ᵥ* Q = 0 →
    ∀ (μ : ℂ) (v : ι → ℂ), v ≠ 0 → (Q.map ((↑) : ℝ → ℂ)) *ᵥ v = μ • v →
    |μ.im| ≤
      Real.cot (Real.pi / ((convexHull ℝ (Set.range v)).extremePoints ℝ).ncard) * |μ.re|

/-- Every edge of the support is reversible: `Q i j > 0 ↔ Q j i > 0` (so every cycle affinity is
finite). -/
def ReversibleSupport (Q : Matrix ι ι ℝ) : Prop := ∀ i j, i ≠ j → (0 < Q i j ↔ 0 < Q j i)

/-- A simple cycle of length `k`: `k` distinct states `c 0 → c 1 → ⋯ → c (k-1) → c 0`, with every
forward rate positive. -/
def IsSimpleCycle (Q : Matrix ι ι ℝ) {k : ℕ} (c : Fin k → ι) : Prop :=
  3 ≤ k ∧ Function.Injective c ∧
    ∀ t : Fin k, 0 < Q (c t) (c ⟨(t.val + 1) % k, Nat.mod_lt _ (by have := t.isLt; omega)⟩)

/-- Cycle affinity `F_c = Σ log(forward rate / backward rate)`. -/
noncomputable def cycleAffinity (Q : Matrix ι ι ℝ) {k : ℕ} (c : Fin k → ι) : ℝ :=
  ∑ t : Fin k,
    if h : 0 < k then
      Real.log (Q (c t) (c ⟨(t.val + 1) % k, Nat.mod_lt _ h⟩) /
                Q (c ⟨(t.val + 1) % k, Nat.mod_lt _ h⟩) (c t))
    else 0

/-- S3, stated as a `Prop`, not proved here (Barato–Seifert conjecture, PRE 95 062409 (2017), eq. (7); proved by Ohga–Ito–Kolchinsky,
PRL 131 077101 (2023), Eq. (10), for every mode). For every eigenvalue `μ`, either `μ` is real, or
some simple cycle `c` of length `k` satisfies `|Im μ| ≤ cot(π/k) · tanh(|F_c|/(2k)) · |Re μ|`. The
existential is equivalent to the paper's max over cycles. -/
def BaratoSeifertBound (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (Q : Matrix ι ι ℝ), IsGenerator Q → ReversibleSupport Q →
    ∀ (q : ι → ℝ), (∀ i, 0 < q i) → q ᵥ* Q = 0 →
    ∀ (μ : ℂ) (v : ι → ℂ), v ≠ 0 → (Q.map ((↑) : ℝ → ℂ)) *ᵥ v = μ • v →
    μ.im = 0 ∨ ∃ (k : ℕ) (c : Fin k → ι), IsSimpleCycle Q c ∧
      |μ.im| ≤ Real.cot (Real.pi / k) * Real.tanh (|cycleAffinity Q c| / (2 * k)) * |μ.re|

end BaratoSeifert
