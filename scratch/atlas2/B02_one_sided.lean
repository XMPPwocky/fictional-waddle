import Mathlib

/-!
# B02 — Creators without annihilators (one-sided shift, one fermion mode, no finite bosons)

## What is proved (pure mathematics)

(1) One-sided shift on sequences `ℕ → ℝ`:
`S f 0 = 0`, `S f (n+1) = f n` (creation / right shift) and `L f n = f (n+1)` (left shift).
* `L_comp_S`: `L ∘ S = id` (isometry identity `S*S = 1`); `S_leftInverse`: `LeftInverse L S`.
* `S_comp_L_ne`: `S ∘ L ≠ id`; witnessed by `exists_SL_ne` (the constant sequence `1`).
* `S_injective`, `S_not_surjective` (nothing maps to a sequence with `f 0 ≠ 0`),
  `S_no_right_inverse`: no `R` at all with `S ∘ R = id`.
* `LS_sub_SL`: `L (S f) - S (L f) = (vacuum projection) f`, i.e. the pointwise value is
  `if n = 0 then f 0 else 0` — the commutator `[L,S]` is the rank-one projector onto `δ₀`,
  not the identity.
* `sum_S_mul_eq_sum_mul_L`: exact finite identity
  `∑_{n<M+1} (S f) n * g n = ∑_{n<M} f n * (L g) n` (no hypotheses).
* `adjoint_finite_support`: if `f n = 0` for `n ≥ N` and `N ≤ M`, then
  `∑_{n<M+1} (S f) n * g n = ∑_{n<M+1} f n * (L g) n` (inner-product adjointness `⟨Sf,g⟩=⟨f,Lg⟩`
  on a window containing the support).

(2) One fermion mode, `a = !![0,1;0,0]` over `ℂ`, `a† := aᵀ` (and `conjTranspose_a`: `aᴴ = aᵀ`; `adag_eq`: `a† = !![0,0;1,0]`):
* `a_mul_a`: `a * a = 0`; `adag_mul_adag`: `a† * a† = 0`;
* `anticomm`: `a * a† + a† * a = 1`.

(3) No finite bosons: `no_finite_CCR` — over any field `K` of characteristic zero, for `n ≥ 1`
and `A B : Matrix (Fin n) (Fin n) K`, `A * B - B * A ≠ 1` (trace: `0 ≠ n`).
`no_finite_CCR_complex` is the `ℂ` instance; `no_finite_CCR_fintype` the same for any nonempty
finite index type.

(4) Majorana: `γ = a + a†` satisfies `gamma_hermitian : γᴴ = γ` and `gamma_sq : γ * γ = 1`.

(5) Going down (addition, second agent): `no_finite_one_sided` — for square matrices over any
commutative ring and any finite index type, `L * S = 1 → S * L = 1`. A finite-dimensional
one-sided isometry does not exist, so the `S`/`L` asymmetry in (1) needs infinitely many levels.
Concrete `example`s at the end check non-vacuity: `adjoint_finite_support` on `f = δ₀`
(both sides equal `1`), `S δ₀ = δ₁`, the 2-level truncated creator has `a * a† ≠ 1`, and an
invertible non-identity matrix satisfying the hypothesis of `no_finite_one_sided`.

## Interpretation (not proved; physics reading)

* `S` is the creation operator on the "occupation ladder" `ℕ`; `L ∘ S = id` with `S ∘ L ≠ id`
  shows a creator whose left inverse is not a two-sided inverse: the vacuum `δ₀` is not in the
  range of `S`. `LS_sub_SL` gives `[L,S] = |0⟩⟨0|`, trace 1, which is consistent with (3)
  because the trace argument needs finite dimension; on `ℓ²` the real CCR needs unbounded
  `√n` weights, which we do not formalise here.
* The fermion statements are just the Pauli-exclusion algebra `a² = 0`, `{a,a†} = 1` on `ℂ²`;
  `γ` is a self-adjoint unitary (Majorana) generator of a Clifford algebra with one generator.
* We use plain functions `ℕ → ℝ`, not `ℓ²`; "adjointness" is only the finite-window sum
  identity above, not a statement about `lp` adjoints.

## Changes from the task text

None in substance. Finite-support adjointness is stated with `Finset.range (M+1)` windows and
the support bound `∀ n, N ≤ n → f n = 0` with `N ≤ M`; `g` needs no support bound. Extra
lemmas (`LS_sub_SL`, `adag_eq`, `adag_mul_adag`, `conjTranspose_a`, `no_finite_CCR_fintype`) are additions.
Second-agent review: all statements above were kept verbatim; `no_finite_one_sided` and the
examples were appended. The only reading caveat: "adjointness" is a finite-window identity on
`ℕ → ℝ`, and the window must reach one past the support of `f` (`N ≤ M`, window `range (M+1)`),
because `S` moves the support up by one.
-/

namespace Atlas2.B02

open Matrix Finset

/-! ## (1) One-sided shift -/

/-- Right shift (creator): `S f 0 = 0`, `S f (n+1) = f n`. -/
def S (f : ℕ → ℝ) : ℕ → ℝ := fun n => Nat.casesOn n 0 f

/-- Left shift: `L f n = f (n+1)`. -/
def L (f : ℕ → ℝ) : ℕ → ℝ := fun n => f (n + 1)

@[simp] theorem S_zero (f : ℕ → ℝ) : S f 0 = 0 := rfl
@[simp] theorem S_succ (f : ℕ → ℝ) (n : ℕ) : S f (n + 1) = f n := rfl
@[simp] theorem L_apply (f : ℕ → ℝ) (n : ℕ) : L f n = f (n + 1) := rfl

/-- `L ∘ S = id` (the isometry identity `S* S = 1`). -/
theorem L_comp_S : L ∘ S = id := by
  funext f n
  rfl

theorem S_leftInverse : Function.LeftInverse L S := fun f => congrFun L_comp_S f

/-- A sequence not fixed by `S ∘ L`: the constant `1` (its value at `0` is lost). -/
theorem exists_SL_ne : ∃ f : ℕ → ℝ, S (L f) ≠ f := by
  refine ⟨fun _ => 1, fun h => ?_⟩
  have := congrFun h 0
  simp at this

theorem S_comp_L_ne : S ∘ L ≠ id := by
  intro h
  obtain ⟨f, hf⟩ := exists_SL_ne
  exact hf (congrFun h f)

theorem S_injective : Function.Injective S := S_leftInverse.injective

theorem S_not_surjective : ¬ Function.Surjective S := by
  intro h
  obtain ⟨g, hg⟩ := h (fun _ => 1)
  have := congrFun hg 0
  simp at this

theorem S_no_right_inverse : ¬ ∃ R : (ℕ → ℝ) → (ℕ → ℝ), S ∘ R = id := by
  rintro ⟨R, hR⟩
  exact S_not_surjective fun f => ⟨R f, congrFun hR f⟩

/-- `[L,S] = |0⟩⟨0|`: `L (S f) - S (L f)` keeps only the value at `0`. -/
theorem LS_sub_SL (f : ℕ → ℝ) (n : ℕ) :
    L (S f) n - S (L f) n = if n = 0 then f 0 else 0 := by
  cases n <;> simp

/-- Exact finite-window identity, no hypotheses. -/
theorem sum_S_mul_eq_sum_mul_L (f g : ℕ → ℝ) (M : ℕ) :
    ∑ n ∈ range (M + 1), S f n * g n = ∑ n ∈ range M, f n * L g n := by
  rw [Finset.sum_range_succ']
  simp

/-- Adjointness `⟨S f, g⟩ = ⟨f, L g⟩` for `f` supported in `range N`, on any window `range (M+1)`
with `N ≤ M`. -/
theorem adjoint_finite_support (f g : ℕ → ℝ) (N M : ℕ) (hf : ∀ n, N ≤ n → f n = 0)
    (hM : N ≤ M) :
    ∑ n ∈ range (M + 1), S f n * g n = ∑ n ∈ range (M + 1), f n * L g n := by
  rw [sum_S_mul_eq_sum_mul_L, Finset.sum_range_succ, hf M hM, zero_mul, add_zero]

/-! ## (2) One fermion mode -/

/-- Annihilator `a = !![0,1;0,0]`. -/
def a : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- Creator `a† = aᵀ`. -/
def adag : Matrix (Fin 2) (Fin 2) ℂ := aᵀ

theorem adag_eq : adag = !![0, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a, adag]

theorem conjTranspose_a : aᴴ = adag := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a, adag]

theorem a_mul_a : a * a = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a, Matrix.mul_apply, Fin.sum_univ_two]

theorem adag_mul_adag : adag * adag = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a, adag, Matrix.mul_apply, Fin.sum_univ_two]

theorem anticomm : a * adag + adag * a = 1 := by
  rw [adag_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a]

/-! ## (3) No finite bosons -/

theorem no_finite_CCR_fintype {K ι : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (A B : Matrix ι ι K) : A * B - B * A ≠ 1 := by
  intro h
  have ht := congrArg Matrix.trace h
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, Matrix.trace_one] at ht
  have : (Fintype.card ι : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact this ht.symm

theorem no_finite_CCR {K : Type*} [Field K] [CharZero K] (n : ℕ) (hn : 1 ≤ n)
    (A B : Matrix (Fin n) (Fin n) K) : A * B - B * A ≠ 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact no_finite_CCR_fintype A B

theorem no_finite_CCR_complex (n : ℕ) (hn : 1 ≤ n) (A B : Matrix (Fin n) (Fin n) ℂ) :
    A * B - B * A ≠ 1 :=
  no_finite_CCR n hn A B

/-! ## (4) Majorana -/

/-- Majorana operator `γ = a + a†`. -/
def gamma : Matrix (Fin 2) (Fin 2) ℂ := a + adag

theorem gamma_hermitian : gammaᴴ = gamma := by
  rw [gamma, adag_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a]

theorem gamma_sq : gamma * gamma = 1 := by
  rw [gamma, adag_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## (5) Going down: finite dimension forbids a one-sided isometry (addition)

`S` has a left inverse but no right inverse. For square matrices over a commutative ring this
cannot happen: a left inverse is automatically a right inverse (Dedekind-finiteness of
`Matrix ι ι R`, via the determinant). So the phenomenon in (1) needs infinitely many levels,
just as the CCR in (3) does. -/

/-- In finite dimension, `L * S = 1` forces `S * L = 1`: no finite one-sided isometry. -/
theorem no_finite_one_sided {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (Lm Sm : Matrix ι ι R) (h : Lm * Sm = 1) : Sm * Lm = 1 := by
  exact mul_eq_one_comm.mp h

/-! ## Concrete examples (non-vacuity checks) -/

/-- The hypotheses of `adjoint_finite_support` hold for a nonzero `f = δ₀` (with `N = 1`, `M = 1`). -/
example :
    ∑ n ∈ range 2, S (fun n => if n = 0 then (1 : ℝ) else 0) n * (fun n : ℕ => (n : ℝ)) n =
      ∑ n ∈ range 2, (fun n => if n = 0 then (1 : ℝ) else 0) n * L (fun n : ℕ => (n : ℝ)) n :=
  adjoint_finite_support _ _ 1 1 (fun n hn => by simp; omega) le_rfl

/-- Both sides of the instance above equal `1` (so the identity is not `0 = 0`). -/
example :
    ∑ n ∈ range 2, S (fun n => if n = 0 then (1 : ℝ) else 0) n * (fun n : ℕ => (n : ℝ)) n = 1 := by
  simp [Finset.sum_range_succ]

/-- `S` applied to `δ₀` is `δ₁`, and `L` undoes it. -/
example : S (fun n => if n = 0 then (1 : ℝ) else 0) 1 = 1 ∧
    L (S (fun n => if n = 0 then (1 : ℝ) else 0)) 0 = 1 := by
  simp

/-- The 2-level truncation of the creator, `a† = !![0,0;1,0]`, is not an isometry:
`a * a† = diag(1,0) ≠ 1`, consistent with `no_finite_one_sided` (`a * a† = 1` would force
`a† * a = 1`, and then `anticomm` would read `1 + 1 = 1`). -/
example : a * adag ≠ 1 := by
  intro h
  have := congrFun (congrFun h 1) 1
  rw [adag_eq] at this
  simp [a, Matrix.mul_apply, Fin.sum_univ_two] at this

/-- `no_finite_one_sided` is not vacuous: an invertible non-identity pair on `Fin 2`. -/
example : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; 1, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end Atlas2.B02
