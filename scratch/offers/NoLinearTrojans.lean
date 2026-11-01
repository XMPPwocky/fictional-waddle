import Mathlib

/-!
# No linear trojans

Linear system `x_{t+1} = A x_t + B u_t`, `y_t = C x_t` on the state space
`(V ⊕ H) → ℝ`. The visible-to-hidden coupling block is `A_vh i j = A (inl i) (inr j)`
and the hidden output block is `C_h y j = C y (inr j)`.

PROVED
* `traj_eq`: the trajectory splits as `x_t = A^t x_0 + x_t(0)`, where `x_t(0)` is the
  trajectory started from the zero state with the same inputs.
* `visible_eq`: if `A_vh = 0` and the initial states agree on `V`, the states agree on `V`
  at every time.
* `no_trojan` (claim 1): if `A_vh = 0` and `C_h = 0`, then for every input sequence and
  every pair of initial states with the same visible part, `y_t = y'_t` for all `t`.
* `no_trojan_fromBlocks`: the same statement with `A = fromBlocks A_vv 0 A_hv A_hh` and
  `C = fromCols C_v 0`.
* `insensitive_iff_krylov` (claim 2, the equivalence): for arbitrary `A, B, C`, the output
  is insensitive to the hidden part of the initial state (for all inputs and all times)
  if and only if `C A^k e_h = 0` for every `k` and every hidden basis vector `e_h`.
* `krylov_of_blocks` (claim 2 under the hypotheses): if `A_vh = 0` and `C_h = 0` then
  `C A^k e_h = 0` for all `k` and `h`.
* `needs_Avh_zero` (claim 3a): with one-dimensional blocks, `A = [[0,1],[0,0]]`,
  `C = [1,0]`, `B = 0`: `C_h = 0`, `A_vh ≠ 0`, the initial states `e_h` and `0` have the
  same visible part, and `y_1 = 1 ≠ 0 = y'_1`.
* `needs_Ch_zero` (claim 3b): with one-dimensional blocks, `A = 0`, `C = [0,1]`, `B = 0`:
  `A_vh = 0`, `C_h ≠ 0`, the initial states `e_h` and `0` have the same visible part, and
  `y_0 = 1 ≠ 0 = y'_0`.
-/

namespace NoLinearTrojans

open Matrix

variable {V H U Y : Type*} [Fintype V] [Fintype H] [Fintype U] [Fintype Y]
  [DecidableEq V] [DecidableEq H]

/-- State trajectory of `x_{t+1} = A x_t + B u_t` from `x0`. -/
def traj (A : Matrix (V ⊕ H) (V ⊕ H) ℝ) (B : Matrix (V ⊕ H) U ℝ) (u : ℕ → U → ℝ)
    (x0 : V ⊕ H → ℝ) : ℕ → (V ⊕ H → ℝ)
  | 0 => x0
  | t + 1 => A *ᵥ traj A B u x0 t + B *ᵥ u t

/-- Output `y_t = C x_t`. -/
def out (A : Matrix (V ⊕ H) (V ⊕ H) ℝ) (B : Matrix (V ⊕ H) U ℝ)
    (C : Matrix Y (V ⊕ H) ℝ) (u : ℕ → U → ℝ) (x0 : V ⊕ H → ℝ) (t : ℕ) : Y → ℝ :=
  C *ᵥ traj A B u x0 t

/-- Hidden basis vector `e_h`. -/
def eH (h : H) : V ⊕ H → ℝ := Pi.single (Sum.inr h) 1

theorem traj_eq (A : Matrix (V ⊕ H) (V ⊕ H) ℝ) (B : Matrix (V ⊕ H) U ℝ)
    (u : ℕ → U → ℝ) (x0 : V ⊕ H → ℝ) (t : ℕ) :
    traj A B u x0 t = (A ^ t) *ᵥ x0 + traj A B u 0 t := by
  induction t with
  | zero => simp [traj]
  | succ t ih =>
    simp only [traj, ih, mulVec_add, mulVec_mulVec, pow_succ']
    abel

omit [DecidableEq V] [DecidableEq H] in
/-- A vector vanishing on `V` is killed by any matrix whose `inr` columns vanish. -/
theorem mulVec_eq_zero_of_hidden {Z : Type*} (M : Matrix Z (V ⊕ H) ℝ)
    (hM : ∀ z h, M z (Sum.inr h) = 0) (d : V ⊕ H → ℝ) (hd : ∀ v, d (Sum.inl v) = 0) :
    M *ᵥ d = 0 := by
  funext z
  simp [mulVec, dotProduct, Fintype.sum_sum_type, hM, hd]

omit [DecidableEq V] [DecidableEq H] in
theorem visible_eq (A : Matrix (V ⊕ H) (V ⊕ H) ℝ) (B : Matrix (V ⊕ H) U ℝ)
    (hA : ∀ v h, A (Sum.inl v) (Sum.inr h) = 0) (u : ℕ → U → ℝ) (x0 x0' : V ⊕ H → ℝ)
    (hx : ∀ v, x0 (Sum.inl v) = x0' (Sum.inl v)) (t : ℕ) (v : V) :
    traj A B u x0 t (Sum.inl v) = traj A B u x0' t (Sum.inl v) := by
  induction t generalizing v with
  | zero => exact hx v
  | succ t ih =>
    simp only [traj, Pi.add_apply, mulVec, dotProduct, Fintype.sum_sum_type, hA, zero_mul,
      Finset.sum_const_zero, add_zero, ih]

omit [Fintype Y] [DecidableEq V] [DecidableEq H] in
/-- Claim (1). -/
theorem no_trojan (A : Matrix (V ⊕ H) (V ⊕ H) ℝ) (B : Matrix (V ⊕ H) U ℝ)
    (C : Matrix Y (V ⊕ H) ℝ)
    (hA : ∀ v h, A (Sum.inl v) (Sum.inr h) = 0) (hC : ∀ y h, C y (Sum.inr h) = 0)
    (u : ℕ → U → ℝ) (x0 x0' : V ⊕ H → ℝ) (hx : ∀ v, x0 (Sum.inl v) = x0' (Sum.inl v))
    (t : ℕ) : out A B C u x0 t = out A B C u x0' t := by
  have hd := mulVec_eq_zero_of_hidden C hC (traj A B u x0 t - traj A B u x0' t)
    (fun v => by simp [visible_eq A B hA u x0 x0' hx t v])
  rw [mulVec_sub, sub_eq_zero] at hd
  exact hd

omit [Fintype Y] [DecidableEq V] [DecidableEq H] in
/-- Claim (1) in literal block form. -/
theorem no_trojan_fromBlocks (Avv : Matrix V V ℝ) (Ahv : Matrix H V ℝ) (Ahh : Matrix H H ℝ)
    (Cv : Matrix Y V ℝ) (B : Matrix (V ⊕ H) U ℝ)
    (u : ℕ → U → ℝ) (x0 x0' : V ⊕ H → ℝ) (hx : ∀ v, x0 (Sum.inl v) = x0' (Sum.inl v))
    (t : ℕ) :
    out (fromBlocks Avv 0 Ahv Ahh) B (fromCols Cv (0 : Matrix Y H ℝ)) u x0 t =
      out (fromBlocks Avv 0 Ahv Ahh) B (fromCols Cv (0 : Matrix Y H ℝ)) u x0' t :=
  no_trojan _ _ _ (fun _ _ => by simp) (fun _ _ => by simp) u x0 x0' hx t

omit [Fintype Y] in
/-- Claim (2): insensitivity to the hidden initial state is equivalent to the
Krylov condition `C A^k e_h = 0`, for arbitrary `A, B, C`. -/
theorem insensitive_iff_krylov (A : Matrix (V ⊕ H) (V ⊕ H) ℝ) (B : Matrix (V ⊕ H) U ℝ)
    (C : Matrix Y (V ⊕ H) ℝ) :
    (∀ (u : ℕ → U → ℝ) (x0 x0' : V ⊕ H → ℝ), (∀ v, x0 (Sum.inl v) = x0' (Sum.inl v)) →
        ∀ t, out A B C u x0 t = out A B C u x0' t) ↔
      ∀ (k : ℕ) (h : H), C *ᵥ ((A ^ k) *ᵥ eH h) = 0 := by
  constructor
  · intro hins k h
    have := hins 0 (eH h) 0 (fun v => by simp [eH]) k
    simp only [out] at this
    rw [traj_eq A B 0 (eH h) k, mulVec_add] at this
    exact add_eq_right.mp this
  · intro hk u x0 x0' hx t
    have hcol : ∀ h, (C * A ^ t) *ᵥ eH h = 0 := fun h => by
      rw [← mulVec_mulVec]; exact hk t h
    have hM : ∀ y h, (C * A ^ t) y (Sum.inr h) = 0 := fun y h => by
      have := congrFun (hcol h) y
      simpa [eH, mulVec_single_one] using this
    have hd := mulVec_eq_zero_of_hidden (C * A ^ t) hM (x0 - x0')
      (fun v => by simp [hx v])
    simp only [out]
    rw [traj_eq A B u x0 t, traj_eq A B u x0' t, mulVec_add, mulVec_add, mulVec_mulVec,
      mulVec_mulVec]
    rw [mulVec_sub, sub_eq_zero] at hd
    rw [hd]

omit [Fintype Y] in
/-- Claim (2) under the block hypotheses. -/
theorem krylov_of_blocks (A : Matrix (V ⊕ H) (V ⊕ H) ℝ) (C : Matrix Y (V ⊕ H) ℝ)
    (hA : ∀ v h, A (Sum.inl v) (Sum.inr h) = 0) (hC : ∀ y h, C y (Sum.inr h) = 0)
    (k : ℕ) (h : H) : C *ᵥ ((A ^ k) *ᵥ eH h) = 0 :=
  (insensitive_iff_krylov A (0 : Matrix (V ⊕ H) Unit ℝ) C).1
    (fun u x0 x0' hx t => no_trojan A 0 C hA hC u x0 x0' hx t) k h

/-- Claim (3a): dropping `A_vh = 0` (keeping `C_h = 0`) fails at `t = 1`. -/
theorem needs_Avh_zero :
    let A : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ := fromBlocks 0 1 0 0
    let B : Matrix (Unit ⊕ Unit) Unit ℝ := 0
    let C : Matrix Unit (Unit ⊕ Unit) ℝ := fromCols 1 0
    let x0 : Unit ⊕ Unit → ℝ := eH ()
    let x0' : Unit ⊕ Unit → ℝ := 0
    (∀ y h, C y (Sum.inr h) = 0) ∧ A (Sum.inl ()) (Sum.inr ()) ≠ 0 ∧
      (∀ v, x0 (Sum.inl v) = x0' (Sum.inl v)) ∧
      out A B C (fun _ => 0) x0 1 () = 1 ∧ out A B C (fun _ => 0) x0' 1 () = 0 := by
  intro A B C x0 x0'
  refine ⟨fun _ _ => by simp [C], by simp [A], fun _ => by simp [x0, x0', eH], ?_, ?_⟩ <;>
    simp [out, traj, A, B, C, x0, x0', eH, mulVec, dotProduct, Fintype.sum_sum_type]

/-- Claim (3b): dropping `C_h = 0` (keeping `A_vh = 0`) fails at `t = 0`. -/
theorem needs_Ch_zero :
    let A : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ := 0
    let B : Matrix (Unit ⊕ Unit) Unit ℝ := 0
    let C : Matrix Unit (Unit ⊕ Unit) ℝ := fromCols 0 1
    let x0 : Unit ⊕ Unit → ℝ := eH ()
    let x0' : Unit ⊕ Unit → ℝ := 0
    (∀ v h, A (Sum.inl v) (Sum.inr h) = 0) ∧ C () (Sum.inr ()) ≠ 0 ∧
      (∀ v, x0 (Sum.inl v) = x0' (Sum.inl v)) ∧
      out A B C (fun _ => 0) x0 0 () = 1 ∧ out A B C (fun _ => 0) x0' 0 () = 0 := by
  intro A B C x0 x0'
  refine ⟨fun _ _ => by simp [A], by simp [C], fun _ => by simp [x0, x0', eH], ?_, ?_⟩ <;>
    simp [out, traj, C, x0, x0', eH, mulVec, dotProduct, Fintype.sum_sum_type]

end NoLinearTrojans
