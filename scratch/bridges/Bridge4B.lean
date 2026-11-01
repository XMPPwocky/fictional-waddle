import Mathlib

/-!
# Octonion yomi: seven period-4 readers, a group of order 128, Hamming-code orbits

Setting. `Oct` is the Cayley–Dickson double of Mathlib's integer quaternions `ℍ[ℤ]`, with
`(a, b) * (c, d) = (a * c - star d * b, d * a + b * star c)` and basis units `e 0, …, e 7`,
copied verbatim from `scratch/society/OctonionMoufangLoopA.lean` (that file is not an importable
module). A state is `s : Fin 8 → Bool`; `enc' b = if b then 1 else -1` (the convention of
`RootsOfUnityGamesB.enc`), and `encO s` is the octonion with coordinates `enc' (s m)` in the
basis `e m`. `flipAll` negates every bit, `flipHigh` negates the bits `4, …, 7`. Coordinates are
indexed by `Fin 8` with `m ⊕ n` the bitwise xor (`^^^`). `read n s` is defined as the bitwise
decoding of the octonion `e n * encO s` (sign of each coordinate). `step (x, y) = (y, !x)` is the
yomi step of `RootsOfUnityGamesB`. `G` is `Subgroup.closure {read 1, …, read 7}` in
`Equiv.Perm (Fin 8 → Bool)`, acting on states by application.

PROVED
* (0) `read_spec`: `encO (read n s) = e n * encO s` for all `n s` (all `n`, including `n = 0`,
  where `read_zero : read 0 = 1`); `read_unique`: `read n` is the unique map
  `f` with `∀ s, encO (f s) = e n * encO s`. `encO_flipAll`, `encO_flipHigh`: `flipAll` is
  negation of the octonion, `flipHigh` negates its second quaternion.
* (a) `read_pair`: for `n ≠ 0` and every `m`, `read n` maps the pair `(s m, s (m ⊕ n))` to
  `step (s m, s (m ⊕ n))` for all `s`, or to `step^[3] (s m, s (m ⊕ n))` for all `s`.
  `read_sq`: `read n ^ 2 = flipAll`; `orderOf_read`: `orderOf (read n) = 4` (`n ≠ 0`).
* (b) `read_anticomm`: `read n * read n' = flipAll * read n' * read n` for `n, n' ≠ 0`, `n ≠ n'`.
* (c) `read_12`: `read 1 * read 2 = read 3 * flipHigh`.
* `read_prod`: `read 1 * read 2 * read 3 * read 4 * read 5 * read 6 * read 7 = flipAll`.
* (d) `card_G`: `Nat.card G = 128`; `exponent_G`: `Monoid.exponent G = 4`;
  `card_order_two`: 71 elements of order 2; `card_order_four`: 56 elements of order 4;
  `mem_center_G`: `g ∈ center G ↔ g = 1 ∨ g = flipAll`;
  `mem_commutator_G`: `g ∈ commutator G ↔ g = 1 ∨ g = flipAll`.
* (e) `card_Ev`: there are 128 even states; `orbit_even`: the orbit of every even state is the
  set of all even states; `stabilizer_even`: its stabilizer is trivial; `even_regular`: for even
  `s t` there is exactly one `g ∈ G` with `g • s = t`.
  `mem_orbit_odd`: for odd `s`, `t ∈ orbit G s ↔ s ⊕ t ∈ RM(1,3)`;
  `card_orbit_odd`: odd orbits have 16 elements; `card_stabilizer_odd`: odd stabilizers have
  order 8; `odd_orbits`: the orbits of odd states are exactly the 8 pairwise distinct orbits of
  the single-defect states `oneDef m`, so there are 8 of them;
  `unique_defect`: each odd orbit contains exactly one state with exactly one `false` coordinate.
* `orbit_even_not_RM`: for even `s` the criterion `s ⊕ t ∈ RM(1,3)` does not describe the orbit
  (some `t` in the orbit has `s ⊕ t ∉ RM(1,3)`); the RM criterion of (e) holds for odd `s` only.

INTERPRETED
* `encO`, `enc'`, `flipAll`, `flipHigh` were not supplied as code; they are defined here as
  described above. Bit `true` encodes `+1`, `false` encodes `-1`.
* "Parity" of a state is the parity of its number of `true` coordinates (`par`); since there are
  8 coordinates this equals the parity of the number of `false` coordinates.
* `RM(1,3)` is `RM13`, the set of evaluation vectors `m ↦ b ⊕ w₀ m₀ ⊕ w₁ m₁ ⊕ w₂ m₂` of affine
  functions of the binary digits `mᵢ = m.testBit i`.
* "Single-defect state" is a state with exactly one coordinate equal to `false` (one `-1` in the
  octonion encoding), counted by `nDefects`.
* "Center and commutator subgroup are `{1, flipAll}`" is stated as membership equivalences for
  elements of `G`. The group computations run on an explicit faithful model `SC` (signed
  translations `s ↦ (m ↦ s (m ⊕ a) ⊕ c m)`), with `T : SC →* Perm` injective and
  `T (rcode n) = read n`; the sign table `sgnT` is checked against the octonion product
  (`rcode_fl`). Finite facts are checked by `decide +kernel`.
-/

namespace Bridge4B

open Quaternion
open scoped commutatorElement

instance : DecidableEq ℍ[ℤ] := fun a b =>
  decidable_of_iff (a.re = b.re ∧ a.imI = b.imI ∧ a.imJ = b.imJ ∧ a.imK = b.imK)
    (by
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact QuaternionAlgebra.ext h1 h2 h3 h4
      · rintro rfl
        exact ⟨rfl, rfl, rfl, rfl⟩)

@[ext]
structure Oct where
  fst : ℍ[ℤ]
  snd : ℍ[ℤ]
  deriving DecidableEq

instance : Mul Oct where
  mul x y := ⟨x.fst * y.fst - star y.snd * x.snd, y.snd * x.fst + x.snd * star y.fst⟩

instance : Neg Oct := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩

def qbasis : Fin 4 → ℍ[ℤ] :=
  ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

def e (n : Fin 8) : Oct :=
  if h : n.val < 4 then ⟨qbasis ⟨n.val, h⟩, 0⟩ else ⟨0, qbasis ⟨n.val - 4, by omega⟩⟩

abbrev State := Fin 8 → Bool

def enc' (b : Bool) : ℤ := if b then 1 else -1

def encO (s : State) : Oct :=
  ⟨⟨enc' (s 0), enc' (s 1), enc' (s 2), enc' (s 3)⟩,
   ⟨enc' (s 4), enc' (s 5), enc' (s 6), enc' (s 7)⟩⟩

def coord (x : Oct) : Fin 8 → ℤ :=
  ![x.fst.re, x.fst.imI, x.fst.imJ, x.fst.imK, x.snd.re, x.snd.imI, x.snd.imJ, x.snd.imK]

theorem forall_state (P : State → Prop) :
    (∀ s, P s) ↔ ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, P ![b0, b1, b2, b3, b4, b5, b6, b7] := by
  refine ⟨fun h _ _ _ _ _ _ _ _ => h _, fun h s => ?_⟩
  have := h (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) (s 6) (s 7)
  convert this using 1
  funext m; fin_cases m <;> rfl

structure SC where
  tr : Fin 8
  fl : Fin 8 → Bool

instance : DecidableEq SC := fun g h =>
  decidable_of_iff (g.tr = h.tr ∧ g.fl = h.fl)
    (by
      constructor
      · rintro ⟨h1, h2⟩
        cases g; cases h; simp_all
      · rintro rfl
        exact ⟨rfl, rfl⟩)

def rcode (n : Fin 8) : SC := ⟨n, fun p => decide (coord (e n * e (p ^^^ n)) p < 0)⟩

def actC (g : SC) (s : State) : State := fun m => xor (s (m ^^^ g.tr)) (g.fl m)


/-! ## Xor on `Fin 8` -/

theorem x8_assoc : ∀ a b c : Fin 8, a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := by decide
@[simp] theorem x8_zero : ∀ a : Fin 8, a ^^^ 0 = a := by decide
@[simp] theorem zero_x8 : ∀ a : Fin 8, 0 ^^^ a = a := by decide
@[simp] theorem x8_self : ∀ a : Fin 8, a ^^^ a = 0 := by decide
@[simp] theorem x8_cancel : ∀ a b : Fin 8, a ^^^ b ^^^ b = a := by decide
theorem x8_eq_zero : ∀ a b : Fin 8, a ^^^ b = 0 ↔ a = b := by decide

/-! ## The group of signed translations of the eight coordinates -/

theorem SC.ext' {g h : SC} (h1 : g.tr = h.tr) (h2 : g.fl = h.fl) : g = h := by
  cases g; cases h; simp_all

instance : Mul SC := ⟨fun g h => ⟨g.tr ^^^ h.tr, fun m => xor (g.fl m) (h.fl (m ^^^ g.tr))⟩⟩
instance : One SC := ⟨⟨0, fun _ => false⟩⟩
instance : Inv SC := ⟨fun g => ⟨g.tr, fun m => g.fl (m ^^^ g.tr)⟩⟩

@[simp] theorem mul_tr (g h : SC) : (g * h).tr = g.tr ^^^ h.tr := rfl
@[simp] theorem mul_fl (g h : SC) (m : Fin 8) : (g * h).fl m = xor (g.fl m) (h.fl (m ^^^ g.tr)) :=
  rfl
@[simp] theorem one_tr : (1 : SC).tr = 0 := rfl
@[simp] theorem one_fl (m : Fin 8) : (1 : SC).fl m = false := rfl
@[simp] theorem inv_tr (g : SC) : g⁻¹.tr = g.tr := rfl
@[simp] theorem inv_fl (g : SC) (m : Fin 8) : g⁻¹.fl m = g.fl (m ^^^ g.tr) := rfl

instance : Group SC :=
  Group.ofLeftAxioms
    (fun a b c => SC.ext' (by simp [x8_assoc]) (by funext m; simp [x8_assoc]))
    (fun a => SC.ext' (by simp) (by funext m; simp))
    (fun a => SC.ext' (by simp) (by funext m; simp))

/-- `g` acts on states by `(g s) m = s (m ⊕ g.tr) ⊕ g.fl m`. -/
instance : MulAction SC State where
  smul := actC
  one_smul s := by funext m; simp [actC, HSMul.hSMul]
  mul_smul g h s := by
    funext m
    show xor (s (m ^^^ (g.tr ^^^ h.tr))) (xor (g.fl m) (h.fl (m ^^^ g.tr))) =
      xor (xor (s (m ^^^ g.tr ^^^ h.tr)) (h.fl (m ^^^ g.tr))) (g.fl m)
    rw [x8_assoc]
    cases s (m ^^^ (g.tr ^^^ h.tr)) <;> cases g.fl m <;> cases h.fl (m ^^^ g.tr) <;> rfl

/-- The permutation representation of the signed translations. -/
def T : SC →* Equiv.Perm State := MulAction.toPermHom SC State

theorem T_apply (g : SC) (s : State) : T g s = actC g s := rfl

theorem T_injective : Function.Injective T := by
  intro g h hgh
  have hfl : g.fl = h.fl := by
    funext m
    have := congrFun (Equiv.congr_fun hgh (fun _ => false)) m
    simpa [T_apply, actC] using this
  have h2 : ∀ m, decide (m ^^^ g.tr = 0) = decide (m ^^^ h.tr = 0) := by
    intro m
    have := congrFun (Equiv.congr_fun hgh (fun k => decide (k = 0))) m
    simp only [T_apply, actC, hfl] at this
    revert this
    cases h.fl m <;> simp
  have h3 := h2 g.tr
  have htr : g.tr = h.tr := by
    revert h3
    generalize g.tr = a
    generalize h.tr = b
    revert a b
    decide
  exact SC.ext' htr hfl

/-! ## The readers -/

def dec (x : Oct) : State := fun m => decide (0 < coord x m)

theorem dec_encO : ∀ s : State, dec (encO s) = s := by
  rw [forall_state]
  decide +kernel

theorem encO_injective : Function.Injective encO := fun s t h => by
  rw [← dec_encO s, h, dec_encO]

theorem encO_act : ∀ n : Fin 8, ∀ s : State, encO (actC (rcode n) s) = e n * encO s := by
  intro n
  rw [forall_state]
  revert n
  decide +kernel

theorem dec_mul (n : Fin 8) (s : State) : dec (e n * encO s) = actC (rcode n) s := by
  rw [← encO_act, dec_encO]

/-- `read n s` decodes the octonion `e n * encO s`. -/
def read (n : Fin 8) : Equiv.Perm State where
  toFun s := dec (e n * encO s)
  invFun s := actC (rcode n)⁻¹ s
  left_inv s := by
    simp only [dec_mul]
    exact inv_smul_smul (rcode n) s
  right_inv s := by
    simp only [dec_mul]
    exact smul_inv_smul (rcode n) s

theorem read_apply (n : Fin 8) (s : State) : read n s = actC (rcode n) s := dec_mul n s

theorem T_rcode (n : Fin 8) : T (rcode n) = read n :=
  Equiv.ext fun s => (read_apply n s).symm

/-- (0) `read n` realises left multiplication by `e n`. -/
theorem read_spec (n : Fin 8) (s : State) : encO (read n s) = e n * encO s := by
  rw [read_apply]; exact encO_act n s

/-- (0) Uniqueness: `read n` is the only map with this property. -/
theorem read_unique (n : Fin 8) : ∃! f : State → State, ∀ s, encO (f s) = e n * encO s :=
  ⟨read n, read_spec n, fun _ hf => funext fun s =>
    encO_injective ((hf s).trans (read_spec n s).symm)⟩

/-! ## `flipAll`, `flipHigh` -/

def flipAll : Equiv.Perm State where
  toFun s m := !s m
  invFun s m := !s m
  left_inv s := by funext m; simp
  right_inv s := by funext m; simp

def flipHigh : Equiv.Perm State where
  toFun s m := xor (s m) (decide (4 ≤ m.val))
  invFun s m := xor (s m) (decide (4 ≤ m.val))
  left_inv s := by funext m; simp
  right_inv s := by funext m; simp

def Fc : SC := ⟨0, fun _ => true⟩
def Hh : SC := ⟨0, fun m => decide (4 ≤ m.val)⟩

theorem encO_flipAll : ∀ s : State, encO (flipAll s) = -encO s := by
  rw [forall_state]; decide +kernel

theorem encO_flipHigh : ∀ s : State,
    encO (flipHigh s) = ⟨(encO s).fst, -(encO s).snd⟩ := by
  rw [forall_state]; decide +kernel

theorem T_Fc : T Fc = flipAll := by
  ext s m; simp [T_apply, actC, Fc, flipAll]

theorem T_Hh : T Hh = flipHigh := by
  ext s m; simp [T_apply, actC, Hh, flipHigh]

theorem rcode_zero : rcode 0 = 1 := by decide +kernel
theorem Fc_ne_one : Fc ≠ 1 := by decide

theorem read_zero : read 0 = 1 := by rw [← T_rcode, rcode_zero, map_one]
theorem Fc_sq : Fc ^ 2 = 1 := by decide +kernel
theorem rcode_sq : ∀ n : Fin 8, n ≠ 0 → rcode n * rcode n = Fc := by decide +kernel
theorem rcode_anti : ∀ n n' : Fin 8, n ≠ 0 → n' ≠ 0 → n ≠ n' →
    rcode n * rcode n' = Fc * rcode n' * rcode n := by decide +kernel
theorem rcode_12 : rcode 1 * rcode 2 = rcode 3 * Hh := by decide +kernel
theorem rcode_prod :
    rcode 1 * rcode 2 * rcode 3 * rcode 4 * rcode 5 * rcode 6 * rcode 7 = Fc := by decide +kernel

theorem flipAll_ne_one : flipAll ≠ 1 := fun h =>
  Fc_ne_one (T_injective (by rw [T_Fc, map_one]; exact h))

theorem flipAll_sq : flipAll ^ 2 = 1 := by rw [← T_Fc, ← map_pow, Fc_sq, map_one]

/-- (a) `(read n)^2 = flipAll`. -/
theorem read_sq (n : Fin 8) (hn : n ≠ 0) : read n ^ 2 = flipAll := by
  rw [← T_rcode, ← map_pow, pow_two, rcode_sq n hn, T_Fc]

/-- (a) `read n` has order exactly 4. -/
theorem orderOf_read (n : Fin 8) (hn : n ≠ 0) : orderOf (read n) = 4 := by
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := read n)
    (by rw [pow_one, read_sq n hn]; exact flipAll_ne_one)
    (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, read_sq n hn, flipAll_sq])
  simpa using this

/-- One yomi step on a Bool pair (as in `RootsOfUnityGamesB.step`). -/
def step (p : Bool × Bool) : Bool × Bool := (p.2, !p.1)

@[simp] theorem rcode_tr (n : Fin 8) : (rcode n).tr = n := rfl

theorem pair_flip : ∀ n m : Fin 8, n ≠ 0 →
    ((rcode n).fl m = false ∧ (rcode n).fl (m ^^^ n) = true) ∨
    ((rcode n).fl m = true ∧ (rcode n).fl (m ^^^ n) = false) := by decide +kernel

/-- (a) On each pair of coordinates `(m, m ⊕ n)`, `read n` acts as `step` or as `step^[3]`. -/
theorem read_pair (n : Fin 8) (hn : n ≠ 0) (m : Fin 8) :
    (∀ s, (read n s m, read n s (m ^^^ n)) = step (s m, s (m ^^^ n))) ∨
    (∀ s, (read n s m, read n s (m ^^^ n)) = step^[3] (s m, s (m ^^^ n))) := by
  rcases pair_flip n m hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; intro s
    simp [read_apply, actC, h1, h2, step]
  · right; intro s
    simp [read_apply, actC, h1, h2, step, Function.iterate_succ_apply']

/-- (b) Distinct readers anticommute up to `flipAll`. -/
theorem read_anticomm (n n' : Fin 8) (hn : n ≠ 0) (hn' : n' ≠ 0) (hne : n ≠ n') :
    read n * read n' = flipAll * read n' * read n := by
  have := congrArg T (rcode_anti n n' hn hn' hne)
  simpa [map_mul, T_rcode, T_Fc] using this

/-- (c) `read 1 ∘ read 2 = read 3 ∘ flipHigh`. -/
theorem read_12 : read 1 * read 2 = read 3 * flipHigh := by
  have := congrArg T rcode_12
  simpa [map_mul, T_rcode, T_Hh] using this

/-- The ordered product of the seven readers is `flipAll`. -/
theorem read_prod :
    read 1 * read 2 * read 3 * read 4 * read 5 * read 6 * read 7 = flipAll := by
  have := congrArg T rcode_prod
  simpa [map_mul, T_rcode, T_Fc] using this


/-! ## RM(1,3) -/

abbrev Par4 := Bool × Bool × Bool × Bool

/-- The affine Boolean function `b ⊕ w₀ x₀ ⊕ w₁ x₁ ⊕ w₂ x₂` of the binary digits of `m`. -/
def affine (p : Par4) (m : Fin 8) : Bool :=
  xor (xor (xor p.1 (p.2.1 && m.val.testBit 0)) (p.2.2.1 && m.val.testBit 1))
    (p.2.2.2 && m.val.testBit 2)

/-- The Reed–Muller code `RM(1,3)`: evaluation vectors of affine functions on `𝔽₂³`. -/
def RM13 : Set State := Set.range affine

def rmPar (c : State) : Par4 := (c 0, xor (c 1) (c 0), xor (c 2) (c 0), xor (c 4) (c 0))

theorem rmPar_affine : ∀ p, rmPar (affine p) = p := by decide

theorem mem_RM13_iff (c : State) : c ∈ RM13 ↔ affine (rmPar c) = c :=
  ⟨by rintro ⟨p, rfl⟩; rw [rmPar_affine], fun h => ⟨_, h⟩⟩

instance (c : State) : Decidable (c ∈ RM13) := decidable_of_iff _ (mem_RM13_iff c).symm

theorem affine_injective : Function.Injective affine := fun p q h => by
  rw [← rmPar_affine p, h, rmPar_affine]

theorem card_RM13 : Nat.card RM13 = 16 := by
  rw [RM13, Nat.card_coe_set_eq, Set.ncard_range_of_injective affine_injective]
  simp [Nat.card_eq_fintype_card]

theorem RM_xor {c d : State} (hc : c ∈ RM13) (hd : d ∈ RM13) :
    (fun m => xor (c m) (d m)) ∈ RM13 := by
  obtain ⟨p, rfl⟩ := hc
  obtain ⟨q, rfl⟩ := hd
  have : ∀ p q : Par4, (fun m => xor (affine p m) (affine q m)) ∈ RM13 := by decide +kernel
  exact this p q

theorem RM_tr {c : State} (hc : c ∈ RM13) (a : Fin 8) : (fun m => c (m ^^^ a)) ∈ RM13 := by
  obtain ⟨p, rfl⟩ := hc
  have : ∀ (p : Par4) (a : Fin 8), (fun m => affine p (m ^^^ a)) ∈ RM13 := by decide +kernel
  exact this p a

/-! ## The sign table, checked against the octonion product -/

def sgnT : Fin 8 → Fin 8 → Bool :=
  ![![false, false, false, false, false, false, false, false],
    ![true, false, true, false, true, false, false, true],
    ![true, false, false, true, true, true, false, false],
    ![true, true, false, false, true, false, true, false],
    ![true, false, false, false, false, true, true, true],
    ![true, true, false, true, false, false, false, true],
    ![true, true, true, false, false, true, false, false],
    ![true, false, true, true, false, false, true, false]]

theorem rcode_fl : ∀ n m : Fin 8, (rcode n).fl m = sgnT n m := by decide +kernel

theorem rcode_eqT (n : Fin 8) : rcode n = ⟨n, sgnT n⟩ :=
  SC.ext' rfl (funext (rcode_fl n))

/-! ## The explicit group `Gs` -/

def Gs : Subgroup SC where
  carrier := {x | (fun m => xor (x.fl m) (sgnT x.tr m)) ∈ RM13}
  one_mem' := by
    show (fun m => xor false (sgnT 0 m)) ∈ RM13
    decide
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    have hc : ∀ a b : Fin 8,
        (fun m => xor (xor (sgnT a m) (sgnT b (m ^^^ a))) (sgnT (a ^^^ b) m)) ∈ RM13 := by
      decide +kernel
    have := RM_xor (RM_xor hx (RM_tr hy x.tr)) (hc x.tr y.tr)
    have key : ∀ A B C D E : Bool,
        xor (xor A B) E = xor (xor (xor A C) (xor B D)) (xor (xor C D) E) := by decide
    convert this using 1
    funext m
    exact key _ _ _ _ _
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have hi : ∀ a : Fin 8, (fun m => xor (sgnT a (m ^^^ a)) (sgnT a m)) ∈ RM13 := by
      decide +kernel
    have := RM_xor (RM_tr hx x.tr) (hi x.tr)
    have key : ∀ A C E : Bool, xor A E = xor (xor A C) (xor C E) := by decide
    convert this using 1
    funext m
    exact key _ _ _

theorem mem_Gs_iff (x : SC) : x ∈ Gs ↔ (fun m => xor (x.fl m) (sgnT x.tr m)) ∈ RM13 := Iff.rfl

def phiT (q : Fin 8 × Par4) : SC := ⟨q.1, fun m => xor (affine q.2 m) (sgnT q.1 m)⟩

theorem phiT_mem (q : Fin 8 × Par4) : phiT q ∈ Gs := by
  rw [mem_Gs_iff]
  have : (fun m => xor ((phiT q).fl m) (sgnT (phiT q).tr m)) = affine q.2 :=
    funext fun m => by simp [phiT]
  rw [this]
  exact ⟨q.2, rfl⟩

theorem phiT_surj (x : SC) (hx : x ∈ Gs) :
    phiT (x.tr, rmPar (fun m => xor (x.fl m) (sgnT x.tr m))) = x := by
  rw [mem_Gs_iff, mem_RM13_iff] at hx
  refine SC.ext' rfl (funext fun m => ?_)
  simp only [phiT]
  rw [hx]
  simp

theorem phiT_inj : Function.Injective phiT := by
  rintro ⟨a, p⟩ ⟨b, p'⟩ h
  have h1 : a = b := congrArg SC.tr h
  subst h1
  have h2 := congrArg SC.fl h
  have : affine p = affine p' := funext fun m => by
    have := congrFun h2 m
    simp only [phiT] at this
    revert this
    cases sgnT a m <;> simp
  rw [affine_injective this]

theorem phiT_one : phiT (0, (false, false, false, false)) = 1 := by decide +kernel

/-! ## `Hc = closure {rcode 1, …, rcode 7}` equals `Gs` -/

def Hc : Subgroup SC := Subgroup.closure (Set.range fun i : Fin 7 => rcode i.succ)

theorem gen_mem (n : Fin 8) (hn : n ≠ 0) : rcode n ∈ Hc := by
  obtain ⟨j, rfl⟩ := (Fin.eq_zero_or_eq_succ n).resolve_left hn
  exact Subgroup.subset_closure ⟨j, rfl⟩

theorem rcode_mem (n : Fin 8) : rcode n ∈ Hc := by
  by_cases hn : n = 0
  · rw [hn, rcode_zero]; exact one_mem _
  · exact gen_mem n hn

def wordF (p : Par4) : SC :=
  (if p.1 then rcode 1 * rcode 1 else 1) * (if p.2.1 then rcode 2 * rcode 6 * rcode 4 else 1) *
    (if p.2.2.1 then rcode 1 * rcode 5 * rcode 4 else 1) *
    (if p.2.2.2 then rcode 1 * rcode 3 * rcode 2 else 1)

theorem phiT_word : ∀ q : Fin 8 × Par4, phiT q = wordF q.2 * rcode q.1 := by decide +kernel

theorem ite_mem {b : Bool} {x : SC} (hx : x ∈ Hc) : (if b then x else 1) ∈ Hc := by
  cases b
  · exact one_mem _
  · exact hx

theorem wordF_mem (p : Par4) : wordF p ∈ Hc := by
  have g := fun n : Fin 8 => rcode_mem n
  unfold wordF
  refine mul_mem (mul_mem (mul_mem (ite_mem ?_) (ite_mem ?_)) (ite_mem ?_)) (ite_mem ?_)
  · exact mul_mem (g 1) (g 1)
  · exact mul_mem (mul_mem (g 2) (g 6)) (g 4)
  · exact mul_mem (mul_mem (g 1) (g 5)) (g 4)
  · exact mul_mem (mul_mem (g 1) (g 3)) (g 2)

theorem Hc_eq : Hc = Gs := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    have : ∀ n : Fin 8, (⟨n, sgnT n⟩ : SC) ∈ Gs := by
      intro n; rw [mem_Gs_iff]; revert n; decide +kernel
    simpa [rcode_eqT] using this i.succ
  · intro x hx
    rw [← phiT_surj x hx, phiT_word]
    exact mul_mem (wordF_mem _) (rcode_mem _)

/-! ## The reader group `G` -/

/-- `G = closure {read 1, …, read 7}` inside the permutations of the 256 states. -/
def G : Subgroup (Equiv.Perm State) := Subgroup.closure (Set.range fun i : Fin 7 => read i.succ)

theorem G_eq : G = Gs.map T := by
  rw [← Hc_eq, Hc, MonoidHom.map_closure, ← Set.range_comp]
  have : (T ∘ fun i : Fin 7 => rcode i.succ) = fun i => read i.succ :=
    funext fun i => T_rcode _
  rw [this]; rfl

theorem mem_G {g : Equiv.Perm State} : g ∈ G ↔ ∃ q, T (phiT q) = g := by
  rw [G_eq, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, by rw [phiT_surj x hx]⟩
  · rintro ⟨q, rfl⟩
    exact ⟨phiT q, phiT_mem q, rfl⟩

theorem read_mem (n : Fin 8) : read n ∈ G := by
  rw [← T_rcode, G_eq]
  exact Subgroup.mem_map_of_mem T (Hc_eq ▸ rcode_mem n)

/-- (d) `|G| = 128`. -/
theorem card_G : Nat.card G = 128 := by
  rw [G_eq, Subgroup.card_map_of_injective T_injective]
  have e : Fin 8 × Par4 ≃ Gs :=
    Equiv.ofBijective (fun q => ⟨phiT q, phiT_mem q⟩)
      ⟨fun q q' h => phiT_inj (congrArg Subtype.val h),
       fun x => ⟨_, Subtype.ext (phiT_surj x.1 x.2)⟩⟩
  rw [← Nat.card_congr e]
  simp [Nat.card_eq_fintype_card]

def psi (q : Fin 8 × Par4) : G := ⟨T (phiT q), mem_G.2 ⟨q, rfl⟩⟩

theorem psi_bij : Function.Bijective psi :=
  ⟨fun q q' h => phiT_inj (T_injective (congrArg Subtype.val h)),
   fun g => by obtain ⟨q, hq⟩ := mem_G.1 g.2; exact ⟨q, Subtype.ext hq⟩⟩

noncomputable def psiEquiv : Fin 8 × Par4 ≃ G := Equiv.ofBijective psi psi_bij

theorem orderOf_psi (q : Fin 8 × Par4) : orderOf (psiEquiv q) = orderOf (phiT q) := by
  show orderOf (psi q) = _
  rw [← Subgroup.orderOf_coe]
  exact orderOf_injective T T_injective _

theorem orderOf_eq_four_iff {M : Type*} [Monoid M] (x : M) :
    orderOf x = 4 ↔ x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
  constructor
  · intro h
    refine ⟨h ▸ pow_orderOf_eq_one x, pow_ne_one_of_lt_orderOf (by norm_num) (by omega)⟩
  · rintro ⟨h4, h2⟩
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x) (by simpa using h2) (by simpa using h4)
    simpa using this

/-- (d) `G` has exactly 71 elements of order 2. -/
theorem card_order_two : Nat.card {g : G // orderOf g = 2} = 71 := by
  have h : ∀ q, (phiT q ^ 2 = 1 ∧ phiT q ≠ 1) ↔ orderOf (psiEquiv q) = 2 := fun q => by
    rw [orderOf_psi]; exact orderOf_eq_prime_iff.symm
  rw [← Nat.card_congr (psiEquiv.subtypeEquiv h), Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

/-- (d) `G` has exactly 56 elements of order 4. -/
theorem card_order_four : Nat.card {g : G // orderOf g = 4} = 56 := by
  have h : ∀ q, (phiT q ^ 4 = 1 ∧ phiT q ^ 2 ≠ 1) ↔ orderOf (psiEquiv q) = 4 := fun q => by
    rw [orderOf_psi]; exact (orderOf_eq_four_iff _).symm
  rw [← Nat.card_congr (psiEquiv.subtypeEquiv h), Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem phiT_pow_four : ∀ q, phiT q ^ 4 = 1 := by decide +kernel

/-- (d) `G` has exponent 4. -/
theorem exponent_G : Monoid.exponent G = 4 := by
  apply Nat.dvd_antisymm
  · rw [Monoid.exponent_dvd]
    intro g
    apply orderOf_dvd_of_pow_eq_one
    obtain ⟨q, rfl⟩ := psiEquiv.surjective g
    apply Subtype.ext
    show (T (phiT q)) ^ 4 = 1
    rw [← map_pow, phiT_pow_four, map_one]
  · have := Monoid.order_dvd_exponent (⟨read 1, read_mem 1⟩ : G)
    rwa [Subgroup.orderOf_mk, orderOf_read 1 (by decide)] at this


/-! ## Center and commutator subgroup -/

theorem center_dec : ∀ q : Fin 8 × Par4,
    (∀ i : Fin 7, (⟨i.succ, sgnT i.succ⟩ : SC) * phiT q = phiT q * ⟨i.succ, sgnT i.succ⟩) ↔
      (phiT q = 1 ∨ phiT q = Fc) := by decide +kernel

theorem Fc_central (g : SC) : g * Fc = Fc * g :=
  SC.ext' (by simp [Fc]) (by funext m; simp [Fc])

theorem read_flipAll (n : Fin 8) : read n * flipAll = flipAll * read n := by
  rw [← T_rcode, ← T_Fc, ← map_mul, ← map_mul, Fc_central]

/-- (d) The center of `G` is `{1, flipAll}`. -/
theorem mem_center_G (g : G) :
    g ∈ Subgroup.center G ↔ (g : Equiv.Perm State) = 1 ∨ (g : Equiv.Perm State) = flipAll := by
  obtain ⟨q, hq⟩ := mem_G.1 g.2
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    have key : ∀ i : Fin 7, rcode i.succ * phiT q = phiT q * rcode i.succ := fun i =>
      T_injective (by
        have := congrArg Subtype.val (h ⟨read i.succ, read_mem _⟩)
        simp only [Subgroup.coe_mul] at this
        rw [map_mul, map_mul, T_rcode, hq]
        exact this)
    simp only [rcode_eqT] at key
    rcases (center_dec q).1 key with h1 | h1
    · left; rw [← hq, h1, map_one]
    · right; rw [← hq, h1, T_Fc]
  · intro h k
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hle : G ≤ Subgroup.centralizer {(g : Equiv.Perm State)} := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rcases h with h | h
      · rw [h]; simp
      · rw [h, read_flipAll]
    exact ((Subgroup.mem_centralizer_iff.1 (hle k.2)) g rfl).symm

theorem comm_mul_mem {M : Type*} [Group M] (N : Subgroup M) (hN : N ≤ Subgroup.center M)
    {x y z : M} (hy : ⁅x, y⁆ ∈ N) (hz : ⁅x, z⁆ ∈ N) : ⁅x, y * z⁆ ∈ N := by
  have hc : ∀ g, g * ⁅x, z⁆ = ⁅x, z⁆ * g := Subgroup.mem_center_iff.1 (hN hz)
  have e : ⁅x, y * z⁆ = ⁅x, z⁆ * ⁅x, y⁆ := by
    calc ⁅x, y * z⁆ = (x * y * x⁻¹) * ⁅x, z⁆ * y⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = ⁅x, z⁆ * (x * y * x⁻¹) * y⁻¹ := by rw [hc]
      _ = ⁅x, z⁆ * ⁅x, y⁆ := by simp only [commutatorElement_def]; group
  rw [e]; exact N.mul_mem hz hy

theorem comm_inv_mem {M : Type*} [Group M] (N : Subgroup M) (hN : N ≤ Subgroup.center M)
    {x y : M} (hy : ⁅x, y⁆ ∈ N) : ⁅x, y⁻¹⁆ ∈ N := by
  have hc : ∀ g, g * ⁅x, y⁆⁻¹ = ⁅x, y⁆⁻¹ * g := Subgroup.mem_center_iff.1 (hN (N.inv_mem hy))
  have e : ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
    calc ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y := by simp only [commutatorElement_def]; group
      _ = ⁅x, y⁆⁻¹ * y⁻¹ * y := by rw [hc]
      _ = ⁅x, y⁆⁻¹ := by group
  rw [e]; exact N.inv_mem hy

theorem Fc_mul_Fc : Fc * Fc = 1 := by decide
theorem Fc_inv : Fc⁻¹ = Fc := by decide

def Nsub : Subgroup SC where
  carrier := {x | x = 1 ∨ x = Fc}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul Fc)
    · exact Or.inr (mul_one Fc)
    · exact Or.inl Fc_mul_Fc
  inv_mem' := by
    rintro a (rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr Fc_inv

theorem Nsub_le_center : Nsub ≤ Subgroup.center SC := by
  rintro x (rfl | rfl)
  · exact one_mem _
  · exact Subgroup.mem_center_iff.2 Fc_central

def KX (x : SC) : Subgroup SC where
  carrier := {y | ⁅x, y⁆ ∈ Nsub}
  one_mem' := by
    show ⁅x, 1⁆ ∈ Nsub
    rw [commutatorElement_one_right]; exact one_mem _
  mul_mem' := comm_mul_mem Nsub Nsub_le_center
  inv_mem' := comm_inv_mem Nsub Nsub_le_center

theorem comm_gens : ∀ (q : Fin 8 × Par4) (i : Fin 7),
    ⁅phiT q, (⟨i.succ, sgnT i.succ⟩ : SC)⁆ = 1 ∨ ⁅phiT q, (⟨i.succ, sgnT i.succ⟩ : SC)⁆ = Fc := by
  decide +kernel

theorem comm_Gs (x : SC) (hx : x ∈ Gs) (y : SC) (hy : y ∈ Gs) : ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = Fc := by
  have hle : Hc ≤ KX x := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    show ⁅x, rcode i.succ⁆ ∈ Nsub
    rw [← phiT_surj x hx, rcode_eqT]
    exact comm_gens _ i
  exact hle (Hc_eq ▸ hy)

theorem comm_12 : ⁅rcode 1, rcode 2⁆ = Fc := by decide +kernel

/-- (d) The commutator subgroup of `G` is `{1, flipAll}`. -/
theorem mem_commutator_G (g : G) :
    g ∈ commutator G ↔ (g : Equiv.Perm State) = 1 ∨ (g : Equiv.Perm State) = flipAll := by
  constructor
  · intro hg
    have hle : commutator G ≤ Subgroup.center G := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro g1 _ g2 _
      rw [mem_center_G]
      obtain ⟨q1, h1⟩ := mem_G.1 g1.2
      obtain ⟨q2, h2⟩ := mem_G.1 g2.2
      have e : ((⁅g1, g2⁆ : G) : Equiv.Perm State) = T ⁅phiT q1, phiT q2⁆ := by
        rw [map_commutatorElement, h1, h2]
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      rcases comm_Gs _ (phiT_mem q1) _ (phiT_mem q2) with h | h
      · left; rw [e, h, map_one]
      · right; rw [e, h, T_Fc]
    exact (mem_center_G g).1 (hle hg)
  · rintro (h | h)
    · have : g = 1 := Subtype.ext h
      rw [this]; exact one_mem _
    · have : g = ⁅(⟨read 1, read_mem 1⟩ : G), ⟨read 2, read_mem 2⟩⁆ := by
        apply Subtype.ext
        rw [h]
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← T_rcode, ← T_rcode, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
          ← commutatorElement_def, comm_12, T_Fc]
      rw [this, _root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)


/-! ## Orbits on the 256 states -/

/-- Even parity: an even number of coordinates equal `true`. -/
def par (s : State) : Prop := (Finset.univ.filter (fun m => s m = true)).card % 2 = 0

instance (s : State) : Decidable (par s) := inferInstanceAs (Decidable (_ = _))

/-- The even-parity states. -/
def Ev : Set State := {s | par s}

theorem G_smul (g : G) (s : State) : g • s = (g : Equiv.Perm State) s := rfl

theorem sgnT_zero : ∀ m : Fin 8, sgnT 0 m = false := by decide

/-- `s (m ⊕ a) ⊕ s m ⊕ sgn(a, m)`. -/
def Dfun (a : Fin 8) (s : State) : State := fun m => xor (xor (s (m ^^^ a)) (s m)) (sgnT a m)

theorem D_iff : ∀ (a : Fin 8) (s : State), Dfun a s ∈ RM13 ↔ (a = 0 ∨ ¬ par s) := by
  intro a
  rw [forall_state]
  revert a
  decide +kernel

theorem act_phiT (q : Fin 8 × Par4) (s : State) (m : Fin 8) :
    xor (s m) (actC (phiT q) s m) = xor (Dfun q.1 s m) (affine q.2 m) := by
  simp only [actC, phiT, Dfun]
  cases s m <;> cases s (m ^^^ q.1) <;> cases affine q.2 m <;> cases sgnT q.1 m <;> rfl

theorem smul_eq_actC {g : G} {q : Fin 8 × Par4} (hq : T (phiT q) = g) (s : State) :
    g • s = actC (phiT q) s := by
  rw [G_smul, ← hq]; rfl

/-- (e) For odd `s`: `t ∈ orbit(s)` iff `s ⊕ t ∈ RM(1,3)`. -/
theorem mem_orbit_odd (s : State) (hs : ¬ par s) (t : State) :
    t ∈ MulAction.orbit G s ↔ (fun m => xor (s m) (t m)) ∈ RM13 := by
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨q, hq⟩ := mem_G.1 g.2
    have h2 := RM_xor ((D_iff q.1 s).2 (Or.inr hs)) ⟨q.2, rfl⟩
    convert h2 using 1
    funext m
    show xor (s m) ((g • s) m) = _
    rw [smul_eq_actC hq, act_phiT]
  · rintro ⟨p, hp⟩
    refine ⟨psi (0, p), ?_⟩
    show psi (0, p) • s = t
    rw [smul_eq_actC (g := psi (0, p)) (q := (0, p)) rfl]
    funext m
    have h1 := congrFun hp m
    have h2 := act_phiT (0, p) s m
    have h3 : Dfun 0 s m = false := by simp [Dfun, sgnT_zero]
    rw [h3, h1] at h2
    revert h2
    cases s m <;> cases t m <;> cases actC (phiT (0, p)) s m <;> simp

def xorEquiv (s : State) : State ≃ State where
  toFun t m := xor (s m) (t m)
  invFun t m := xor (s m) (t m)
  left_inv t := by funext m; simp
  right_inv t := by funext m; simp

/-- (e) Each odd orbit has 16 elements. -/
theorem card_orbit_odd (s : State) (hs : ¬ par s) : Nat.card (MulAction.orbit G s) = 16 := by
  rw [← card_RM13]
  exact Nat.card_congr ((xorEquiv s).subtypeEquiv (fun t => mem_orbit_odd s hs t))

/-- (e) Each odd state has a stabilizer of order 8. -/
theorem card_stabilizer_odd (s : State) (hs : ¬ par s) :
    Nat.card (MulAction.stabilizer G s) = 8 := by
  have h := Subgroup.card_mul_index (MulAction.stabilizer G s)
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, card_orbit_odd s hs, card_G] at h
  omega

/-- The parity-preserving permutations. -/
def Ppar : Subgroup (Equiv.Perm State) where
  carrier := {g | ∀ s, par (g s) ↔ par s}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun ha hb s => (ha _).trans (hb s)
  inv_mem' := by
    intro g hg s
    have := hg (g⁻¹ s)
    have e : g (g⁻¹ s) = s := by simp
    rw [e] at this
    exact this.symm

theorem read_par : ∀ (n : Fin 8) (s : State), par (read n s) ↔ par s := by
  intro n
  simp only [read_apply, rcode_eqT]
  rw [forall_state]
  revert n
  decide +kernel

theorem G_le_Ppar : G ≤ Ppar := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  exact read_par i.succ

theorem card_Ev_aux :
    (Finset.univ.filter (fun s : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool =>
      par ![s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1, s.2.2.2.2.2.2.1,
        s.2.2.2.2.2.2.2])).card = 128 := by
  decide +kernel

def tupEquiv : (Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) ≃ State where
  toFun s := ![s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1, s.2.2.2.2.2.2.1,
    s.2.2.2.2.2.2.2]
  invFun s := (s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7)
  left_inv s := rfl
  right_inv s := by funext m; fin_cases m <;> rfl

/-- (e) There are 128 even-parity states. -/
theorem card_Ev : Nat.card Ev = 128 := by
  rw [← card_Ev_aux, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (tupEquiv.subtypeEquiv (fun _ => Iff.rfl))).symm

/-- (e) Even states have trivial stabilizer. -/
theorem stabilizer_even (s : State) (hs : par s) : MulAction.stabilizer G s = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg
  rw [Subgroup.mem_bot]
  obtain ⟨q, hq⟩ := mem_G.1 g.2
  rw [smul_eq_actC hq] at hg
  have hD : Dfun q.1 s = affine q.2 := funext fun m => by
    have := act_phiT q s m
    rw [hg] at this
    revert this
    cases s m <;> cases Dfun q.1 s m <;> cases affine q.2 m <;> simp
  have h0 : q.1 = 0 := ((D_iff q.1 s).1 ⟨q.2, hD.symm⟩).resolve_right (not_not.2 hs)
  have hz : affine q.2 = affine (false, false, false, false) := by
    rw [← hD, h0]; funext m; simp [Dfun, sgnT_zero, affine]
  have hq' : q = (0, (false, false, false, false)) := Prod.ext h0 (affine_injective hz)
  apply Subtype.ext
  rw [← hq, hq', phiT_one, map_one]; rfl

/-- (e) The even states form a single orbit. -/
theorem orbit_even (s : State) (hs : par s) : MulAction.orbit G s = Ev := by
  apply Set.eq_of_subset_of_ncard_le
  · rintro _ ⟨g, rfl⟩
    show par (g • s)
    rw [G_smul]
    exact (G_le_Ppar g.2 s).2 hs
  · rw [← MulAction.index_stabilizer, stabilizer_even s hs, Subgroup.index_bot, card_G,
      ← Nat.card_coe_set_eq, card_Ev]
  · exact Set.toFinite _

/-- (e) The action on the even states is regular: each `t ∈ Ev` is reached from each `s ∈ Ev` by
exactly one element of `G`. -/
theorem even_regular (s t : State) (hs : par s) (ht : par t) : ∃! g : G, g • s = t := by
  have : t ∈ MulAction.orbit G s := by rw [orbit_even s hs]; exact ht
  obtain ⟨g, hg⟩ := this
  refine ⟨g, hg, fun g' hg' => ?_⟩
  have h : g⁻¹ * g' ∈ MulAction.stabilizer G s := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hg', ← hg, inv_smul_smul]
  rw [stabilizer_even s hs, Subgroup.mem_bot] at h
  exact (inv_mul_eq_one.1 h).symm

/-- The RM criterion fails for even `s`: some `t` in its orbit has `s ⊕ t ∉ RM(1,3)`. -/
theorem orbit_even_not_RM (s : State) (hs : par s) :
    ∃ t ∈ MulAction.orbit G s, (fun m => xor (s m) (t m)) ∉ RM13 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hinj : Function.Injective (fun t : MulAction.orbit G s =>
      (⟨xorEquiv s t.1, h t.1 t.2⟩ : RM13)) := fun a b hab =>
    Subtype.ext ((xorEquiv s).injective (congrArg Subtype.val hab))
  have := Nat.card_le_card_of_injective _ hinj
  rw [card_RM13, orbit_even s hs, card_Ev] at this
  omega

/-- The state with a single `false` (encoded `-1`) coordinate, at `m`. -/
def oneDef (m : Fin 8) : State := fun k => decide (k ≠ m)

/-- The number of `false` (encoded `-1`) coordinates. -/
def nDefects (t : State) : ℕ := (Finset.univ.filter (fun k => t k = false)).card

theorem nDefects_one_iff : ∀ t : State, nDefects t = 1 ↔ ∃ m, t = oneDef m := by
  rw [forall_state]
  decide +kernel

theorem odd_has_def : ∀ s : State, ¬ par s → ∃ m, (fun k => xor (s k) (oneDef m k)) ∈ RM13 := by
  rw [forall_state]
  decide +kernel

theorem def_distinct : ∀ m m' : Fin 8,
    (fun k => xor (oneDef m k) (oneDef m' k)) ∈ RM13 → m = m' := by decide +kernel

theorem oneDef_odd : ∀ m : Fin 8, ¬ par (oneDef m) := by decide +kernel

/-- (e) Each odd orbit contains exactly one single-defect state. -/
theorem unique_defect (s : State) (hs : ¬ par s) :
    ∃! t, t ∈ MulAction.orbit G s ∧ nDefects t = 1 := by
  obtain ⟨m, hm⟩ := odd_has_def s hs
  refine ⟨oneDef m, ⟨(mem_orbit_odd s hs _).2 hm, (nDefects_one_iff _).2 ⟨m, rfl⟩⟩, ?_⟩
  rintro t ⟨ht, hd⟩
  obtain ⟨m', rfl⟩ := (nDefects_one_iff t).1 hd
  have h1 := RM_xor ((mem_orbit_odd s hs _).1 ht) hm
  have key : ∀ a b c : Bool, xor (xor a b) (xor a c) = xor b c := by decide
  simp only [key] at h1
  rw [def_distinct m' m h1]

theorem orbit_oneDef_injective :
    Function.Injective (fun m : Fin 8 => MulAction.orbit G (oneDef m)) := by
  intro m m' h
  have h1 : oneDef m ∈ MulAction.orbit G (oneDef m') := MulAction.orbit_eq_iff.1 h
  exact (def_distinct m' m ((mem_orbit_odd _ (oneDef_odd m') _).1 h1)).symm

/-- (e) The odd states fall into exactly 8 orbits. -/
theorem odd_orbits :
    {O : Set State | ∃ s, ¬ par s ∧ O = MulAction.orbit G s} =
      Set.range (fun m : Fin 8 => MulAction.orbit G (oneDef m)) ∧
    Set.ncard {O : Set State | ∃ s, ¬ par s ∧ O = MulAction.orbit G s} = 8 := by
  have e : {O : Set State | ∃ s, ¬ par s ∧ O = MulAction.orbit G s} =
      Set.range (fun m : Fin 8 => MulAction.orbit G (oneDef m)) := by
    ext O
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨m, hm⟩ := odd_has_def s hs
      exact ⟨m, MulAction.orbit_eq_iff.2 ((mem_orbit_odd s hs _).2 hm)⟩
    · rintro ⟨m, rfl⟩
      exact ⟨oneDef m, oneDef_odd m, rfl⟩
  refine ⟨e, ?_⟩
  rw [e, Set.ncard_range_of_injective orbit_oneDef_injective]
  simp

end Bridge4B
