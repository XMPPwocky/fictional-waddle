import Mathlib

/-!
# Octonion readers: seven period-4 maps generate a group of order 128

States are `St := Fin 8 → Bool`. The octonions `Oct` are copied from
`scratch/society/OctonionMoufangLoopA.lean`: pairs of integer quaternions with
`(a, b) * (c, d) = (a * c - star d * b, d * a + b * star c)` and basis units `e 0, …, e 7`.
A state is encoded as `encO s = Σ_m enc' (s m) • e m`, with `enc' true = 1`,
`enc' false = -1`. `flipAll` negates every coordinate, `flipHigh` negates coordinates
`4, 5, 6, 7`. `read n = act n (sgn n)` is the signed translation
`(read n s) p = s (p xor n) xor sgn n p`, where `sgn` is a sign table; the table is not
trusted, `read_spec` proves the defining property against the octonion product.
`G` is `Subgroup.closure {read 1, …, read 7}` in `Equiv.Perm St`, acting on states by
application. `RM13` is the set of the 16 affine Boolean functions `p ↦ u·p + b` of the
three bits of the coordinate index (the Reed–Muller code `RM(1,3)`, i.e. the extended
Hamming `[8,4,4]` code).

PROVED
* (0) `read_spec`: `encO (read n s) = e n * encO s` for all `n s`; `read_unique`:
  for every `n` (in particular every `n ≠ 0`) there is exactly one map `f : St → St`
  with `encO (f s) = e n * encO s` for all `s`.
* (a) `read_pair`: for `n ≠ 0` and every `m`, either `(read n s m, read n s (m xor n)) =
  step (s m, s (m xor n))` for all `s`, or `= step^[3] (s m, s (m xor n))` for all `s`.
  `read_sq`: `read n ^ 2 = flipAll`; `orderOf_read`: `orderOf (read n) = 4` (`n ≠ 0`).
* (b) `read_anticomm`: `read n * read n' = flipAll * read n' * read n` for distinct
  nonzero `n n'`.
* (c) `read_one_two`, `read_one_two_comp`: `read 1 ∘ read 2 = read 3 ∘ flipHigh`.
* Further fact: `read_prod`, `read_prod_comp`: `read 1 ∘ read 2 ∘ … ∘ read 7 = flipAll`.
* (d) `card_G`: `Nat.card G = 128`; `exponent_G`: `Monoid.exponent G = 4`;
  `card_order_two`: 71 elements of order 2; `card_order_four`: 56 elements of order 4;
  `mem_center_G`, `center_G_eq`: the center is `{1, flipAll}`;
  `mem_commutator_G`, `commutator_G_eq`: `⁅G, G⁆ = {1, flipAll}` in `Equiv.Perm St`;
  `mem_derived_G`: the same for the derived subgroup `commutator ↥G`.
  Also `mem_G_iff`, `card_RM13`: `G` is exactly `{act a (sgn a + r) | a ∈ 𝔽₂³, r ∈ RM(1,3)}`.
* (e) `card_even`: there are 128 even states; `even_orbit`: for even `s`, the orbit of
  `s` is the set of all even states and the stabilizer is trivial; `even_regular`: for
  even `s t` there is exactly one `g ∈ G` with `g • s = t`.
  `odd_orbit_iff`: for odd `s`, `t ∈ orbit s ↔ s xor t ∈ RM(1,3)`;
  `odd_orbit_card`: every odd orbit has 16 elements and every odd stabilizer 8;
  `card_odd_orbits`: the odd states form exactly 8 orbits;
  `odd_orbit_single_defect`: each odd orbit contains exactly one single-defect state.

INTERPRETED
* The task refers to `encO`, `enc'`, `flipAll`, `flipHigh` "as given" without their
  text. They are rendered as above: `enc'` is the `±1` encoding of `RootsOfUnityGamesA.enc`
  over `ℤ`, and `encO s` has `enc' (s m)` as its `e m` coefficient. `flipAll` and
  `flipHigh` are pinned down by (a) and (c) given `read`: `flipAll = read n ^ 2` and
  `flipHigh = (read 3)⁻¹ * read 1 * read 2`.
* `step` is copied from `RootsOfUnityGamesA`: `step (a, b) = (b, !a)`. "Acts on the pair
  as `step` or `step^[3]`" is read with the choice depending on `n, m` but not on `s`,
  which is stronger than a per-state choice.
* "xor" on indices is `^^^` on `Fin 8`; on states it is coordinatewise `^^`.
* Parity of a state is the parity of `wt s`, the number of `true` coordinates (equal to
  the parity of the number of `false` coordinates, since 8 is even). "Single-defect" is
  `SingleDefect t`: exactly one coordinate is `false`.
* The criterion `t ∈ orbit(s) ↔ s xor t ∈ RM(1,3)` is stated for odd `s`; for even `s`
  it is false as written, since that orbit has 128 elements while `RM(1,3)` has 16.
* Orbits and stabilizers are `MulAction.orbit` and `MulAction.stabilizer` for the action
  of `↥G` on `St` inherited from `Equiv.Perm St`. "Center" and "commutator subgroup" are
  `Subgroup.center ↥G` (stated through `G.subtype`) and both `⁅G, G⁆` and `commutator ↥G`.
* Finite facts (sign table, cocycle and coset identities, parity and defect checks on the
  256 states, element counts over the 128-element parametrisation) are checked by
  `decide +kernel`.
-/

namespace Bridge4A

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

instance : One Oct := ⟨⟨1, 0⟩⟩

instance : Neg Oct := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩

def qbasis : Fin 4 → ℍ[ℤ] :=
  ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

def e (n : Fin 8) : Oct :=
  if h : n.val < 4 then ⟨qbasis ⟨n.val, h⟩, 0⟩ else ⟨0, qbasis ⟨n.val - 4, by omega⟩⟩

abbrev St := Fin 8 → Bool

def enc' : Bool → ℤ
  | true => 1
  | false => -1

def encO (s : St) : Oct :=
  ⟨⟨enc' (s 0), enc' (s 1), enc' (s 2), enc' (s 3)⟩,
   ⟨enc' (s 4), enc' (s 5), enc' (s 6), enc' (s 7)⟩⟩

/-- Bit `p` of `sgnRow n` records the sign in `e n * e (p xor n) = ± e p`. -/
def sgnRow : Fin 8 → ℕ := ![0, 149, 57, 83, 225, 139, 39, 77]

def sgn (n p : Fin 8) : Bool := (sgnRow n).testBit p.val

theorem fxx : ∀ p a : Fin 8, (p ^^^ a) ^^^ a = p := by decide
theorem fassoc : ∀ p a b : Fin 8, (p ^^^ a) ^^^ b = p ^^^ (a ^^^ b) := by decide

def actFun (a : Fin 8) (c : Fin 8 → Bool) (s : St) : St := fun p => s (p ^^^ a) ^^ c p

/-- The signed translation `s ↦ (p ↦ s (p xor a) xor c p)`. -/
def act (a : Fin 8) (c : Fin 8 → Bool) : Equiv.Perm St where
  toFun := actFun a c
  invFun := actFun a (fun p => c (p ^^^ a))
  left_inv s := by funext p; simp [actFun, fxx]
  right_inv s := by funext p; simp [actFun, fxx]

/-- The reader `read n`: left multiplication by `e n`, transported to states. -/
def read (n : Fin 8) : Equiv.Perm St := act n (sgn n)

theorem tuple_eq (s : St) : s = ![s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] := by
  funext p; fin_cases p <;> rfl

theorem forall_st {P : St → Prop}
    (h : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, P ![b0, b1, b2, b3, b4, b5, b6, b7]) (s : St) :
    P s := by
  rw [tuple_eq s]; exact h _ _ _ _ _ _ _ _

theorem read_spec_tuple : ∀ n : Fin 8, ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    encO (read n ![b0, b1, b2, b3, b4, b5, b6, b7]) =
      e n * encO ![b0, b1, b2, b3, b4, b5, b6, b7] := by
  decide +kernel

/-! ## (0) Existence and uniqueness of the reader -/

theorem read_spec (n : Fin 8) (s : St) : encO (read n s) = e n * encO s :=
  forall_st (P := fun s => encO (read n s) = e n * encO s) (read_spec_tuple n) s

theorem enc'_inj : ∀ a b : Bool, enc' a = enc' b → a = b := by decide

theorem encO_injective : Function.Injective encO := by
  intro s t h
  obtain ⟨h1, h2⟩ := Oct.mk.inj h
  obtain ⟨a0, a1, a2, a3⟩ := QuaternionAlgebra.mk.inj h1
  obtain ⟨a4, a5, a6, a7⟩ := QuaternionAlgebra.mk.inj h2
  funext p
  fin_cases p
  · exact enc'_inj _ _ a0
  · exact enc'_inj _ _ a1
  · exact enc'_inj _ _ a2
  · exact enc'_inj _ _ a3
  · exact enc'_inj _ _ a4
  · exact enc'_inj _ _ a5
  · exact enc'_inj _ _ a6
  · exact enc'_inj _ _ a7

/-- (0) For every `n` there is exactly one map `f` with `encO (f s) = e n * encO s`,
and it is `read n`. -/
theorem read_unique (n : Fin 8) :
    ∃! f : St → St, ∀ s, encO (f s) = e n * encO s := by
  refine ⟨read n, read_spec n, fun f hf => ?_⟩
  funext s
  exact encO_injective ((hf s).trans (read_spec n s).symm)

theorem read_unique_ne_zero (n : Fin 8) (_hn : n ≠ 0) :
    ∃! f : St → St, ∀ s, encO (f s) = e n * encO s :=
  read_unique n


/-! ## The signed-translation group -/

theorem fx0 : ∀ p : Fin 8, p ^^^ 0 = p := by decide
theorem f0x : ∀ p : Fin 8, 0 ^^^ p = p := by decide
theorem fself : ∀ p : Fin 8, p ^^^ p = 0 := by decide
theorem fcomm : ∀ p q : Fin 8, p ^^^ q = q ^^^ p := by decide

@[simp] theorem act_apply (a : Fin 8) (c : Fin 8 → Bool) (s : St) (p : Fin 8) :
    act a c s p = (s (p ^^^ a) ^^ c p) := rfl

theorem act_mul (a b : Fin 8) (c d : Fin 8 → Bool) :
    act a c * act b d = act (a ^^^ b) (fun p => c p ^^ d (p ^^^ a)) := by
  ext s p
  simp only [Equiv.Perm.mul_apply, act_apply, fassoc]
  cases s (p ^^^ (a ^^^ b)) <;> cases c p <;> cases d (p ^^^ a) <;> rfl

theorem act_inv (a : Fin 8) (c : Fin 8 → Bool) :
    (act a c)⁻¹ = act a (fun p => c (p ^^^ a)) := by
  ext s p; rfl

theorem act_zero_zero : act 0 (fun _ => false) = 1 := by
  ext s p; simp

theorem act_eq_key : ∀ a b : Fin 8, ∀ x : Bool,
    (decide (a ^^^ a = 0) ^^ x) = (decide (a ^^^ b = 0) ^^ x) → a = b := by decide

theorem act_eq_iff (a b : Fin 8) (c d : Fin 8 → Bool) :
    act a c = act b d ↔ a = b ∧ c = d := by
  constructor
  · intro h
    have hc : c = d := by
      funext p
      have := congrFun (congrArg (fun g : Equiv.Perm St => g (fun _ => false)) h) p
      simpa using this
    subst hc
    refine ⟨?_, rfl⟩
    have := congrFun (congrArg (fun g : Equiv.Perm St => g (fun q => decide (q = 0))) h) a
    exact act_eq_key a b (c a) this
  · rintro ⟨rfl, rfl⟩; rfl

/-- `flipAll s = fun m => !s m`. -/
def flipAll : Equiv.Perm St where
  toFun s := fun m => !s m
  invFun s := fun m => !s m
  left_inv s := by funext m; simp
  right_inv s := by funext m; simp

/-- `flipHigh` negates the coordinates `4, 5, 6, 7` (the second quaternion). -/
def flipHigh : Equiv.Perm St where
  toFun s := fun m => if 4 ≤ m.val then !s m else s m
  invFun s := fun m => if 4 ≤ m.val then !s m else s m
  left_inv s := by funext m; by_cases h : 4 ≤ m.val <;> simp [h]
  right_inv s := by funext m; by_cases h : 4 ≤ m.val <;> simp [h]

theorem flipAll_eq : flipAll = act 0 (fun _ => true) := by
  ext s p; simp [flipAll]

theorem flipHigh_eq : flipHigh = act 0 (fun m => decide (4 ≤ m.val)) := by
  ext s p
  show (if 4 ≤ p.val then !s p else s p) = (s (p ^^^ 0) ^^ decide (4 ≤ p.val))
  rw [fx0]; by_cases h : 4 ≤ p.val <;> simp [h]

theorem sgn_zero : sgn 0 = fun _ => false := by decide

theorem read_zero : read 0 = 1 := by rw [read, sgn_zero, act_zero_zero]

theorem flipAll_ne_one : flipAll ≠ 1 := by
  intro h
  have := congrFun (congrArg (fun g : Equiv.Perm St => g (fun _ => false)) h) 0
  simp [flipAll] at this

theorem flipAll_mul_self : flipAll * flipAll = 1 := by
  ext s p; simp [flipAll]

theorem flipAll_sq : flipAll ^ 2 = 1 := by rw [pow_two, flipAll_mul_self]

theorem flipAll_inv : flipAll⁻¹ = flipAll := by
  rw [inv_eq_iff_mul_eq_one, flipAll_mul_self]

/-! ## (a) Each reader acts on the pair `(s m, s (m xor n))` as `step` or `step^[3]` -/

/-- One level deeper of reading (as in `RootsOfUnityGamesA.step`). -/
def step : Bool × Bool → Bool × Bool
  | (a, b) => (b, !a)

theorem step3 (x : Bool × Bool) : step^[3] x = (!x.2, x.1) := by
  obtain ⟨a, b⟩ := x; cases a <;> cases b <;> rfl

theorem sgn_pair : ∀ n m : Fin 8, n ≠ 0 →
    (sgn n m = false ∧ sgn n (m ^^^ n) = true) ∨
      (sgn n m = true ∧ sgn n (m ^^^ n) = false) := by decide

/-- (a) For `n ≠ 0` and every coordinate `m`, `read n` maps the pair
`(s m, s (m xor n))` to `step` of it for all `s`, or to `step^[3]` of it for all `s`. -/
theorem read_pair (n : Fin 8) (hn : n ≠ 0) (m : Fin 8) :
    (∀ s : St, (read n s m, read n s (m ^^^ n)) = step (s m, s (m ^^^ n))) ∨
      (∀ s : St, (read n s m, read n s (m ^^^ n)) = step^[3] (s m, s (m ^^^ n))) := by
  rcases sgn_pair n m hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; intro s
    simp only [read, act_apply, fxx, h1, h2, step, Bool.xor_false, Bool.xor_true]
  · right; intro s
    rw [step3]
    simp only [read, act_apply, fxx, h1, h2, Bool.xor_false, Bool.xor_true]

theorem read_sq_key : ∀ n : Fin 8, n ≠ 0 →
    n ^^^ n = 0 ∧ (fun p => sgn n p ^^ sgn n (p ^^^ n)) = fun _ => true := by decide

/-- (a) `(read n)^2 = flipAll` for `n ≠ 0`. -/
theorem read_sq (n : Fin 8) (hn : n ≠ 0) : read n ^ 2 = flipAll := by
  rw [pow_two, read, act_mul, flipAll_eq, act_eq_iff]
  exact read_sq_key n hn

/-- (a) `read n` has order exactly `4` for `n ≠ 0`. -/
theorem orderOf_read (n : Fin 8) (hn : n ≠ 0) : orderOf (read n) = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := read n)
    (by rw [pow_one, read_sq n hn]; exact flipAll_ne_one)
    (by rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 from rfl, pow_mul, read_sq n hn, flipAll_sq])
  simpa using h

/-! ## (b), (c) and the ordered product -/

/-- (b) Distinct readers anticommute up to `flipAll`. -/
theorem read_anticomm (n n' : Fin 8) (hn : n ≠ 0) (hn' : n' ≠ 0) (hnn : n ≠ n') :
    read n * read n' = flipAll * read n' * read n := by
  simp only [read, flipAll_eq, act_mul, act_eq_iff]
  revert hn hn' hnn
  revert n n'
  decide +kernel

/-- (c) `read 1 * read 2 = read 3 * flipHigh` in `Equiv.Perm St`. -/
theorem read_one_two : read 1 * read 2 = read 3 * flipHigh := by
  simp only [read, flipHigh_eq, act_mul, act_eq_iff]
  decide +kernel

/-- (c) As maps: `read 1 ∘ read 2 = read 3 ∘ flipHigh`. -/
theorem read_one_two_comp : ⇑(read 1) ∘ ⇑(read 2) = ⇑(read 3) ∘ ⇑flipHigh := by
  rw [← Equiv.Perm.coe_mul, ← Equiv.Perm.coe_mul, read_one_two]

/-- The ordered product of the seven readers is `flipAll`. -/
theorem read_prod :
    read 1 * read 2 * read 3 * read 4 * read 5 * read 6 * read 7 = flipAll := by
  simp only [read, flipAll_eq, act_mul, act_eq_iff]
  decide +kernel

theorem read_prod_comp :
    ⇑(read 1) ∘ ⇑(read 2) ∘ ⇑(read 3) ∘ ⇑(read 4) ∘ ⇑(read 5) ∘ ⇑(read 6) ∘ ⇑(read 7) =
      ⇑flipAll := by
  rw [← read_prod]; rfl


/-! ## RM(1,3) -/

/-- `dot u p`: the mod-2 inner product of the 3-bit expansions of `u` and `p`. -/
def dot (u p : Fin 8) : Bool :=
  (u.val.testBit 0 && p.val.testBit 0) ^^ (u.val.testBit 1 && p.val.testBit 1) ^^
    (u.val.testBit 2 && p.val.testBit 2)

/-- The affine Boolean function `p ↦ u·p + b` on `𝔽₂³`, as a word of length 8. -/
def rmw (u : Fin 8) (b : Bool) : Fin 8 → Bool := fun p => dot u p ^^ b

/-- The first-order Reed–Muller code `RM(1,3)` (the extended Hamming `[8,4,4]` code):
the 16 affine functions of the three bits of the coordinate index. -/
def RM13 : Set (Fin 8 → Bool) := Set.range fun x : Fin 8 × Bool => rmw x.1 x.2

def InRM (v : Fin 8 → Bool) : Prop := ∃ u : Fin 8, ∃ b : Bool, rmw u b = v

instance : DecidablePred InRM := fun v =>
  inferInstanceAs (Decidable (∃ u : Fin 8, ∃ b : Bool, rmw u b = v))

theorem mem_RM13 (v : Fin 8 → Bool) : v ∈ RM13 ↔ InRM v :=
  ⟨fun ⟨x, h⟩ => ⟨x.1, x.2, h⟩, fun ⟨u, b, h⟩ => ⟨(u, b), h⟩⟩

theorem card_RM13 : RM13.ncard = 16 := by
  rw [RM13, Set.ncard_range_of_injective]
  · rw [Nat.card_eq_fintype_card]; rfl
  · rintro ⟨u, b⟩ ⟨u', b'⟩ h
    revert h; revert u b u' b'; decide

/-- Decoder for affine words. -/
def rmdecU (v : Fin 8 → Bool) : Fin 8 :=
  (if v 1 ^^ v 0 then 1 else 0) + (if v 2 ^^ v 0 then 2 else 0) + (if v 4 ^^ v 0 then 4 else 0)

theorem dec_rmw : ∀ u : Fin 8, ∀ b : Bool, rmw (rmdecU (rmw u b)) (rmw u b 0) = rmw u b := by
  decide

theorem InRM_iff_dec (v : Fin 8 → Bool) : InRM v ↔ rmw (rmdecU v) (v 0) = v := by
  constructor
  · rintro ⟨u, b, rfl⟩; exact dec_rmw u b
  · intro h; exact ⟨_, _, h⟩

theorem rmw_inj : ∀ u b u' b', rmw u b = rmw u' b' → u = u' ∧ b = b' := by decide +kernel

theorem dot_xor : ∀ u u' p : Fin 8, dot (u ^^^ u') p = (dot u p ^^ dot u' p) := by decide
theorem dot_shift : ∀ u p a : Fin 8, dot u (p ^^^ a) = (dot u p ^^ dot u a) := by decide +kernel
theorem dot_zero : ∀ p : Fin 8, dot 0 p = false := by decide

theorem InRM.xor {v w : Fin 8 → Bool} (hv : InRM v) (hw : InRM w) :
    InRM (fun p => v p ^^ w p) := by
  obtain ⟨u, b, rfl⟩ := hv
  obtain ⟨u', b', rfl⟩ := hw
  refine ⟨u ^^^ u', b ^^ b', ?_⟩
  funext p
  simp only [rmw, dot_xor]
  cases dot u p <;> cases dot u' p <;> cases b <;> cases b' <;> rfl

theorem InRM.shift {v : Fin 8 → Bool} (hv : InRM v) (a : Fin 8) :
    InRM (fun p => v (p ^^^ a)) := by
  obtain ⟨u, b, rfl⟩ := hv
  refine ⟨u, b ^^ dot u a, ?_⟩
  funext p
  simp only [rmw, dot_shift]
  cases dot u p <;> cases dot u a <;> cases b <;> rfl

theorem InRM.congr {v w : Fin 8 → Bool} (hv : InRM v) (h : v = w) : InRM w := h ▸ hv

theorem InRM_zero : InRM (fun _ => false) := ⟨0, false, by funext p; simp [rmw, dot_zero]⟩

theorem cocycle : ∀ a b : Fin 8,
    InRM (fun p => sgn a p ^^ sgn b (p ^^^ a) ^^ sgn (a ^^^ b) p) := by
  decide +kernel

theorem sgn_inv : ∀ a : Fin 8, InRM (fun p => sgn a (p ^^^ a) ^^ sgn a p) := by
  decide +kernel

/-! ## (d) The group generated by the seven readers -/

/-- The seven readers generate `G`. -/
def G : Subgroup (Equiv.Perm St) :=
  Subgroup.closure {read 1, read 2, read 3, read 4, read 5, read 6, read 7}

/-- Explicit description: signed translations `act a c` with `c + sgn a ∈ RM(1,3)`. -/
def H : Subgroup (Equiv.Perm St) where
  carrier := {g | ∃ a c, InRM (fun p => c p ^^ sgn a p) ∧ act a c = g}
  one_mem' := ⟨0, fun _ => false, by decide, act_zero_zero⟩
  mul_mem' := by
    rintro _ _ ⟨a, c, hc, rfl⟩ ⟨b, d, hd, rfl⟩
    refine ⟨a ^^^ b, _, ?_, (act_mul a b c d).symm⟩
    refine ((hc.xor (hd.shift a)).xor (cocycle a b)).congr ?_
    funext p
    cases c p <;> cases d (p ^^^ a) <;> cases sgn a p <;> cases sgn b (p ^^^ a) <;>
      cases sgn (a ^^^ b) p <;> rfl
  inv_mem' := by
    rintro _ ⟨a, c, hc, rfl⟩
    refine ⟨a, fun p => c (p ^^^ a), ?_, (act_inv a c).symm⟩
    refine ((hc.shift a).xor (sgn_inv a)).congr ?_
    funext p
    try beta_reduce
    cases c (p ^^^ a) <;> cases sgn a (p ^^^ a) <;> cases sgn a p <;> rfl

theorem read_mem_H (n : Fin 8) : read n ∈ H :=
  ⟨n, sgn n, ⟨0, false, by funext p; simp [rmw, dot_zero]⟩, rfl⟩

theorem G_le_H : G ≤ H := by
  rw [G, Subgroup.closure_le]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨read_mem_H 1, read_mem_H 2, read_mem_H 3, read_mem_H 4, read_mem_H 5, read_mem_H 6,
    read_mem_H 7⟩

theorem fin8_cases : ∀ n : Fin 8, n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by
  decide

theorem read_mem_G (n : Fin 8) : read n ∈ G := by
  rcases fin8_cases n with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [read_zero]; exact one_mem _
  all_goals exact Subgroup.subset_closure (by simp)

theorem act0_mul (v w : Fin 8 → Bool) : act 0 v * act 0 w = act 0 (fun p => v p ^^ w p) := by
  rw [act_mul, fself]; simp only [fx0]

theorem basis4 : act 0 (rmw 4 false) = read 1 * read 2 * (read 3)⁻¹ := by
  simp only [read, act_inv, act_mul, act_eq_iff]; decide +kernel
theorem basis2 : act 0 (rmw 2 false) = read 1 * read 4 * (read 5)⁻¹ := by
  simp only [read, act_inv, act_mul, act_eq_iff]; decide +kernel
theorem basis1 : act 0 (rmw 1 false) = read 2 * read 4 * (read 6)⁻¹ := by
  simp only [read, act_inv, act_mul, act_eq_iff]; decide +kernel
theorem basis0 : act 0 (rmw 0 true) = read 1 * read 1 := by
  simp only [read, act_mul, act_eq_iff]; decide +kernel

theorem sel_mem {v : Fin 8 → Bool} (h : act 0 v ∈ G) (β : Bool) :
    act 0 (fun p => β && v p) ∈ G := by
  cases β
  · simp only [Bool.false_and]; rw [act_zero_zero]; exact one_mem _
  · simpa using h

theorem rmw_decomp : ∀ u b, rmw u b = fun p =>
    ((u.val.testBit 0 && rmw 1 false p) ^^ (u.val.testBit 1 && rmw 2 false p)) ^^
      ((u.val.testBit 2 && rmw 4 false p) ^^ (b && rmw 0 true p)) := by
  decide +kernel

theorem rmw_mem (u : Fin 8) (b : Bool) : act 0 (rmw u b) ∈ G := by
  have h1 : act 0 (rmw 1 false) ∈ G := by
    rw [basis1]; exact mul_mem (mul_mem (read_mem_G _) (read_mem_G _)) (inv_mem (read_mem_G _))
  have h2 : act 0 (rmw 2 false) ∈ G := by
    rw [basis2]; exact mul_mem (mul_mem (read_mem_G _) (read_mem_G _)) (inv_mem (read_mem_G _))
  have h4 : act 0 (rmw 4 false) ∈ G := by
    rw [basis4]; exact mul_mem (mul_mem (read_mem_G _) (read_mem_G _)) (inv_mem (read_mem_G _))
  have h0 : act 0 (rmw 0 true) ∈ G := by
    rw [basis0]; exact mul_mem (read_mem_G _) (read_mem_G _)
  have := mul_mem (mul_mem (sel_mem h1 (u.val.testBit 0)) (sel_mem h2 (u.val.testBit 1)))
    (mul_mem (sel_mem h4 (u.val.testBit 2)) (sel_mem h0 b))
  rw [act0_mul, act0_mul, act0_mul] at this
  rw [rmw_decomp u b]
  exact this

theorem H_le_G : H ≤ G := by
  rintro _ ⟨a, c, ⟨u, b, hub⟩, rfl⟩
  have : act a c = act 0 (rmw u b) * read a := by
    rw [read, act_mul, act_eq_iff]
    refine ⟨(f0x a).symm, ?_⟩
    funext p
    rw [hub, fx0]
    dsimp only
    cases c p <;> cases sgn a p <;> rfl
  rw [this]
  exact mul_mem (rmw_mem u b) (read_mem_G a)

theorem G_eq_H : G = H := le_antisymm G_le_H H_le_G

/-- The parametrisation of `G` by `(a, u, b) ∈ 𝔽₂³ × 𝔽₂³ × 𝔽₂`. -/
def cv (x : Fin 8 × Fin 8 × Bool) : Fin 8 → Bool := fun p => sgn x.1 p ^^ rmw x.2.1 x.2.2 p

def ψ (x : Fin 8 × Fin 8 × Bool) : Equiv.Perm St := act x.1 (cv x)

theorem ψ_mem (x : Fin 8 × Fin 8 × Bool) : ψ x ∈ G := by
  rw [G_eq_H]
  refine ⟨x.1, cv x, ⟨x.2.1, x.2.2, ?_⟩, rfl⟩
  funext p
  simp only [cv]
  cases sgn x.1 p <;> cases rmw x.2.1 x.2.2 p <;> rfl

theorem mem_G_iff (g : Equiv.Perm St) : g ∈ G ↔ ∃ x, ψ x = g := by
  constructor
  · intro hg
    rw [G_eq_H] at hg
    obtain ⟨a, c, ⟨u, b, hub⟩, rfl⟩ := hg
    refine ⟨(a, u, b), ?_⟩
    simp only [ψ]
    congr 1
    funext p
    simp only [cv, hub]
    cases c p <;> cases sgn a p <;> rfl
  · rintro ⟨x, rfl⟩; exact ψ_mem x

theorem ψ_injective : Function.Injective ψ := by
  rintro ⟨a, u, b⟩ ⟨a', u', b'⟩ h
  obtain ⟨rfl, h2⟩ := (act_eq_iff _ _ _ _).1 h
  have : rmw u b = rmw u' b' := by
    funext p
    have := congrFun h2 p
    simpa [cv] using this
  obtain ⟨rfl, rfl⟩ := rmw_inj _ _ _ _ this
  rfl

theorem coe_G_eq_range : (G : Set (Equiv.Perm St)) = Set.range ψ := by
  ext g; exact (mem_G_iff g).trans Iff.rfl

/-- (d) `|G| = 128`. -/
theorem card_G : Nat.card G = 128 := by
  have : Nat.card G = Nat.card (Set.range ψ) := by rw [← coe_G_eq_range]; rfl
  rw [this, Nat.card_range_of_injective ψ_injective, Nat.card_eq_fintype_card]
  rfl

noncomputable def eqv : (Fin 8 × Fin 8 × Bool) ≃ G :=
  Equiv.ofBijective (fun x => ⟨ψ x, ψ_mem x⟩)
    ⟨fun x y h => ψ_injective (congrArg Subtype.val h), fun g => by
      obtain ⟨x, hx⟩ := (mem_G_iff g).1 g.2
      exact ⟨x, Subtype.ext hx⟩⟩

theorem coe_eqv (x : Fin 8 × Fin 8 × Bool) : ((eqv x : G) : Equiv.Perm St) = ψ x := rfl

theorem act_pow_four (a : Fin 8) (c : Fin 8 → Bool) : act a c ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two (act a c), act_mul, fself, pow_two,
    act0_mul]
  convert act_zero_zero using 2
  funext p
  simp

theorem G_pow_four (g : G) : g ^ 4 = 1 := by
  obtain ⟨x, hx⟩ := (mem_G_iff g).1 g.2
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hx]
  exact act_pow_four _ _

/-- (d) `G` has exponent `4`. -/
theorem exponent_G : Monoid.exponent G = 4 := by
  apply Nat.dvd_antisymm
  · exact Monoid.exponent_dvd_of_forall_pow_eq_one G_pow_four
  · have := Monoid.order_dvd_exponent (⟨read 1, read_mem_G 1⟩ : G)
    rwa [← Subgroup.orderOf_coe, orderOf_read 1 (by decide)] at this

def sqv (x : Fin 8 × Fin 8 × Bool) : Fin 8 → Bool := fun p => cv x p ^^ cv x (p ^^^ x.1)

theorem ψ_sq (x : Fin 8 × Fin 8 × Bool) : ψ x ^ 2 = act 0 (sqv x) := by
  rw [pow_two, ψ, act_mul, fself]; rfl

theorem ψ_zero : ψ (0, 0, false) = 1 := by
  rw [ψ, show cv (0, 0, false) = fun _ => false by decide]; exact act_zero_zero

theorem ψ_flip : ψ (0, 0, true) = flipAll := by
  rw [ψ, flipAll_eq, show cv (0, 0, true) = fun _ => true by decide]

theorem ψ_eq_one_iff (x : Fin 8 × Fin 8 × Bool) : ψ x = 1 ↔ x = (0, 0, false) := by
  constructor
  · intro h; exact ψ_injective (h.trans ψ_zero.symm)
  · rintro rfl; exact ψ_zero

theorem ψ_sq_eq_one_iff (x : Fin 8 × Fin 8 × Bool) :
    ψ x ^ 2 = 1 ↔ sqv x = fun _ => false := by
  rw [ψ_sq, ← act_zero_zero, act_eq_iff]; simp

theorem orderOf_ψ_two (x : Fin 8 × Fin 8 × Bool) :
    orderOf (ψ x) = 2 ↔ (sqv x = fun _ => false) ∧ x ≠ (0, 0, false) := by
  rw [orderOf_eq_prime_iff, ψ_sq_eq_one_iff, Ne, ψ_eq_one_iff]

theorem orderOf_ψ_four (x : Fin 8 × Fin 8 × Bool) :
    orderOf (ψ x) = 4 ↔ ¬ (sqv x = fun _ => false) := by
  rw [← ψ_sq_eq_one_iff]
  constructor
  · intro h h2
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h] at this
    exact absurd this (by decide)
  · intro h
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := ψ x) (by rwa [pow_one])
      (by exact act_pow_four _ _)
    simpa using this

/-- (d) `G` has exactly 71 elements of order 2. -/
theorem card_order_two : Nat.card {g : G // orderOf g = 2} = 71 := by
  have e := eqv.subtypeEquiv (p := fun x => (sqv x = fun _ => false) ∧ x ≠ (0, 0, false))
    (q := fun g : G => orderOf g = 2)
    (fun x => by rw [← Subgroup.orderOf_coe, coe_eqv, orderOf_ψ_two])
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

/-- (d) `G` has exactly 56 elements of order 4. -/
theorem card_order_four : Nat.card {g : G // orderOf g = 4} = 56 := by
  have e := eqv.subtypeEquiv (p := fun x => ¬ (sqv x = fun _ => false))
    (q := fun g : G => orderOf g = 4)
    (fun x => by rw [← Subgroup.orderOf_coe, coe_eqv, orderOf_ψ_four])
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel


/-! ## (d) Center and commutator subgroup -/

theorem center_key : ∀ x : Fin 8 × Fin 8 × Bool,
    (∀ n : Fin 8, n ≠ 0 → n ^^^ x.1 = x.1 ^^^ n ∧
      (fun p => sgn n p ^^ cv x (p ^^^ n)) = (fun p => cv x p ^^ sgn n (p ^^^ x.1))) →
    x = (0, 0, false) ∨ x = (0, 0, true) := by
  decide +kernel

theorem flipAll_comm_act (a : Fin 8) (c : Fin 8 → Bool) :
    flipAll * act a c = act a c * flipAll := by
  rw [flipAll_eq, act_mul, act_mul, act_eq_iff]
  refine ⟨by rw [f0x, fx0], ?_⟩
  funext p
  simp only [fx0]
  cases c p <;> rfl

theorem flipAll_mem_G : flipAll ∈ G := ψ_flip ▸ ψ_mem (0, 0, true)

/-- (d) The center of `G` is `{1, flipAll}`. -/
theorem mem_center_G (g : G) :
    g ∈ Subgroup.center G ↔ (g : Equiv.Perm St) = 1 ∨ (g : Equiv.Perm St) = flipAll := by
  obtain ⟨x, hx⟩ := (mem_G_iff g).1 g.2
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hc
    have key : ∀ n : Fin 8, n ≠ 0 → n ^^^ x.1 = x.1 ^^^ n ∧
        (fun p => sgn n p ^^ cv x (p ^^^ n)) = (fun p => cv x p ^^ sgn n (p ^^^ x.1)) := by
      intro n _
      have := congrArg Subtype.val (hc ⟨read n, read_mem_G n⟩)
      change read n * (g : Equiv.Perm St) = (g : Equiv.Perm St) * read n at this
      rw [← hx] at this
      simp only [ψ, read, act_mul, act_eq_iff] at this
      exact this
    rcases center_key x key with h | h
    · left; rw [← hx, h, ψ_zero]
    · right; rw [← hx, h, ψ_flip]
  · rintro (h | h) k
    · apply Subtype.ext
      change (k : Equiv.Perm St) * g = (g : Equiv.Perm St) * k
      rw [h, mul_one, one_mul]
    · apply Subtype.ext
      obtain ⟨y, hy⟩ := (mem_G_iff k).1 k.2
      change (k : Equiv.Perm St) * g = (g : Equiv.Perm St) * k
      rw [h, ← hy, ψ]
      exact (flipAll_comm_act _ _).symm

theorem center_G_eq :
    ((Subgroup.center G).map G.subtype : Set (Equiv.Perm St)) = {1, flipAll} := by
  ext z
  simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_insert_iff,
    Set.mem_singleton_iff, Subgroup.coe_subtype]
  constructor
  · rintro ⟨g, hg, rfl⟩; exact (mem_center_G g).1 hg
  · rintro (rfl | rfl)
    · exact ⟨1, one_mem _, rfl⟩
    · exact ⟨⟨flipAll, flipAll_mem_G⟩, (mem_center_G _).2 (Or.inr rfl), rfl⟩

/-- The subgroup `{1, flipAll}` of `Equiv.Perm St`. -/
def Zc : Subgroup (Equiv.Perm St) where
  carrier := {z | z = 1 ∨ z = flipAll}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro _ _ (rfl | rfl) (rfl | rfl)
    · left; exact one_mul 1
    · right; exact one_mul _
    · right; exact mul_one _
    · left; exact flipAll_mul_self
  inv_mem' := by
    rintro _ (rfl | rfl)
    · left; exact inv_one
    · right; exact flipAll_inv

def W0 (a b : Fin 8) : Bool := sgn a 0 ^^ sgn a (0 ^^^ b) ^^ sgn b 0 ^^ sgn b (0 ^^^ a)

theorem W_const : ∀ a b p : Fin 8,
    (sgn a p ^^ sgn a (p ^^^ b) ^^ sgn b p ^^ sgn b (p ^^^ a)) = W0 a b := by
  decide +kernel

def κ (x y : Fin 8 × Fin 8 × Bool) : Bool := W0 x.1 y.1 ^^ dot x.2.1 y.1 ^^ dot y.2.1 x.1

theorem comm_formula (x y : Fin 8 × Fin 8 × Bool) :
    ψ x * ψ y = act 0 (fun _ => κ x y) * (ψ y * ψ x) := by
  obtain ⟨a, u, β⟩ := x
  obtain ⟨b, v, γ⟩ := y
  simp only [ψ, cv, act_mul, act_eq_iff]
  refine ⟨by rw [f0x, fcomm], ?_⟩
  funext p
  simp only [κ, rmw, fx0, dot_shift, ← W_const a b p]
  generalize sgn a p = A1
  generalize sgn b (p ^^^ a) = A2
  generalize sgn b p = A3
  generalize sgn a (p ^^^ b) = A4
  generalize dot u p = D1
  generalize dot v p = D2
  generalize dot u b = D3
  generalize dot v a = D4
  revert A1 A2 A3 A4 D1 D2 D3 D4 β γ
  decide

theorem comm_mem_Zc (x y : Fin 8 × Fin 8 × Bool) : ⁅ψ x, ψ y⁆ ∈ Zc := by
  rw [commutatorElement_def, comm_formula x y]
  generalize κ x y = k
  cases k
  · left; rw [act_zero_zero]; group
  · right; rw [← flipAll_eq]; group

theorem commutator_read_one_two : ⁅read 1, read 2⁆ = flipAll := by
  rw [commutatorElement_def, read_anticomm 1 2 (by decide) (by decide) (by decide)]
  group

/-- (d) The commutator subgroup `⁅G, G⁆` (inside `Equiv.Perm St`) is `{1, flipAll}`. -/
theorem mem_commutator_G (z : Equiv.Perm St) : z ∈ ⁅G, G⁆ ↔ z = 1 ∨ z = flipAll := by
  constructor
  · intro hz
    have hle : ⁅G, G⁆ ≤ Zc := by
      rw [Subgroup.commutator_le]
      intro g1 h1 g2 h2
      obtain ⟨x, rfl⟩ := (mem_G_iff g1).1 h1
      obtain ⟨y, rfl⟩ := (mem_G_iff g2).1 h2
      exact comm_mem_Zc x y
    exact hle hz
  · rintro (rfl | rfl)
    · exact one_mem _
    · rw [← commutator_read_one_two]
      exact Subgroup.commutator_mem_commutator (read_mem_G 1) (read_mem_G 2)

theorem commutator_G_eq :
    ((⁅G, G⁆ : Subgroup (Equiv.Perm St)) : Set (Equiv.Perm St)) = {1, flipAll} := by
  ext z; exact mem_commutator_G z

/-- (d) The derived subgroup `commutator ↥G` of the group `↥G` is `{1, flipAll}`. -/
theorem mem_derived_G (g : G) :
    g ∈ commutator G ↔ (g : Equiv.Perm St) = 1 ∨ (g : Equiv.Perm St) = flipAll := by
  rw [← mem_commutator_G, ← Subgroup.map_subtype_commutator]
  exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective G)).symm

/-! ## (e) Orbits on the 256 states -/

/-- Number of `true` coordinates. -/
def wt (s : St) : ℕ := (Finset.univ.filter fun m => s m = true).card

def par (s : St) : Bool := s 0 ^^ s 1 ^^ s 2 ^^ s 3 ^^ s 4 ^^ s 5 ^^ s 6 ^^ s 7

theorem even_wt_iff_par (s : St) : Even (wt s) ↔ par s = false :=
  forall_st (P := fun s => Even (wt s) ↔ par s = false) (by decide +kernel) s

theorem card_par_false : (Finset.univ.filter fun t : St => par t = false).card = 128 := by
  decide +kernel

/-- There are 128 even-parity states. -/
theorem card_even : {t : St | Even (wt t)}.ncard = 128 := by
  have : {t : St | Even (wt t)} = ↑(Finset.univ.filter fun t : St => par t = false) := by
    ext t; simp [even_wt_iff_par]
  rw [this, Set.ncard_coe_finset, card_par_false]

theorem par_read_tuple : ∀ n : Fin 8, ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    par (read n ![b0, b1, b2, b3, b4, b5, b6, b7]) = par ![b0, b1, b2, b3, b4, b5, b6, b7] := by
  decide +kernel

theorem par_read (n : Fin 8) (s : St) : par (read n s) = par s :=
  forall_st (P := fun s => par (read n s) = par s) (par_read_tuple n) s

theorem par_G {g : Equiv.Perm St} (hg : g ∈ G) (s : St) : par (g s) = par s := by
  unfold G at hg
  induction hg using Subgroup.closure_induction generalizing s with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact par_read _ s
  | one => rfl
  | mul x y _ _ ihx ihy => rw [Equiv.Perm.mul_apply, ihx, ihy]
  | inv x _ ih =>
    have h := ih (x⁻¹ s)
    rw [show x (x⁻¹ s) = s from x.apply_symm_apply s] at h
    exact h.symm

theorem mem_orbit_iff (s t : St) : t ∈ MulAction.orbit G s ↔ ∃ x, ψ x s = t := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨x, hx⟩ := (mem_G_iff g).1 g.2
    exact ⟨x, by rw [hx]; rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨ψ x, ψ_mem x⟩, rfl⟩

theorem sgn_zero' : ∀ p : Fin 8, sgn 0 p = false := by decide

/-- `p ↦ s (p xor a) + s p + sgn a p`. -/
def shiftv (s : St) (a : Fin 8) : Fin 8 → Bool := fun p => s (p ^^^ a) ^^ s p ^^ sgn a p

theorem odd_shift_tuple : ∀ a : Fin 8, ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    par ![b0, b1, b2, b3, b4, b5, b6, b7] = true →
      rmw (rmdecU (shiftv ![b0, b1, b2, b3, b4, b5, b6, b7] a))
          (shiftv ![b0, b1, b2, b3, b4, b5, b6, b7] a 0) =
        shiftv ![b0, b1, b2, b3, b4, b5, b6, b7] a := by
  decide +kernel

theorem even_shift_tuple : ∀ a : Fin 8, a ≠ 0 → ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    par ![b0, b1, b2, b3, b4, b5, b6, b7] = false →
      rmw (rmdecU (shiftv ![b0, b1, b2, b3, b4, b5, b6, b7] a))
          (shiftv ![b0, b1, b2, b3, b4, b5, b6, b7] a 0) ≠
        shiftv ![b0, b1, b2, b3, b4, b5, b6, b7] a := by
  decide +kernel

theorem odd_shift (s : St) (hs : par s = true) (a : Fin 8) : InRM (shiftv s a) :=
  (InRM_iff_dec _).2 (forall_st (P := fun s => par s = true →
    rmw (rmdecU (shiftv s a)) (shiftv s a 0) = shiftv s a) (odd_shift_tuple a) s hs)

theorem even_shift (s : St) (hs : par s = false) (a : Fin 8) (ha : a ≠ 0) :
    ¬ InRM (shiftv s a) := by
  rw [InRM_iff_dec]
  exact forall_st (P := fun s => par s = false →
    rmw (rmdecU (shiftv s a)) (shiftv s a 0) ≠ shiftv s a) (even_shift_tuple a ha) s hs

theorem mem_orbit_of_xor (s t : St) (h : InRM (fun m => s m ^^ t m)) :
    t ∈ MulAction.orbit G s := by
  obtain ⟨u, b, hub⟩ := h
  rw [mem_orbit_iff]
  refine ⟨(0, u, b), ?_⟩
  funext p
  have h1 : rmw u b p = (s p ^^ t p) := congrFun hub p
  show (s (p ^^^ 0) ^^ (sgn 0 p ^^ rmw u b p)) = t p
  rw [fx0, h1, sgn_zero']
  cases s p <;> cases t p <;> rfl

theorem xor_of_mem_orbit (s t : St) (hs : par s = true) (h : t ∈ MulAction.orbit G s) :
    InRM (fun m => s m ^^ t m) := by
  obtain ⟨⟨a, u, b⟩, rfl⟩ := (mem_orbit_iff s t).1 h
  refine ((odd_shift s hs a).xor ⟨u, b, rfl⟩).congr ?_
  funext p
  show ((s (p ^^^ a) ^^ s p ^^ sgn a p) ^^ rmw u b p) =
    (s p ^^ (s (p ^^^ a) ^^ (sgn a p ^^ rmw u b p)))
  cases s (p ^^^ a) <;> cases s p <;> cases sgn a p <;> cases rmw u b p <;> rfl

theorem par_of_not_even {s : St} (hs : ¬ Even (wt s)) : par s = true := by
  rw [even_wt_iff_par] at hs; simpa using hs

/-- (e) For an odd state `s`: `t ∈ orbit(s)` iff `s xor t ∈ RM(1,3)`. -/
theorem odd_orbit_iff (s t : St) (hs : ¬ Even (wt s)) :
    t ∈ MulAction.orbit G s ↔ (fun m => s m ^^ t m) ∈ RM13 := by
  rw [mem_RM13]
  exact ⟨xor_of_mem_orbit s t (par_of_not_even hs), mem_orbit_of_xor s t⟩

theorem odd_orbit_eq (s : St) (hs : ¬ Even (wt s)) :
    MulAction.orbit G s = Set.range (fun y : Fin 8 × Bool => fun m => s m ^^ rmw y.1 y.2 m) := by
  ext t
  rw [odd_orbit_iff s t hs, mem_RM13]
  constructor
  · rintro ⟨u, b, h⟩
    refine ⟨(u, b), ?_⟩
    funext m
    show (s m ^^ rmw u b m) = t m
    rw [show rmw u b m = (s m ^^ t m) from congrFun h m]
    cases s m <;> cases t m <;> rfl
  · rintro ⟨⟨u, b⟩, rfl⟩
    refine ⟨u, b, ?_⟩
    funext m
    show rmw u b m = (s m ^^ (s m ^^ rmw u b m))
    cases s m <;> cases rmw u b m <;> rfl

theorem card_orbit_mul_stab (s : St) :
    Nat.card (MulAction.orbit G s) * Nat.card (MulAction.stabilizer G s) = 128 := by
  rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G s), card_G]

/-- (e) Each odd orbit has 16 elements and each odd stabilizer has 8 elements. -/
theorem odd_orbit_card (s : St) (hs : ¬ Even (wt s)) :
    Nat.card (MulAction.orbit G s) = 16 ∧ Nat.card (MulAction.stabilizer G s) = 8 := by
  have h16 : Nat.card (MulAction.orbit G s) = 16 := by
    rw [odd_orbit_eq s hs, Nat.card_range_of_injective, Nat.card_eq_fintype_card]
    · rfl
    · rintro ⟨u, b⟩ ⟨u', b'⟩ h
      have : rmw u b = rmw u' b' := by
        funext m
        have := congrFun h m
        simpa using this
      obtain ⟨rfl, rfl⟩ := rmw_inj _ _ _ _ this
      rfl
  refine ⟨h16, ?_⟩
  have := card_orbit_mul_stab s
  rw [h16] at this
  omega

/-- (e) The stabilizer of an even state is trivial. -/
theorem even_stab_trivial (s : St) (hs : Even (wt s)) : MulAction.stabilizer G s = ⊥ := by
  have hs' : par s = false := (even_wt_iff_par s).1 hs
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg
  obtain ⟨⟨a, u, b⟩, hx⟩ := (mem_G_iff g).1 g.2
  have hfix : ψ (a, u, b) s = s := by rw [hx]; exact hg
  have hsh : shiftv s a = rmw u b := by
    funext p
    have := congrFun hfix p
    change (s (p ^^^ a) ^^ (sgn a p ^^ rmw u b p)) = s p at this
    show (s (p ^^^ a) ^^ s p ^^ sgn a p) = rmw u b p
    revert this
    cases s (p ^^^ a) <;> cases s p <;> cases sgn a p <;> cases rmw u b p <;> decide
  by_cases ha : a = 0
  · subst ha
    have h0 : rmw u b = rmw 0 false := by
      rw [← hsh]; funext p; simp [shiftv, sgn_zero', rmw, dot_zero]
    obtain ⟨rfl, rfl⟩ := rmw_inj _ _ _ _ h0
    apply Subtype.ext
    rw [← hx, ψ_zero]
    rfl
  · exact absurd ⟨u, b, hsh.symm⟩ (even_shift s hs' a ha)

theorem even_orbit_subset (s : St) (hs : Even (wt s)) :
    MulAction.orbit G s ⊆ {t | Even (wt t)} := by
  rintro t ht
  obtain ⟨x, rfl⟩ := (mem_orbit_iff s t).1 ht
  show Even (wt (ψ x s))
  rw [even_wt_iff_par, par_G (ψ_mem x)]
  exact (even_wt_iff_par s).1 hs

/-- (e) The 128 even states form a single orbit, and the action on it is regular
(trivial stabilizers). -/
theorem even_orbit (s : St) (hs : Even (wt s)) :
    MulAction.orbit G s = {t | Even (wt t)} ∧ MulAction.stabilizer G s = ⊥ := by
  have hstab := even_stab_trivial s hs
  refine ⟨?_, hstab⟩
  have h128 : Nat.card (MulAction.orbit G s) = 128 := by
    have := card_orbit_mul_stab s
    rw [hstab, Subgroup.card_bot, mul_one] at this
    exact this
  apply Set.eq_of_subset_of_ncard_le (even_orbit_subset s hs)
  rw [← Nat.card_coe_set_eq (MulAction.orbit G s), h128, card_even]

/-- (e) Regularity on the even states: for even `s t` there is exactly one `g ∈ G`
with `g • s = t`. -/
theorem even_regular (s t : St) (hs : Even (wt s)) (ht : Even (wt t)) :
    ∃! g : G, g • s = t := by
  obtain ⟨horb, hstab⟩ := even_orbit s hs
  have : t ∈ MulAction.orbit G s := by rw [horb]; exact ht
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 this
  refine ⟨g, hg, fun h hh => ?_⟩
  have : g⁻¹ * h ∈ MulAction.stabilizer G s := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hh, ← hg, inv_smul_smul]
  rw [hstab, Subgroup.mem_bot] at this
  exact (inv_mul_eq_one.1 this).symm

/-- The single-defect state with its unique `false` at coordinate `m`. -/
def δ (m : Fin 8) : St := fun p => decide (p ≠ m)

/-- A state with exactly one `false` coordinate. -/
def SingleDefect (t : St) : Prop := (Finset.univ.filter fun m => t m = false).card = 1

instance : DecidablePred SingleDefect := fun t =>
  inferInstanceAs (Decidable ((Finset.univ.filter fun m => t m = false).card = 1))

theorem singleDefect_iff (t : St) : SingleDefect t ↔ ∃ m, t = δ m :=
  forall_st (P := fun t => SingleDefect t ↔ ∃ m, t = δ m) (by decide +kernel) t

theorem par_δ : ∀ m, par (δ m) = true := by decide

theorem not_even_δ (m : Fin 8) : ¬ Even (wt (δ m)) := by
  rw [even_wt_iff_par, par_δ]; decide

theorem defect_exists_tuple : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    par ![b0, b1, b2, b3, b4, b5, b6, b7] = true → ∃ m : Fin 8,
      rmw (rmdecU (fun p => ![b0, b1, b2, b3, b4, b5, b6, b7] p ^^ δ m p))
          ((fun p => ![b0, b1, b2, b3, b4, b5, b6, b7] p ^^ δ m p) 0) =
        (fun p => ![b0, b1, b2, b3, b4, b5, b6, b7] p ^^ δ m p) := by
  decide +kernel

theorem defect_exists (s : St) (hs : par s = true) : ∃ m, InRM (fun p => s p ^^ δ m p) := by
  obtain ⟨m, hm⟩ := forall_st (P := fun s => par s = true → ∃ m : Fin 8,
      rmw (rmdecU (fun p => s p ^^ δ m p)) ((fun p => s p ^^ δ m p) 0) =
        (fun p => s p ^^ δ m p)) defect_exists_tuple s hs
  exact ⟨m, (InRM_iff_dec _).2 hm⟩

theorem defect_sep : ∀ m m' : Fin 8, InRM (fun p => δ m p ^^ δ m' p) → m = m' := by
  decide +kernel

theorem xor_trans {s t t' : St} (h : InRM (fun p => s p ^^ t p))
    (h' : InRM (fun p => s p ^^ t' p)) : InRM (fun p => t p ^^ t' p) := by
  refine (h.xor h').congr ?_
  funext p
  cases s p <;> cases t p <;> cases t' p <;> rfl

/-- (e) Each odd orbit contains exactly one single-defect state. -/
theorem odd_orbit_single_defect (s : St) (hs : ¬ Even (wt s)) :
    ∃! t, t ∈ MulAction.orbit G s ∧ SingleDefect t := by
  obtain ⟨m, hm⟩ := defect_exists s (par_of_not_even hs)
  refine ⟨δ m, ⟨mem_orbit_of_xor s _ hm, (singleDefect_iff _).2 ⟨m, rfl⟩⟩, ?_⟩
  rintro t ⟨ht, hdt⟩
  obtain ⟨m', rfl⟩ := (singleDefect_iff t).1 hdt
  have h' := xor_of_mem_orbit s _ (par_of_not_even hs) ht
  rw [defect_sep m' m (xor_trans h' hm)]

/-- (e) The odd states fall into exactly 8 orbits. -/
theorem card_odd_orbits :
    {O : Set St | ∃ s, ¬ Even (wt s) ∧ O = MulAction.orbit G s}.ncard = 8 := by
  have hset : {O : Set St | ∃ s, ¬ Even (wt s) ∧ O = MulAction.orbit G s} =
      Set.range (fun m : Fin 8 => MulAction.orbit G (δ m)) := by
    ext O
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨m, hm⟩ := defect_exists s (par_of_not_even hs)
      refine ⟨m, ?_⟩
      rw [MulAction.orbit_eq_iff]
      apply mem_orbit_of_xor
      refine hm.congr ?_
      funext p
      cases s p <;> cases δ m p <;> rfl
    · rintro ⟨m, rfl⟩
      exact ⟨δ m, not_even_δ m, rfl⟩
  rw [hset, Set.ncard_range_of_injective]
  · rw [Nat.card_eq_fintype_card]; rfl
  · intro m m' h
    have hm : δ m ∈ MulAction.orbit G (δ m') := by
      rw [← MulAction.orbit_eq_iff]; exact h
    exact (defect_sep m' m (xor_of_mem_orbit _ _ (par_δ m') hm)).symm

end Bridge4A
