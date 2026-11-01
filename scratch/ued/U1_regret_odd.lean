import Mathlib

/-!
# U1: Regret is the odd part between copies

Statements are identical to `U1_regret_odd.statements.lean`; only the placeholder proofs have been
filled in. The 11 original statements are unchanged. The second (adversarial) agent appended
section (5) and the non-vacuity example (N) to both files.

## Proved (machine-checked)
* (1) `regret U a p e = -regret U p a e`.
* (2) `regret U p p e = 0`; hence every environment is a maximizer of
  `e ↦ regret U p p e` (`IsMaxOn` on `Set.univ`, and the finite argmax filter is `univ`).
* (3) With `σ = Prod.swap`: `regretPair U e ∘ σ = -regretPair U e`; the even part
  `(f + f ∘ σ)/2` of regret is `0`; regret equals its odd part; and for finite `Pol`,
  every `σ`-symmetric `g` satisfies `∑ x, g x * regretPair U e x = 0`.
* (4) Copies sharing policy *and* seed have realized regret `0`. With one policy and
  two seeds (`seedU`), realized regret is `1 ≠ 0`.
* (N) Non-vacuity of (3): for `boolU` (two policies), `regretPair boolU () ≠ 0`.
* (5) Going up: regret satisfies the cocycle law `R(a,b) + R(b,c) = R(a,c)`. For nonempty
  `Pol`, a function `f` on pairs has the form `f (a,p) = u a - u p` iff it satisfies that
  law (`isRegret_iff_cocycle`). The cocycle law implies oddness (`cocycle_odd`).
  Rock-paper-scissors on `Fin 3` is odd (`rps_odd`) but is not a regret
  (`rps_not_regret`). So oddness under `σ` is necessary for being a regret, not sufficient.

## Interpreted (not proved; reading of the theorems)
* "A designer maximizing regret against identical copies is indifferent" means the
  objective is the constant `0`, so it carries no signal about which environment to pick.
  Nothing here models a designer's learning dynamics, tie-breaking, or a UED training loop.
* "Regret is the odd part" is the `σ`-parity decomposition of functions on `Pol × Pol`.
  Orthogonality uses the counting inner product on finite `Pol × Pol`. The theorems do
  not claim this is the only natural inner product.
* (4) says only that sharing a policy does not zero out *realized* regret when the seeds
  differ. Expected regret over i.i.d. seeds is not addressed here.
* (5) In discrete-Hodge terms, odd functions on pairs are edge flows on the complete
  graph over `Pol`. Regrets are exactly the gradient flows; RPS is a pure cyclic (curl)
  flow. This reading is not proved: no Hodge decomposition is formalised here, only
  "exact ↔ cocycle" and one odd, non-exact witness. One more unproved consequence: a
  regret-style objective between copies can only ever express a transitive score
  difference. An intransitive pairwise payoff is odd but is never a regret.

`Π` is a reserved keyword in Lean, so policies are `Pol` and environments are `Env`.
-/

namespace UED.U1

open BigOperators

variable {Pol Env : Type*}

/-- Regret of antagonist `a` over protagonist `p` in environment `e`. -/
def regret (U : Pol → Env → ℝ) (a p : Pol) (e : Env) : ℝ := U a e - U p e

/-- (1) Antisymmetry. -/
theorem regret_antisymm (U : Pol → Env → ℝ) (a p : Pol) (e : Env) :
    regret U a p e = - regret U p a e := by
  unfold regret; ring

/-- (2a) Identical copies have zero regret. -/
theorem regret_self (U : Pol → Env → ℝ) (p : Pol) (e : Env) :
    regret U p p e = 0 := by
  unfold regret; ring

/-- (2b) A designer maximizing regret against identical copies is indifferent: every
environment maximizes `e ↦ regret U p p e` over all environments. -/
theorem identical_copies_every_env_maximizer (U : Pol → Env → ℝ) (p : Pol) (e : Env) :
    IsMaxOn (fun e' => regret U p p e') Set.univ e := by
  intro e' _
  simp [regret_self]

/-- (2c) Same thing, stated as a finite argmax: the argmax set is all of `Finset.univ`. -/
theorem identical_copies_argmax_univ [Fintype Env] (U : Pol → Env → ℝ) (p : Pol) :
    (Finset.univ.filter (fun e => ∀ e', regret U p p e' ≤ regret U p p e)) = Finset.univ := by
  ext e
  simp [regret_self]

/-- Regret as a function on the pair `(antagonist, protagonist)`. -/
def regretPair (U : Pol → Env → ℝ) (e : Env) (x : Pol × Pol) : ℝ := regret U x.1 x.2 e

/-- Even part under the swap involution `σ = Prod.swap`. -/
noncomputable def evenPart {α : Type*} (f : α × α → ℝ) (x : α × α) : ℝ := (f x + f x.swap) / 2

/-- Odd part under the swap involution `σ = Prod.swap`. -/
noncomputable def oddPart {α : Type*} (f : α × α → ℝ) (x : α × α) : ℝ := (f x - f x.swap) / 2

/-- (3a) Curie form: `R ∘ σ = -R`. -/
theorem regretPair_comp_swap (U : Pol → Env → ℝ) (e : Env) :
    regretPair U e ∘ Prod.swap = -regretPair U e := by
  funext x
  simp [regretPair, regret]

/-- (3b) The even part of regret under `σ` is zero. -/
theorem evenPart_regretPair (U : Pol → Env → ℝ) (e : Env) :
    evenPart (regretPair U e) = 0 := by
  funext x
  simp only [evenPart, regretPair, regret, Prod.fst_swap, Prod.snd_swap, Pi.zero_apply]
  ring

/-- (3c) Regret equals its own odd part. -/
theorem oddPart_regretPair (U : Pol → Env → ℝ) (e : Env) :
    oddPart (regretPair U e) = regretPair U e := by
  funext x
  simp only [oddPart, regretPair, regret, Prod.fst_swap, Prod.snd_swap]
  ring

/-- (3d) Orthogonality: any `σ`-symmetric `g` on `Pol × Pol` is orthogonal to regret
in the counting inner product `∑ x, g x * R x`. -/
theorem symmetric_orthogonal_regret [Fintype Pol] (U : Pol → Env → ℝ) (e : Env)
    (g : Pol × Pol → ℝ) (hg : ∀ x, g x.swap = g x) :
    ∑ x, g x * regretPair U e x = 0 := by
  set S := ∑ x, g x * regretPair U e x with hS
  have hswap : S = ∑ x : Pol × Pol, g x.swap * regretPair U e x.swap :=
    (Fintype.sum_equiv (Equiv.prodComm Pol Pol) _ _ (fun x => rfl)).symm
  have hneg : S = -S := by
    calc S = ∑ x : Pol × Pol, g x.swap * regretPair U e x.swap := hswap
      _ = ∑ x : Pol × Pol, -(g x * regretPair U e x) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [hg x]
          simp only [regretPair, regret, Prod.fst_swap, Prod.snd_swap]
          ring
      _ = -S := by rw [Finset.sum_neg_distrib]
  linarith

/-- Realized regret when outcomes depend on (policy, seed): antagonist `(a, s)` against
protagonist `(p, t)`. -/
def realizedRegret {Seed : Type*} (U : Pol → Seed → Env → ℝ)
    (a : Pol) (s : Seed) (p : Pol) (t : Seed) (e : Env) : ℝ := U a s e - U p t e

/-- (4a) Copies sharing both policy and seed have realized regret zero. -/
theorem realizedRegret_shared_seed {Seed : Type*} (U : Pol → Seed → Env → ℝ)
    (p : Pol) (s : Seed) (e : Env) :
    realizedRegret U p s p s e = 0 := by
  unfold realizedRegret; ring

/-- Concrete witness for (4b): one policy, one environment, two seeds; the outcome is
`1` on seed `true` and `0` on seed `false`. -/
def seedU : Unit → Bool → Unit → ℝ := fun _ s _ => if s then 1 else 0

/-- (4b) Same policy, different seeds: realized regret is `1`, so not zero. -/
theorem realizedRegret_diff_seed_example :
    realizedRegret seedU () true () false () = 1 := by
  simp [realizedRegret, seedU]

/-- (4b') Existential form: some outcome function has nonzero realized regret between
two copies that share the policy but not the seed. -/
theorem exists_nonzero_realizedRegret_same_policy :
    ∃ (U : Unit → Bool → Unit → ℝ) (p : Unit) (s t : Bool) (e : Unit),
      realizedRegret U p s p t e ≠ 0 := by
  refine ⟨seedU, (), true, false, (), ?_⟩
  rw [realizedRegret_diff_seed_example]
  norm_num


/-! ## Adversarial additions (second agent)

Non-vacuity of (3), and one step *up*: regret is not merely odd under `σ`, it is
*exact* (a coboundary `u a - u p`), and exactness is characterised by the cocycle law.
Rock-paper-scissors shows oddness is strictly weaker than exactness. -/

/-- Two-policy outcome table used for non-vacuity: policy `true` scores `1`, `false` scores `0`. -/
def boolU : Bool → Unit → ℝ := fun a _ => if a then 1 else 0

/-- (N) Non-vacuity of (3): the odd function `regretPair` is not identically zero, so
"regret lies in the odd part" is not the trivial statement `R = 0`. -/
theorem regretPair_ne_zero_example : regretPair boolU () ≠ 0 := by
  intro h
  have := congrFun h (true, false)
  simp [regretPair, regret, boolU] at this

/-- (5a) Cocycle (transitivity) law of regret: `R(a,b) + R(b,c) = R(a,c)`. -/
theorem regret_cocycle (U : Pol → Env → ℝ) (a b c : Pol) (e : Env) :
    regret U a b e + regret U b c e = regret U a c e := by
  unfold regret; ring

/-- (5b) **Going up: exactness characterisation.** For a nonempty policy type, a function
`f` on pairs is a regret, i.e. `f (a,p) = u a - u p` for some score `u`, if and only if it
satisfies the cocycle law. (Cocycle implies oddness, see `cocycle_odd`. The converse
fails; see `rps_odd` and `rps_not_regret`.) -/
theorem isRegret_iff_cocycle [Nonempty Pol] (f : Pol × Pol → ℝ) :
    (∃ u : Pol → ℝ, ∀ a p, f (a, p) = u a - u p) ↔
      ∀ a b c, f (a, b) + f (b, c) = f (a, c) := by
  constructor
  · rintro ⟨u, hu⟩ a b c
    rw [hu, hu, hu]; ring
  · intro h
    obtain ⟨o⟩ := ‹Nonempty Pol›
    refine ⟨fun a => f (a, o), fun a p => ?_⟩
    have := h a p o
    linarith

/-- (5c) The cocycle law forces oddness under `σ`. -/
theorem cocycle_odd (f : Pol × Pol → ℝ) (h : ∀ a b c, f (a, b) + f (b, c) = f (a, c)) :
    f ∘ Prod.swap = -f := by
  funext x
  have h0 : f (x.1, x.1) = 0 := by have := h x.1 x.1 x.1; linarith
  have := h x.1 x.2 x.1
  simp only [Function.comp, Prod.swap, Pi.neg_apply]
  linarith

/-- Rock-paper-scissors payoff on `Fin 3`: `+1` if `b = a + 1`, `-1` if `a = b + 1`, else `0`. -/
def rps (x : Fin 3 × Fin 3) : ℝ :=
  if x.2 = x.1 + 1 then 1 else if x.1 = x.2 + 1 then -1 else 0

/-- (5d) Rock-paper-scissors is odd under `σ`. -/
theorem rps_odd : rps ∘ Prod.swap = -rps := by
  funext x
  obtain ⟨a, b⟩ := x
  fin_cases a <;> fin_cases b <;> simp [rps]

/-- (5e) ...but rock-paper-scissors is not a regret of any score `u`: oddness is strictly
weaker than being a regret. -/
theorem rps_not_regret : ¬ ∃ u : Fin 3 → ℝ, ∀ a p, rps (a, p) = u a - u p := by
  rw [isRegret_iff_cocycle]
  intro h
  have := h 0 1 2
  simp [rps] at this
  norm_num at this
end UED.U1
