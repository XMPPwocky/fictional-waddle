import Mathlib

/-!
# Faithful sum-encodings of tic-tac-toe need 10 symbols; with exactly 10 they are the Lo Shu mod 10

`lo`, `lines`, `inLine`, `isLine`, `rot` are copied verbatim from `scratch/sidechannel/LoShu.lean`.
That file does not define `Faithful`, `Magic` or `D4`; they are defined here as follows.
* `Magic g t`: every line (three distinct cells with `isLine`) has label sum `t`.
* `Faithful g t`: for three distinct cells, `isLine` holds iff the label sum is `t`.
* `D4`: the eight maps `rot^i` and `rot^i ∘ refl` (`i < 4`), `refl = ![2,1,0,5,4,3,8,7,6]`.

PROVED:
* `faithful_injective` (a): in any `AddCommGroup`, `Faithful g t → Injective g`.
* `magic_faithful_iff_injective_rat` (b): over `ℚ`, `Magic g t → (Faithful g t ↔ Injective g)`
  (`magic_faithful_iff_injective` proves it over any field of characteristic zero).
* `not_faithful_of_card_lt_ten` (c): in a finite `AddCommGroup` with fewer than 10 elements
  no `(g, t)` is faithful.
* `faithful_zmod10_iff` (d): over `ZMod 10`, `Faithful g t` iff
  `(g, t) = (fun x => (lo (σ x) : ZMod 10) + k, 15 + 3 * k)` for some `σ ∈ D4`, `k : ZMod 10`.
* `card_faithful_zmod10` (d): there are exactly 80 faithful pairs over `ZMod 10`.
* Auxiliary: `magic_param` (every magic labelling over an `AddCommGroup` is
  `g 4 + cu x • u + cv x • v` with `t = 3 • g 4`), `faithful_translate`.

INTERPRETED (not formalized): "needs 10 symbols" is read as (c), a statement about the
cardinality of the target group; the encodings are maps `Fin 9 → G` into an abelian group.
-/

namespace Bridge1B

def lo : Fin 9 → ℕ := ![4, 9, 2, 3, 5, 7, 8, 1, 6]

def lines : List (ℕ × ℕ × ℕ) :=
  [(0, 1, 2), (3, 4, 5), (6, 7, 8), (0, 3, 6), (1, 4, 7), (2, 5, 8), (0, 4, 8), (2, 4, 6)]

def inLine (l : ℕ × ℕ × ℕ) (x : ℕ) : Bool := x == l.1 || x == l.2.1 || x == l.2.2

def isLine (a b c : Fin 9) : Bool :=
  lines.any fun l => inLine l a.val && inLine l b.val && inLine l c.val

def rot : Fin 9 → Fin 9 := ![2, 5, 8, 1, 4, 7, 0, 3, 6]

def refl : Fin 9 → Fin 9 := ![2, 1, 0, 5, 4, 3, 8, 7, 6]

def D4 : Finset (Fin 9 → Fin 9) :=
  {id, rot, rot ∘ rot, rot ∘ rot ∘ rot, refl, rot ∘ refl, rot ∘ rot ∘ refl, rot ∘ rot ∘ rot ∘ refl}

section Defs
variable {G : Type*} [AddCommGroup G]

def Magic (g : Fin 9 → G) (t : G) : Prop :=
  ∀ a b c : Fin 9, a ≠ b → b ≠ c → a ≠ c → isLine a b c = true → g a + g b + g c = t

def Faithful (g : Fin 9 → G) (t : G) : Prop :=
  ∀ a b c : Fin 9, a ≠ b → b ≠ c → a ≠ c → (isLine a b c = true ↔ g a + g b + g c = t)

instance [DecidableEq G] (g : Fin 9 → G) (t : G) : Decidable (Faithful g t) := by
  unfold Faithful; infer_instance

/-- Coefficients of the general magic labelling `g 4 + cu x • u + cv x • v`. -/
def cu : Fin 9 → ℤ := ![1, -1, 0, -1, 0, 1, 0, 1, -1]
def cv : Fin 9 → ℤ := ![0, -1, 1, 1, 0, -1, -1, 1, 0]

def H (u v : G) (x : Fin 9) : G := cu x • u + cv x • v

end Defs

section General
variable {G : Type*} [AddCommGroup G]

theorem Faithful.magic {g : Fin 9 → G} {t : G} (hF : Faithful g t) : Magic g t :=
  fun a b c hab hbc hac hl => (hF a b c hab hbc hac).1 hl

lemma escape : ∀ a b : Fin 9, a ≠ b → ∃ c d : Fin 9, a ≠ c ∧ c ≠ d ∧ a ≠ d ∧
    isLine a c d = true ∧ b ≠ c ∧ b ≠ d ∧ isLine b c d = false := by
  decide

/-- (a) A faithful encoding is injective, in any abelian group. -/
theorem faithful_injective {g : Fin 9 → G} {t : G} (hF : Faithful g t) : Function.Injective g := by
  intro a b hg
  by_contra hab
  obtain ⟨c, d, hac, hcd, had, hl, hbc, hbd, hnl⟩ := escape a b hab
  have h1 : g a + g c + g d = t := (hF a c d hac hcd had).1 hl
  rw [hg] at h1
  have h2 := (hF b c d hbc hcd hbd).2 h1
  rw [hnl] at h2
  exact Bool.false_ne_true h2

/-- Every magic labelling is determined by its centre and the two cells `0`, `2`. -/
theorem magic_param {g : Fin 9 → G} {t : G} (hM : Magic g t) :
    t = 3 • g 4 ∧ g = fun x => H (g 0 - g 4) (g 2 - g 4) x + g 4 := by
  have r0 := hM 0 1 2 (by decide) (by decide) (by decide) (by decide)
  have r1 := hM 3 4 5 (by decide) (by decide) (by decide) (by decide)
  have r2 := hM 6 7 8 (by decide) (by decide) (by decide) (by decide)
  have c0 := hM 0 3 6 (by decide) (by decide) (by decide) (by decide)
  have c1 := hM 1 4 7 (by decide) (by decide) (by decide) (by decide)
  have c2 := hM 2 5 8 (by decide) (by decide) (by decide) (by decide)
  have d0 := hM 0 4 8 (by decide) (by decide) (by decide) (by decide)
  have d1 := hM 2 4 6 (by decide) (by decide) (by decide) (by decide)
  have ht : t = 3 • g 4 := by
    linear_combination (norm := module) r0 + r2 - d0 - d1 - c1
  refine ⟨ht, ?_⟩
  have e8 : g 8 = g 4 - (g 0 - g 4) := by linear_combination (norm := module) d0 + ht
  have e6 : g 6 = g 4 - (g 2 - g 4) := by linear_combination (norm := module) d1 + ht
  have e1 : g 1 = g 4 - (g 0 - g 4) - (g 2 - g 4) := by
    linear_combination (norm := module) r0 + ht
  have e7 : g 7 = g 4 + (g 0 - g 4) + (g 2 - g 4) := by
    linear_combination (norm := module) c1 + ht - e1
  have e3 : g 3 = g 4 - (g 0 - g 4) + (g 2 - g 4) := by
    linear_combination (norm := module) c0 + ht - e6
  have e5 : g 5 = g 4 + (g 0 - g 4) - (g 2 - g 4) := by
    linear_combination (norm := module) r1 + ht - e3
  funext x
  fin_cases x <;> simp [H, cu, cv] <;> first
    | (linear_combination (norm := module) e1) | (linear_combination (norm := module) e3)
    | (linear_combination (norm := module) e5) | (linear_combination (norm := module) e6)
    | (linear_combination (norm := module) e7) | (linear_combination (norm := module) e8)

theorem faithful_translate (g : Fin 9 → G) (t k : G) :
    Faithful (fun x => g x + k) (t + 3 • k) ↔ Faithful g t := by
  unfold Faithful
  have key : ∀ a b c : Fin 9, g a + k + (g b + k) + (g c + k) = t + 3 • k ↔ g a + g b + g c = t := by
    intro a b c
    rw [show g a + k + (g b + k) + (g c + k) = (g a + g b + g c) + 3 • k by module]
    exact add_left_inj _
  simp only [key]

theorem magic_faithful_iff_H {g : Fin 9 → G} {t : G} (hM : Magic g t) :
    Faithful g t ↔ Faithful (H (g 0 - g 4) (g 2 - g 4)) 0 := by
  obtain ⟨ht, hg⟩ := magic_param hM
  have := faithful_translate (H (g 0 - g 4) (g 2 - g 4)) 0 (g 4)
  rw [zero_add, ← ht, ← hg] at this
  exact this

end General

section Small

lemma nc05 : ∀ c : Fin 9, c ≠ 0 → c ≠ 5 → isLine 0 5 c = false := by decide
lemma nc07 : ∀ c : Fin 9, c ≠ 0 → c ≠ 7 → isLine 0 7 c = false := by decide
lemma nc23 : ∀ c : Fin 9, c ≠ 2 → c ≠ 3 → isLine 2 3 c = false := by decide
lemma nc27 : ∀ c : Fin 9, c ≠ 2 → c ≠ 7 → isLine 2 7 c = false := by decide

variable {G : Type*} [AddCommGroup G]

lemma pair_constraint {g : Fin 9 → G} {t : G} (hF : Faithful g t) (hs : Function.Surjective g)
    (a b : Fin 9) (hab : a ≠ b) (hnc : ∀ c : Fin 9, c ≠ a → c ≠ b → isLine a b c = false) :
    2 • g a + g b = t ∨ g a + 2 • g b = t := by
  obtain ⟨c, hc⟩ := hs (t - g a - g b)
  by_cases hca : c = a
  · left; subst hca; linear_combination (norm := module) hc
  by_cases hcb : c = b
  · right; subst hcb; linear_combination (norm := module) hc
  exfalso
  have hsum : g a + g b + g c = t := by rw [hc]; abel
  have := (hF a b c hab (Ne.symm hcb) (Ne.symm hca)).2 hsum
  rw [hnc c hca hcb] at this
  exact Bool.false_ne_true this

lemma small_algebra (u v : G) (hu : u ≠ 0) (hv : v ≠ 0) (h9 : ∀ x : G, 9 • x = 0)
    (hA : 3 • u - v = 0 ∨ 3 • u - 2 • v = 0) (hB : 3 • u + v = 0 ∨ 3 • u + 2 • v = 0)
    (hC : 3 • v - u = 0 ∨ 3 • v - 2 • u = 0) (hD : 3 • v + u = 0 ∨ 3 • v + 2 • u = 0) : False := by
  have h3v : 3 • v = 0 := by
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact absurd (by linear_combination (norm := module) h9 v - 4 • (hB - hA)) hv
    · linear_combination (norm := module) hB - hA
    · linear_combination (norm := module) hB - hA
    · exact absurd (by linear_combination (norm := module) h9 v - 2 • (hB - hA)) hv
  have h3u : 3 • u = 0 := by
    rcases hC with hC | hC <;> rcases hD with hD | hD
    · exact absurd (by linear_combination (norm := module) h9 u - 4 • (hD - hC)) hu
    · linear_combination (norm := module) hD - hC
    · linear_combination (norm := module) hD - hC
    · exact absurd (by linear_combination (norm := module) h9 u - 2 • (hD - hC)) hu
  rcases hA with hA | hA
  · exact hv (by linear_combination (norm := module) h3u - hA)
  · exact hv (by linear_combination (norm := module) h9 v - 4 • (h3u - hA))

/-- (c) No faithful encoding into a finite abelian group with fewer than 10 elements. -/
theorem not_faithful_of_card_lt_ten [Fintype G] (hG : Fintype.card G < 10)
    (g : Fin 9 → G) (t : G) : ¬ Faithful g t := by
  intro hF
  have hinj := faithful_injective hF
  have hle : 9 ≤ Fintype.card G := by
    simpa using Fintype.card_le_of_injective g hinj
  have hcard : Fintype.card (Fin 9) = Fintype.card G := by simp; omega
  have hs : Function.Surjective g :=
    ((Fintype.bijective_iff_injective_and_card g).2 ⟨hinj, hcard⟩).2
  have h9 : ∀ x : G, 9 • x = 0 := by
    intro x
    have := card_nsmul_eq_zero (G := G) (x := x)
    rwa [← hcard, Fintype.card_fin] at this
  obtain ⟨ht, hg⟩ := magic_param hF.magic
  have e3 : g 3 = g 4 - (g 0 - g 4) + (g 2 - g 4) := by
    conv_lhs => rw [hg]
    simp [H, cu, cv]; module
  have e5 : g 5 = g 4 + (g 0 - g 4) - (g 2 - g 4) := by
    conv_lhs => rw [hg]
    simp [H, cu, cv]; module
  have e7 : g 7 = g 4 + (g 0 - g 4) + (g 2 - g 4) := by
    conv_lhs => rw [hg]
    simp [H, cu, cv]; module
  have hA := pair_constraint hF hs 0 5 (by decide) nc05
  have hB := pair_constraint hF hs 0 7 (by decide) nc07
  have hC := pair_constraint hF hs 2 3 (by decide) nc23
  have hD := pair_constraint hF hs 2 7 (by decide) nc27
  rw [e5, ht] at hA
  rw [e7, ht] at hB hD
  rw [e3, ht] at hC
  have hu : g 0 - g 4 ≠ 0 := sub_ne_zero.2 (fun h => absurd (hinj h) (by decide))
  have hv : g 2 - g 4 ≠ 0 := sub_ne_zero.2 (fun h => absurd (hinj h) (by decide))
  refine small_algebra (g 0 - g 4) (g 2 - g 4) hu hv h9 ?_ ?_ ?_ ?_
  · rcases hA with h | h
    · left; linear_combination (norm := module) h
    · right; linear_combination (norm := module) h
  · rcases hB with h | h
    · left; linear_combination (norm := module) h
    · right; linear_combination (norm := module) h
  · rcases hC with h | h
    · left; linear_combination (norm := module) h
    · right; linear_combination (norm := module) h
  · rcases hD with h | h
    · left; linear_combination (norm := module) h
    · right; linear_combination (norm := module) h

end Small

section CharZero

lemma table_line : ∀ a b c : Fin 9, a ≠ b → b ≠ c → a ≠ c → isLine a b c = true →
    cu a + cu b + cu c = 0 ∧ cv a + cv b + cv c = 0 := by
  decide

lemma table_nonline : ∀ a b c : Fin 9, a ≠ b → b ≠ c → a ≠ c → isLine a b c = false →
    (cu a + cu b + cu c ≠ 0 ∨ cv a + cv b + cv c ≠ 0) ∧
    ∃ i j : Fin 9, i ≠ j ∧
      (cu i - cu j) * (cv a + cv b + cv c) = (cv i - cv j) * (cu a + cu b + cu c) := by
  intro a; fin_cases a <;> decide +kernel

variable {K : Type*} [Field K]

lemma H_sum (u v : K) (a b c : Fin 9) :
    H u v a + H u v b + H u v c =
      ((cu a + cu b + cu c : ℤ) : K) * u + ((cv a + cv b + cv c : ℤ) : K) * v := by
  simp only [H, zsmul_eq_mul]; push_cast; ring

lemma H_sub (u v : K) (i j : Fin 9) :
    H u v i - H u v j = ((cu i - cu j : ℤ) : K) * u + ((cv i - cv j : ℤ) : K) * v := by
  simp only [H, zsmul_eq_mul]; push_cast; ring

theorem H_faithful_of_injective [CharZero K] (u v : K) (hinj : Function.Injective (H u v)) :
    Faithful (H u v) 0 := by
  intro a b c hab hbc hac
  constructor
  · intro hl
    obtain ⟨hP, hQ⟩ := table_line a b c hab hbc hac hl
    rw [H_sum, hP, hQ]; simp
  · intro hs
    by_contra hnl
    rw [Bool.not_eq_true] at hnl
    obtain ⟨hPQ, i, j, hij, hrel⟩ := table_nonline a b c hab hbc hac hnl
    rw [H_sum] at hs
    set P : ℤ := cu a + cu b + cu c
    set Q : ℤ := cv a + cv b + cv c
    set dP : ℤ := cu i - cu j
    set dQ : ℤ := cv i - cv j
    have hrelK : (dP : K) * Q = (dQ : K) * P := by exact_mod_cast hrel
    have hd : H u v i - H u v j = 0 := by
      rw [H_sub]
      rcases hPQ with hP | hQ
      · have hPK : (P : K) ≠ 0 := by exact_mod_cast hP
        have : (P : K) * ((dP : K) * u + (dQ : K) * v) = 0 := by
          linear_combination (dP : K) * hs - v * hrelK
        exact (mul_eq_zero.1 this).resolve_left hPK
      · have hQK : (Q : K) ≠ 0 := by exact_mod_cast hQ
        have : (Q : K) * ((dP : K) * u + (dQ : K) * v) = 0 := by
          linear_combination (dQ : K) * hs + u * hrelK
        exact (mul_eq_zero.1 this).resolve_left hQK
    exact hij (hinj (sub_eq_zero.1 hd))

/-- (b) Over a field of characteristic zero, a magic labelling is faithful iff injective. -/
theorem magic_faithful_iff_injective [CharZero K] {g : Fin 9 → K} {t : K} (hM : Magic g t) :
    Faithful g t ↔ Function.Injective g := by
  refine ⟨faithful_injective, fun hinj => ?_⟩
  rw [magic_faithful_iff_H hM]
  obtain ⟨_, hg⟩ := magic_param hM
  apply H_faithful_of_injective
  intro x y hxy
  apply hinj
  rw [hg]
  simp only [hxy]

/-- (b) over `ℚ`. -/
theorem magic_faithful_iff_injective_rat {g : Fin 9 → ℚ} {t : ℚ} (hM : Magic g t) :
    Faithful g t ↔ Function.Injective g :=
  magic_faithful_iff_injective hM

end CharZero

section ZMod10

def Hz (u v : ZMod 10) : Fin 9 → ZMod 10 := ![u, -u - v, v, v - u, 0, u - v, -v, u + v, -u]

lemma H_eq_Hz (u v : ZMod 10) : H u v = Hz u v := by
  funext x
  fin_cases x <;> simp [H, Hz, cu, cv] <;> abel

lemma Hz_classify : ∀ u v : ZMod 10,
    Faithful (Hz u v) 0 ↔ ∃ σ ∈ D4, Hz u v = fun x => (lo (σ x) : ZMod 10) - 5 := by
  intro u v
  fin_cases u <;> fin_cases v <;> decide +kernel

lemma D4_forall {P : (Fin 9 → Fin 9) → Prop} : (∀ σ ∈ D4, P σ) ↔
    P id ∧ P rot ∧ P (rot ∘ rot) ∧ P (rot ∘ rot ∘ rot) ∧ P refl ∧ P (rot ∘ refl) ∧
      P (rot ∘ rot ∘ refl) ∧ P (rot ∘ rot ∘ rot ∘ refl) := by
  simp [D4]

lemma loShu_D4_faithful : ∀ σ ∈ D4, Faithful (fun x => (lo (σ x) : ZMod 10)) 15 := by
  rw [D4_forall]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- (d) The faithful pairs over `ZMod 10` are exactly the translated Lo Shu squares under `D4`. -/
theorem faithful_zmod10_iff (g : Fin 9 → ZMod 10) (t : ZMod 10) :
    Faithful g t ↔ ∃ σ ∈ D4, ∃ k : ZMod 10,
      g = (fun x => (lo (σ x) : ZMod 10) + k) ∧ t = 15 + 3 * k := by
  constructor
  · intro hF
    have hM := hF.magic
    obtain ⟨ht, hg⟩ := magic_param hM
    have hH := (magic_faithful_iff_H hM).1 hF
    rw [H_eq_Hz] at hH
    obtain ⟨σ, hσ, hz⟩ := (Hz_classify _ _).1 hH
    refine ⟨σ, hσ, g 4 - 5, ?_, ?_⟩
    · conv_lhs => rw [hg]
      rw [H_eq_Hz, hz]
      funext x
      ring
    · rw [ht, nsmul_eq_mul]
      push_cast
      ring
  · rintro ⟨σ, hσ, k, rfl, rfl⟩
    have := (faithful_translate (fun x => (lo (σ x) : ZMod 10)) 15 k).2 (loShu_D4_faithful σ hσ)
    rwa [nsmul_eq_mul, Nat.cast_ofNat] at this

lemma D4_card : D4.card = 8 := by rfl

lemma D4_center : ∀ σ ∈ D4, σ 4 = 4 := by
  rw [D4_forall]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

lemma D4_lo_inj : ∀ σ ∈ D4, ∀ τ ∈ D4,
    ((fun x => (lo (σ x) : ZMod 10)) = fun x => (lo (τ x) : ZMod 10)) → σ = τ := by
  intro σ hσ τ hτ h
  funext x
  have hx := congrFun h x
  simp only [D4, Finset.mem_insert, Finset.mem_singleton] at hσ hτ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  revert x <;> decide

def enc (p : (Fin 9 → Fin 9) × ZMod 10) : (Fin 9 → ZMod 10) × ZMod 10 :=
  (fun x => (lo (p.1 x) : ZMod 10) + p.2, 15 + 3 * p.2)

/-- (d) There are exactly 80 faithful pairs over `ZMod 10`. -/
theorem card_faithful_zmod10 :
    Fintype.card {p : (Fin 9 → ZMod 10) × ZMod 10 // Faithful p.1 p.2} = 80 := by
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter fun p : (Fin 9 → ZMod 10) × ZMod 10 => Faithful p.1 p.2) =
      (D4 ×ˢ (Finset.univ : Finset (ZMod 10))).image enc := by
    ext ⟨g, t⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_product, enc, Prod.exists, Prod.mk.injEq, faithful_zmod10_iff]
    constructor
    · rintro ⟨σ, hσ, k, hg, ht⟩
      exact ⟨σ, k, ⟨hσ, trivial⟩, hg.symm, ht.symm⟩
    · rintro ⟨σ, k, ⟨hσ, -⟩, hg, ht⟩
      exact ⟨σ, hσ, k, hg.symm, ht.symm⟩
  rw [hset, Finset.card_image_of_injOn, Finset.card_product, D4_card, Finset.card_univ, ZMod.card]
  rintro ⟨σ, k⟩ hσk ⟨τ, l⟩ hτl he
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hσk hτl
  simp only [enc, Prod.mk.injEq] at he
  obtain ⟨hf, -⟩ := he
  have h4 := congrFun hf 4
  simp only [D4_center σ hσk.1, D4_center τ hτl.1] at h4
  have hkl : k = l := add_left_cancel h4
  subst hkl
  have hστ : σ = τ := D4_lo_inj σ hσk.1 τ hτl.1 (by
    funext x
    exact add_right_cancel (congrFun hf x))
  rw [hστ]

end ZMod10

end Bridge1B
