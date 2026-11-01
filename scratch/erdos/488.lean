import Mathlib

/-!
# Erdős problem 488: a counterexample

The statement `erdos_488` (copied from `488.statement.lean`) asks whether, for a finite set
`A` of integers `≥ 2` and `B` the set of positive multiples of elements of `A`, one has
`|B ∩ [1,m]| / m < 2 |B ∩ [1,n]| / n` for all `m > n ≥ max A`.
The theorem `erdos_488_false` below proves the negation of that statement.

Construction. Let `S` be the 53 odd primes below `257`, `Q = ∏ S`, and call `x` good if
`x ≠ 0` and all prime factors of `x` are below `257`. Let `D j` be the odd good numbers in
`[1, 256^j]`. Since `|D j| ≤ (8j+1)^53`, some `k` has `2 |D (k+1)| ≤ 3 |D k|`.
Put `T = 256^k`, `A = {good a : T < a ≤ 256 T}`, `n = 256 T`, `m = 2 T Q`.
* Every multiple of an element of `A` that is at most `n` lies in `A`, and
  `|A| ≤ 8 |D (k+1)| ≤ 12 |D k|`.
* For `d ∈ D k` let `c_d = 2^e d ∈ (T, 2T]`. The products `c_d * r`, with `r < Q` coprime to
  `Q`, are distinct elements of `B ∩ [1, m]`, so `|B ∩ [1,m]| ≥ |D k| * φ(Q)`.
* `3 Q ≤ 16 φ(Q)` (a finite check), which gives `2 m |B ∩ [1,n]| ≤ n |B ∩ [1,m]|`.

This follows the construction posted by Declan Gessel on the erdosproblems.com forum
(proof-claims thread for problem 488); the Lean proof here was written independently.
-/

namespace Erdos488

/-- The original statement, copied verbatim from `488.statement.lean`, as a proposition. -/
def Statement : Prop := ∀ (A : Finset ℕ), A.Nonempty →
    0 ∉ A → 1 ∉ A →
    letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
    ∀ᵉ (n : ℕ) (m > n), A.max ≤ n →
      ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
        2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n

/-- The odd primes below `257`. -/
def S : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251}

/-- `S` has 53 elements. -/
theorem S_card : S.card = 53 := by decide

/-- Every element of `S` is prime. -/
theorem S_prime : ∀ p ∈ S, p.Prime := by
  intro p hp
  fin_cases hp <;> norm_num

/-- Every odd prime below `257` lies in `S`. -/
theorem prime_mem_S {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hlt : p < 257) : p ∈ S := by
  interval_cases p <;> first | exact absurd rfl h2 | decide | (norm_num at hp)

/-- `3 ∏ p ≤ 16 ∏ (p - 1)` over `p ∈ S`. -/
theorem ratio : 3 * ∏ p ∈ S, p ≤ 16 * ∏ p ∈ S, (p - 1) := by decide

/-- `∏ S > 128`. -/
theorem Qbig : 128 < ∏ p ∈ S, p := by decide

set_option exponentiation.threshold 5000 in
/-- The numerical inequality used in the pigeonhole step. -/
theorem growth : 2 ^ 4096 * (8 * 4096 + 1) ^ 53 < 3 ^ 4096 := by norm_num


/-- `x` is nonzero and every prime factor of `x` is less than `257`. -/
def Good (x : ℕ) : Prop := x ≠ 0 ∧ ∀ p, p.Prime → p ∣ x → p < 257

theorem good_mul {x y : ℕ} (hx : Good x) (hy : Good y) : Good (x * y) := by
  refine ⟨Nat.mul_ne_zero hx.1 hy.1, fun p hp hd => ?_⟩
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · exact hx.2 p hp h
  · exact hy.2 p hp h

theorem good_of_lt {c : ℕ} (h1 : 1 ≤ c) (h2 : c < 257) : Good c :=
  ⟨by omega, fun p _ hd => lt_of_le_of_lt (Nat.le_of_dvd (by omega) hd) h2⟩

theorem good_pow {b e : ℕ} (hb : Good b) : Good (b ^ e) := by
  refine ⟨pow_ne_zero _ hb.1, fun p hp hd => hb.2 p hp (hp.dvd_of_dvd_pow hd)⟩

theorem good_of_dvd {x y : ℕ} (hy : Good y) (hxy : x ∣ y) : Good x :=
  ⟨fun h => hy.1 (Nat.eq_zero_of_zero_dvd (h ▸ hxy)),
    fun p hp hd => hy.2 p hp (dvd_trans hd hxy)⟩

theorem mem_S_of_dvd {d p : ℕ} (hodd : Odd d) (hg : Good d) (hp : p.Prime) (hd : p ∣ d) :
    p ∈ S := by
  have h2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hd)
  exact prime_mem_S hp h2 (hg.2 p hp hd)

/-- Odd numbers with prime factors below `257` are determined by their exponents at the
primes in `S`. -/
theorem ext_S {d d' : ℕ} (ho : Odd d) (ho' : Odd d') (hg : Good d) (hg' : Good d')
    (h : ∀ p ∈ S, d.factorization p = d'.factorization p) : d = d' := by
  refine Nat.eq_of_factorization_eq hg.1 hg'.1 (fun p => ?_)
  by_cases hpS : p ∈ S
  · exact h p hpS
  by_cases hp : p.Prime
  · rw [Nat.factorization_eq_zero_of_not_dvd (fun hd => hpS (mem_S_of_dvd ho hg hp hd)),
      Nat.factorization_eq_zero_of_not_dvd (fun hd => hpS (mem_S_of_dvd ho' hg' hp hd))]
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]

open Classical in
/-- Odd numbers in `[1, 256^j]` with all prime factors below `257`. -/
noncomputable def D (j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (256 ^ j)).filter (fun d => Odd d ∧ Good d)

theorem mem_D {j d : ℕ} : d ∈ D j ↔ (1 ≤ d ∧ d ≤ 256 ^ j) ∧ Odd d ∧ Good d := by
  classical
  simp [D, Finset.mem_filter, Finset.mem_Icc]

/-- `|D j| ≤ (8j+1)^53`, via the exponent vector at the primes of `S`. -/
theorem card_D_le (j : ℕ) : (D j).card ≤ (8 * j + 1) ^ 53 := by
  classical
  let t : Finset (S → ℕ) := Fintype.piFinset (fun _ : S => Finset.range (8 * j + 1))
  have ht : t.card = (8 * j + 1) ^ 53 := by
    simp [t, Fintype.card_piFinset, Finset.prod_const, S_card]
  rw [← ht]
  refine Finset.card_le_card_of_injOn (fun d => fun p : S => d.factorization p) ?_ ?_
  · intro d hd
    rw [Finset.mem_coe, mem_D] at hd
    simp only [t, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
    intro p
    have hp := S_prime p.1 p.2
    have h1 : p.1 ^ d.factorization p.1 ≤ d := Nat.ordProj_le p.1 hd.2.2.1
    have h2 : 2 ^ d.factorization p.1 ≤ p.1 ^ d.factorization p.1 :=
      Nat.pow_le_pow_left hp.two_le _
    have h3 : (256 : ℕ) ^ j = 2 ^ (8 * j) := by rw [pow_mul]; norm_num
    have h4 : 2 ^ d.factorization p.1 ≤ 2 ^ (8 * j) := by omega
    have h5 := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 h4
    omega
  · intro d hd d' hd' heq
    rw [Finset.mem_coe, mem_D] at hd hd'
    refine ext_S hd.2.1 hd'.2.1 hd.2.2 hd'.2.2 (fun p hp => ?_)
    exact congrFun heq ⟨p, hp⟩

theorem one_le_card_D_zero : 1 ≤ (D 0).card := by
  refine Finset.card_pos.2 ⟨1, ?_⟩
  rw [mem_D]
  exact ⟨⟨le_refl _, by norm_num⟩, odd_one, good_of_lt le_rfl (by norm_num)⟩

/-- Some `k` satisfies `2 * |D (k+1)| ≤ 3 * |D k|`. -/
theorem exists_slow : ∃ k, 2 * (D (k + 1)).card ≤ 3 * (D k).card := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have key : ∀ j, 3 ^ j ≤ 2 ^ j * (D j).card := by
    intro j
    induction j with
    | zero => simpa using one_le_card_D_zero
    | succ j ih =>
      have := hcon j
      calc 3 ^ (j + 1) = 3 * 3 ^ j := by ring
        _ ≤ 3 * (2 ^ j * (D j).card) := Nat.mul_le_mul_left _ ih
        _ = 2 ^ j * (3 * (D j).card) := by ring
        _ ≤ 2 ^ j * (2 * (D (j + 1)).card) := Nat.mul_le_mul_left _ this.le
        _ = 2 ^ (j + 1) * (D (j + 1)).card := by ring
  have h1 := le_trans (key 4096) (Nat.mul_le_mul_left (2 ^ 4096) (card_D_le 4096))
  exact absurd (lt_of_le_of_lt h1 growth) (lt_irrefl _)

/-- The modulus `Q`, the product of the odd primes below `257`. -/
def Q : ℕ := ∏ p ∈ S, p

theorem totient_Q : Nat.totient Q = ∏ p ∈ S, (p - 1) := by
  have h := Nat.totient_mul_prod_primeFactors Q
  have hpf : Q.primeFactors = S := Nat.primeFactors_prod S_prime
  rw [hpf] at h
  have hQ : 0 < Q := lt_trans (by norm_num) Qbig
  have h3 : ∏ p ∈ S, p = Q := rfl
  rw [h3, mul_comm Q (∏ p ∈ S, (p - 1))] at h
  exact Nat.eq_of_mul_eq_mul_right hQ h

open Classical in
/-- The finite set used in the counterexample: integers in `(T, 256 T]` with all prime
factors below `257`. -/
noncomputable def Aset (T : ℕ) : Finset ℕ := (Finset.Ioc T (256 * T)).filter Good

theorem mem_Aset {T a : ℕ} : a ∈ Aset T ↔ (T < a ∧ a ≤ 256 * T) ∧ Good a := by
  classical
  simp [Aset, Finset.mem_filter, Finset.mem_Ioc]

/-- `|Aset (256^k)| ≤ 8 |D (k+1)|`, via the odd part and the 2-adic exponent mod 8. -/
theorem card_Aset_le (k : ℕ) : (Aset (256 ^ k)).card ≤ 8 * (D (k + 1)).card := by
  classical
  set T := 256 ^ k with hT
  have hcard : (D (k + 1) ×ˢ Finset.range 8).card = 8 * (D (k + 1)).card := by
    rw [Finset.card_product, Finset.card_range, mul_comm]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun a => (ordCompl[2] a, a.factorization 2 % 8)) ?_ ?_
  · intro a ha
    rw [Finset.mem_coe, mem_Aset] at ha
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
    refine ⟨?_, Nat.mod_lt _ (by norm_num)⟩
    rw [mem_D]
    have hpos := Nat.ordCompl_pos 2 ha.2.1
    have hle := Nat.ordCompl_le a 2
    refine ⟨⟨hpos, ?_⟩, ?_, good_of_dvd ha.2 (Nat.ordCompl_dvd a 2)⟩
    · rw [pow_succ]; omega
    · exact Nat.coprime_two_left.1 (Nat.coprime_ordCompl Nat.prime_two ha.2.1)
  · intro a ha a' ha' heq
    rw [Finset.mem_coe, mem_Aset] at ha ha'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨ho, he⟩ := heq
    have ea := Nat.ordProj_mul_ordCompl_eq_self a 2
    have ea' := Nat.ordProj_mul_ordCompl_eq_self a' 2
    set e := a.factorization 2
    set e' := a'.factorization 2
    set o := ordCompl[2] a
    have hlt : ∀ {x y : ℕ} {u v : ℕ}, T < x → y ≤ 256 * T → 2 ^ u * o = x → 2 ^ v * o = y →
        u + 8 ≤ v → False := by
      intro x y u v hx hy hux hvy huv
      have : 2 ^ (u + 8) ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) huv
      have h256 : 2 ^ (u + 8) * o = 256 * x := by rw [← hux, pow_add]; ring
      have : 2 ^ (u + 8) * o ≤ 2 ^ v * o := Nat.mul_le_mul_right _ this
      omega
    rcases lt_trichotomy e e' with h | h | h
    · exact (hlt ha.1.1 ha'.1.2 ea (by rw [ho]; exact ea') (by omega)).elim
    · rw [← ea, ← ea', h, ho]
    · exact (hlt ha'.1.1 ha.1.2 (by rw [ho]; exact ea') ea (by omega)).elim

/-- For `1 ≤ d ≤ T`, some power of two moves `d` into `(T, 2T]`. -/
theorem exists_lift (T d : ℕ) :
    ∃ e, 1 ≤ d → d ≤ T → T < 2 ^ e * d ∧ 2 ^ e * d ≤ 2 * T := by
  classical
  by_cases hd : 1 ≤ d ∧ d ≤ T
  swap
  · exact ⟨0, fun h1 h2 => (hd ⟨h1, h2⟩).elim⟩
  have hex : ∃ e, T < 2 ^ e * d :=
    ⟨T, lt_of_lt_of_le Nat.lt_two_pow_self (Nat.le_mul_of_pos_right _ hd.1)⟩
  refine ⟨Nat.find hex, fun _ _ => ⟨Nat.find_spec hex, ?_⟩⟩
  have hne : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, pow_zero, one_mul] at this
    omega
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hmin := Nat.find_min hex (show e < Nat.find hex by omega)
  rw [he, pow_succ, mul_comm (2 ^ e) 2, mul_assoc]
  omega

theorem two_not_mem_S : 2 ∉ S := by decide

/-- Multiplying by a power of two and by `r` coprime to `Q` does not change the exponent of
any `p ∈ S`. -/
theorem factorization_lift {p e d r : ℕ} (hp : p ∈ S) (hd : d ≠ 0) (hr : r ≠ 0)
    (hcop : Q.Coprime r) : (2 ^ e * d * r).factorization p = d.factorization p := by
  have hpp := S_prime p hp
  rw [Nat.factorization_mul (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) hd) hr,
    Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hd]
  simp only [Finsupp.coe_add, Pi.add_apply]
  have h1 : (2 ^ e).factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h)
    exact two_not_mem_S (this ▸ hp)
  have h2 : r.factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    have hpQ : p ∣ Q := Finset.dvd_prod_of_mem _ hp
    exact (Nat.Prime.coprime_iff_not_dvd hpp).1 (Nat.Coprime.coprime_dvd_left hpQ hcop)
  rw [h1, h2]
  simp

/-- Erdős problem 488 is false as formalised: the negation of `erdos_488`. -/
theorem erdos_488_false : ¬ (∀ (A : Finset ℕ), A.Nonempty →
    0 ∉ A → 1 ∉ A →
    letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
    ∀ᵉ (n : ℕ) (m > n), A.max ≤ n →
      ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
        2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n) := by
  intro hall
  obtain ⟨k, hk⟩ := exists_slow
  set T := 256 ^ k with hT
  have hT1 : 1 ≤ T := Nat.one_le_pow _ _ (by norm_num)
  have hgT : Good T := good_pow (good_of_lt (by norm_num) (by norm_num))
  set A := Aset T with hAdef
  have h2T : 2 * T ∈ A :=
    mem_Aset.2 ⟨⟨by omega, by omega⟩, good_mul (good_of_lt (by norm_num) (by norm_num)) hgT⟩
  have hA0 : 0 ∉ A := fun h => by have := (mem_Aset.1 h).1.1; omega
  have hA1 : 1 ∉ A := fun h => by have := (mem_Aset.1 h).1.1; omega
  have hQ : 128 < Q := Qbig
  have hmax : A.max ≤ ((256 * T : ℕ) : WithBot ℕ) :=
    Finset.max_le (fun a ha => WithBot.coe_le_coe.2 (mem_Aset.1 ha).1.2)
  have hmn : 256 * T < 2 * T * Q := by nlinarith
  have h := hall A ⟨_, h2T⟩ hA0 hA1 (256 * T) (2 * T * Q) hmn hmax
  have h' : (((Finset.Icc 1 (2 * T * Q)).filter (· ∈ {n ≥ 1 | ∃ a ∈ A, a ∣ n})).card : ℚ)
      / ((2 * T * Q : ℕ) : ℚ) <
      2 * ((Finset.Icc 1 (256 * T)).filter (· ∈ {n ≥ 1 | ∃ a ∈ A, a ∣ n})).card
      / ((256 * T : ℕ) : ℚ) := h
  clear h hall
  -- upper bound at n = 256 T
  have hcn : ((Finset.Icc 1 (256 * T)).filter (· ∈ {n ≥ 1 | ∃ a ∈ A, a ∣ n})).card
      ≤ A.card := by
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hx
    obtain ⟨⟨hx1, hxn⟩, _, a, ha, c, rfl⟩ := hx
    rw [mem_Aset] at ha ⊢
    have hc1 : 1 ≤ c := Nat.pos_of_ne_zero (by rintro rfl; simp at hx1)
    have hc : c < 256 := by
      by_contra hc
      push Not at hc
      have : a * 256 ≤ a * c := Nat.mul_le_mul_left _ hc
      omega
    refine ⟨⟨?_, hxn⟩, good_mul ha.2 (good_of_lt hc1 (by omega))⟩
    have : a * 1 ≤ a * c := Nat.mul_le_mul_left _ hc1
    omega
  have hA := card_Aset_le k
  rw [← hT] at hA
  -- lower bound at m = 2 T Q
  choose f hf using exists_lift T
  let R := (Finset.range Q).filter (fun r => Q.Coprime r)
  have hR : R.card = Nat.totient Q := (Nat.totient_eq_card_coprime Q).symm
  have hcm : (D k).card * Nat.totient Q ≤
      ((Finset.Icc 1 (2 * T * Q)).filter (· ∈ {n ≥ 1 | ∃ a ∈ A, a ∣ n})).card := by
    rw [← hR, ← Finset.card_product]
    have hRmem : ∀ r ∈ R, 1 ≤ r ∧ r < Q ∧ Q.Coprime r := by
      intro r hr
      simp only [R, Finset.mem_filter, Finset.mem_range] at hr
      refine ⟨Nat.pos_of_ne_zero ?_, hr.1, hr.2⟩
      rintro rfl
      have := Nat.coprime_zero_right Q |>.1 hr.2
      omega
    have hDmem : ∀ d ∈ D k, 1 ≤ d ∧ d ≤ T ∧ Odd d ∧ Good d := by
      intro d hd
      rw [mem_D] at hd
      exact ⟨hd.1.1, hd.1.2, hd.2.1, hd.2.2⟩
    refine Finset.card_le_card_of_injOn (fun x => 2 ^ f x.1 * x.1 * x.2) ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_product] at hx
      obtain ⟨hd1, hdT, hdo, hdg⟩ := hDmem x.1 hx.1
      obtain ⟨hr1, hrQ, hrc⟩ := hRmem x.2 hx.2
      obtain ⟨hlo, hhi⟩ := hf x.1 hd1 hdT
      have hcA : 2 ^ f x.1 * x.1 ∈ A :=
        mem_Aset.2 ⟨⟨hlo, by omega⟩,
          good_mul (good_pow (good_of_lt (by norm_num) (by norm_num))) hdg⟩
      have hle : 2 ^ f x.1 * x.1 * x.2 ≤ 2 * T * Q := Nat.mul_le_mul hhi hrQ.le
      have hpos : 1 ≤ 2 ^ f x.1 * x.1 * x.2 :=
        Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
          (by omega)) (by omega))
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
      exact ⟨⟨hpos, hle⟩, hpos, _, hcA, Dvd.intro _ rfl⟩
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_product] at hx hy
      obtain ⟨hd1, hdT, hdo, hdg⟩ := hDmem x.1 hx.1
      obtain ⟨hr1, hrQ, hrc⟩ := hRmem x.2 hx.2
      obtain ⟨he1, heT, heo, heg⟩ := hDmem y.1 hy.1
      obtain ⟨hs1, hsQ, hsc⟩ := hRmem y.2 hy.2
      simp only at hxy
      have hd : x.1 = y.1 := by
        refine ext_S hdo heo hdg heg (fun p hp => ?_)
        have hx0 : x.1 ≠ 0 := by omega
        have hx2 : x.2 ≠ 0 := by omega
        have hy0 : y.1 ≠ 0 := by omega
        have hy2 : y.2 ≠ 0 := by omega
        rw [← factorization_lift hp hx0 hx2 hrc (e := f x.1),
          ← factorization_lift hp hy0 hy2 hsc (e := f y.1), hxy]
      rw [hd] at hxy
      have hr : x.2 = y.2 :=
        Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero
          (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (by omega))) hxy
      exact Prod.ext hd hr
  rw [totient_Q] at hcm
  have hF := ratio
  change 3 * Q ≤ 16 * ∏ p ∈ S, (p - 1) at hF
  generalize (∏ p ∈ S, (p - 1)) = F at hcm hF
  generalize ((Finset.Icc 1 (2 * T * Q)).filter (· ∈ {n ≥ 1 | ∃ a ∈ A, a ∣ n})).card = cm
    at hcm h'
  generalize ((Finset.Icc 1 (256 * T)).filter (· ∈ {n ≥ 1 | ∃ a ∈ A, a ∣ n})).card = cn
    at hcn h'
  have hmpos : (0 : ℚ) < ((2 * T * Q : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < 2 * T * Q)
  have hnpos : (0 : ℚ) < ((256 * T : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < 256 * T)
  rw [div_lt_div_iff₀ hmpos hnpos] at h'
  have hN : cm * (256 * T) < 2 * cn * (2 * T * Q) := by exact_mod_cast h'
  have hchain : 2 * cn * (2 * T * Q) ≤ cm * (256 * T) := by
    have hA' : A.card ≤ 8 * (D (k + 1)).card := hA
    have e1 : 2 * cn ≤ 24 * (D k).card := by omega
    calc 2 * cn * (2 * T * Q) ≤ 24 * (D k).card * (2 * T * Q) := Nat.mul_le_mul_right _ e1
      _ = 16 * ((D k).card * T) * (3 * Q) := by ring
      _ ≤ 16 * ((D k).card * T) * (16 * F) := Nat.mul_le_mul_left _ hF
      _ = (D k).card * F * (256 * T) := by ring
      _ ≤ cm * (256 * T) := Nat.mul_le_mul_right _ hcm
  omega

/-- `erdos_488_false` is literally the negation of `Statement`. -/
theorem not_statement : ¬ Statement := erdos_488_false

end Erdos488
