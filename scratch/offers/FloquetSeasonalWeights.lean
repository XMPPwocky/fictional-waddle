import Mathlib

/-!
# Seasonal weights for periodic life cycles

Setting: `k ≥ 1` seasons (`[NeZero k]`, indices in `Fin k`, so `s + 1` wraps mod `k`),
`n ≥ 1` types (`[NeZero n]`), real matrices `M : Fin k → Matrix (Fin n) (Fin n) ℝ`.
The cycle product is `cycleProd M = M (k-1) * ... * M 0`, defined as
`(List.ofFn M).reverse.prod`. A seasonal weighting `(w, c)` has all entries of every `w s`
positive, every `c s` positive, and `w (s + 1) ᵥ* M s = c s • w s` for all `s`.

PROVED
* `cycleProd_two`: for `k = 2`, `cycleProd M = M 1 * M 0` (sanity check of the order).
* `suffix_identity`: for a seasonal weighting and `j ≤ k`,
  `w 0 ᵥ* (M (k-1) * ... * M j) = (c j * ... * c (k-1)) • w j` (with `w k := w 0`).
* `cycle_eigen` (part 1): a seasonal weighting satisfies
  `w 0 ᵥ* cycleProd M = (∏ s, c s) • w 0`.
* `seasonal_eq_formula`: every `w s` is determined by `w 0` and `c`:
  `w s = (c s * ... * c (k-1))⁻¹ • (w 0 ᵥ* (M (k-1) * ... * M s))`.
* `exists_unique_seasonal` (part 2): if all entries of every `M s` are positive, `v` is
  entrywise positive, `v ᵥ* cycleProd M = ρ • v`, and `c` is positive with `∏ s, c s = ρ`,
  then there is exactly one `w` such that `(w, c)` is a seasonal weighting with `w 0 = v`.
  Uniqueness of the Perron eigenvector of `P` is NOT used and NOT assumed.
* `gauge` (part 3): if `(w, c)` is a seasonal weighting and `λ` is positive, then
  `(s ↦ λ s • w s, s ↦ c s * λ (s+1) / λ s)` is a seasonal weighting.
* `gauge_prod` (part 3): `∏ s, c s * λ (s+1) / λ s = ∏ s, c s`.
* `gauge_complete`: two seasonal weightings `(w, c)`, `(w', c')` with `w' 0 = μ • w 0`,
  `μ > 0`, are related by the gauge transformation of some positive `λ`.
* `clock_factors_free`: given a seasonal weighting `(w, c)`, for every positive `c'` with
  `∏ c' = ∏ c` there is a (unique) seasonal weighting `(w', c')` with `w' 0 = w 0`; so the
  individual clock factors are not determined, only their product is.
* `clock_factors_not_proportional`: an explicit `k = 2`, `n = 1` instance with two seasonal
  weightings whose clock vectors `(1, 1)` and `(2, 1/2)` are not proportional.
* `exA_pos`, `exB_pos` (part 4): `A = !![1,1;1,1]`, `B = !![2,1;1,1]` have positive entries.
* `no_common_left_eigenvector` (part 4): any `w` with `w ᵥ* A = a • w` and `w ᵥ* B = b • w`
  is zero.
* `no_constant_seasonal_weight` (part 4): no entrywise positive `w` and reals `a b` satisfy
  `w ᵥ* A = a • w` and `w ᵥ* B = b • w`.
* `example_seasonal` (part 4, contrast): for `M = ![A, B]`, `w = ![![1,1], ![1,2/3]]`,
  `c = ![5/3, 3]` is a seasonal weighting (and `∏ c = 5` is the Perron root of `B * A`).

INTERPRETED (not formalized): the reading of `w` as season-dependent reproductive value and
of `∏ c` as the per-cycle growth factor.
-/

namespace FloquetSeasonalWeights

open Matrix Fin.NatCast

variable {k n : ℕ}

/-- Cycle product `M (k-1) * ... * M 0`. -/
def cycleProd (M : Fin k → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (List.ofFn M).reverse.prod

/-- Suffix product `M (k-1) * ... * M j` (equal to `1` for `j ≥ k`). -/
def suffixProd (M : Fin k → Matrix (Fin n) (Fin n) ℝ) (j : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  ((List.ofFn M).drop j).reverse.prod

/-- Suffix clock product `c j * ... * c (k-1)` (equal to `1` for `j ≥ k`). -/
def suffixClock (c : Fin k → ℝ) (j : ℕ) : ℝ :=
  ((List.ofFn c).drop j).prod

/-- Seasonal weighting: positive weights and clock factors with
`w (s + 1) ᵥ* M s = c s • w s`, indices mod `k`. -/
structure IsSeasonalWeighting [NeZero k] (M : Fin k → Matrix (Fin n) (Fin n) ℝ)
    (w : Fin k → Fin n → ℝ) (c : Fin k → ℝ) : Prop where
  w_pos : ∀ s i, 0 < w s i
  c_pos : ∀ s, 0 < c s
  eq : ∀ s, w (s + 1) ᵥ* M s = c s • w s

theorem cycleProd_two (M : Fin 2 → Matrix (Fin n) (Fin n) ℝ) :
    cycleProd M = M 1 * M 0 := by
  simp [cycleProd, List.ofFn_succ]

lemma suffixProd_zero (M : Fin k → Matrix (Fin n) (Fin n) ℝ) :
    suffixProd M 0 = cycleProd M := by
  simp [suffixProd, cycleProd]

lemma suffixProd_of_le (M : Fin k → Matrix (Fin n) (Fin n) ℝ) {j : ℕ} (h : k ≤ j) :
    suffixProd M j = 1 := by
  simp [suffixProd, List.drop_eq_nil_of_le (as := List.ofFn M) (by simpa using h)]

lemma suffixProd_succ (M : Fin k → Matrix (Fin n) (Fin n) ℝ) {j : ℕ} (h : j < k) :
    suffixProd M j = suffixProd M (j + 1) * M ⟨j, h⟩ := by
  unfold suffixProd
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

lemma suffixClock_zero (c : Fin k → ℝ) : suffixClock c 0 = ∏ s, c s := by
  simp [suffixClock, List.prod_ofFn]

lemma suffixClock_of_le (c : Fin k → ℝ) {j : ℕ} (h : k ≤ j) : suffixClock c j = 1 := by
  simp [suffixClock, List.drop_eq_nil_of_le (as := List.ofFn c) (by simpa using h)]

lemma suffixClock_succ (c : Fin k → ℝ) {j : ℕ} (h : j < k) :
    suffixClock c j = c ⟨j, h⟩ * suffixClock c (j + 1) := by
  unfold suffixClock
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

lemma suffixClock_pos (c : Fin k → ℝ) (hc : ∀ s, 0 < c s) (j : ℕ) : 0 < suffixClock c j := by
  unfold suffixClock
  apply List.prod_pos
  intro a ha
  obtain ⟨s, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop ha)
  exact hc s

lemma natCast_eq_mk [NeZero k] {j : ℕ} (h : j < k) : ((j : ℕ) : Fin k) = ⟨j, h⟩ :=
  Fin.ext (Fin.val_cast_of_lt h)

lemma cast_val [NeZero k] (s : Fin k) : ((s : ℕ) : Fin k) = s :=
  Fin.ext (Fin.val_cast_of_lt s.isLt)

lemma natCast_succ' [NeZero k] (j : ℕ) : ((j + 1 : ℕ) : Fin k) = (j : Fin k) + 1 := by
  ext
  simp [Fin.val_add, Fin.val_natCast, Nat.add_mod]

lemma natCast_self' [NeZero k] : ((k : ℕ) : Fin k) = 0 := by
  ext
  simp

lemma pos_vecMul [NeZero n] {u : Fin n → ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hu : ∀ i, 0 < u i) (hA : ∀ i j, 0 < A i j) : ∀ j, 0 < (u ᵥ* A) j := by
  intro j
  simp only [vecMul, dotProduct]
  exact Finset.sum_pos (fun i _ => mul_pos (hu i) (hA i j)) Finset.univ_nonempty

/-- Downward identity along a cycle, using only the eigen-relations. -/
theorem suffix_identity [NeZero k] {M : Fin k → Matrix (Fin n) (Fin n) ℝ}
    {w : Fin k → Fin n → ℝ} {c : Fin k → ℝ}
    (heq : ∀ s, w (s + 1) ᵥ* M s = c s • w s) :
    ∀ j, j ≤ k → w 0 ᵥ* suffixProd M j = suffixClock c j • w (j : Fin k) := by
  have key : ∀ t j, j + t = k →
      w 0 ᵥ* suffixProd M j = suffixClock c j • w (j : Fin k) := by
    intro t
    induction t with
    | zero =>
      intro j hj
      simp only [Nat.add_zero] at hj
      subst hj
      rw [suffixProd_of_le M le_rfl, suffixClock_of_le c le_rfl, natCast_self',
        vecMul_one, one_smul]
    | succ t ih =>
      intro j hj
      have hjk : j < k := by omega
      have h1 := ih (j + 1) (by omega)
      have hs := heq (j : Fin k)
      rw [natCast_eq_mk hjk] at hs
      rw [suffixProd_succ M hjk, suffixClock_succ c hjk, ← vecMul_vecMul, h1, smul_vecMul,
        natCast_succ', natCast_eq_mk hjk, hs, smul_smul, mul_comm]
  intro j hj
  exact key (k - j) j (by omega)

/-- Part (1). -/
theorem cycle_eigen [NeZero k] {M : Fin k → Matrix (Fin n) (Fin n) ℝ}
    {w : Fin k → Fin n → ℝ} {c : Fin k → ℝ} (h : IsSeasonalWeighting M w c) :
    w 0 ᵥ* cycleProd M = (∏ s, c s) • w 0 := by
  have := suffix_identity h.eq 0 (Nat.zero_le _)
  rwa [suffixProd_zero, suffixClock_zero, Nat.cast_zero] at this

theorem seasonal_eq_formula [NeZero k] {M : Fin k → Matrix (Fin n) (Fin n) ℝ}
    {w : Fin k → Fin n → ℝ} {c : Fin k → ℝ} (h : IsSeasonalWeighting M w c) (s : Fin k) :
    w s = (suffixClock c s)⁻¹ • (w 0 ᵥ* suffixProd M s) := by
  have hs := suffix_identity h.eq s s.isLt.le
  rw [cast_val] at hs
  rw [hs, smul_smul, inv_mul_cancel₀ (suffixClock_pos c h.c_pos s).ne', one_smul]

lemma pos_vecMul_suffix [NeZero n] {M : Fin k → Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ s i j, 0 < M s i j) {v : Fin n → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ j, ∀ i, 0 < (v ᵥ* suffixProd M j) i := by
  have key : ∀ t j, j + t = k → ∀ i, 0 < (v ᵥ* suffixProd M j) i := by
    intro t
    induction t with
    | zero =>
      intro j hj
      rw [suffixProd_of_le M (by omega), vecMul_one]
      exact hv
    | succ t ih =>
      intro j hj
      have hjk : j < k := by omega
      rw [suffixProd_succ M hjk, ← vecMul_vecMul]
      exact pos_vecMul (ih (j + 1) (by omega)) (hM _)
  intro j
  by_cases hj : j ≤ k
  · exact key (k - j) j (by omega)
  · rw [suffixProd_of_le M (by omega), vecMul_one]
    exact hv

/-- Part (2). -/
theorem exists_unique_seasonal [NeZero k] [NeZero n] {M : Fin k → Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ s i j, 0 < M s i j) {v : Fin n → ℝ} (hv : ∀ i, 0 < v i) {ρ : ℝ}
    (hP : v ᵥ* cycleProd M = ρ • v) {c : Fin k → ℝ} (hc : ∀ s, 0 < c s)
    (hcρ : ∏ s, c s = ρ) :
    ∃! w : Fin k → Fin n → ℝ, IsSeasonalWeighting M w c ∧ w 0 = v := by
  set W : ℕ → Fin n → ℝ := fun j => (suffixClock c j)⁻¹ • (v ᵥ* suffixProd M j) with hWdef
  have hρ : 0 < ρ := by
    rw [← hcρ]; exact Finset.prod_pos (fun s _ => hc s)
  have hW0 : W 0 = v := by
    simp only [hWdef, suffixProd_zero, suffixClock_zero, hcρ, hP, smul_smul,
      inv_mul_cancel₀ hρ.ne', one_smul]
  have hWk : W k = v := by
    simp only [hWdef, suffixProd_of_le M le_rfl, suffixClock_of_le c le_rfl, vecMul_one,
      inv_one, one_smul]
  have hcast : ∀ j, j ≤ k → W ((j : Fin k) : ℕ) = W j := by
    intro j hj
    rcases Nat.lt_or_eq_of_le hj with hlt | heq
    · rw [natCast_eq_mk hlt]
    · subst heq
      rw [natCast_self', Fin.val_zero, hW0, hWk]
  refine ⟨fun s => W s, ⟨⟨?_, hc, ?_⟩, ?_⟩, ?_⟩
  · intro s i
    simp only [hWdef, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr (suffixClock_pos c hc _)) (pos_vecMul_suffix hM hv _ i)
  · intro s
    have hsucc : W ((s + 1 : Fin k) : ℕ) = W ((s : ℕ) + 1) := by
      have := hcast ((s : ℕ) + 1) s.isLt
      rwa [natCast_succ', cast_val] at this
    show W ((s + 1 : Fin k) : ℕ) ᵥ* M s = c s • W s
    rw [hsucc]
    simp only [hWdef]
    rw [smul_vecMul, vecMul_vecMul, ← suffixProd_succ M s.isLt, smul_smul,
      suffixClock_succ c s.isLt]
    have h1 := (hc s).ne'
    have h2 := (suffixClock_pos c hc ((s : ℕ) + 1)).ne'
    congr 1
    field_simp
  · show W ((0 : Fin k) : ℕ) = v
    rw [Fin.val_zero, hW0]
  · rintro w' ⟨hw', hw'0⟩
    funext s
    rw [seasonal_eq_formula hw' s, hw'0]

/-- Part (3): gauge transformations preserve seasonal weightings. -/
theorem gauge [NeZero k] {M : Fin k → Matrix (Fin n) (Fin n) ℝ}
    {w : Fin k → Fin n → ℝ} {c : Fin k → ℝ} (h : IsSeasonalWeighting M w c)
    (l : Fin k → ℝ) (hl : ∀ s, 0 < l s) :
    IsSeasonalWeighting M (fun s => l s • w s) (fun s => c s * l (s + 1) / l s) where
  w_pos s i := by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_pos (hl s) (h.w_pos s i)
  c_pos s := div_pos (mul_pos (h.c_pos s) (hl _)) (hl s)
  eq s := by
    rw [smul_vecMul, h.eq s, smul_smul, smul_smul]
    congr 1
    field_simp [(hl s).ne']

/-- Part (3): the product of the clock factors is gauge invariant. -/
theorem gauge_prod [NeZero k] (c l : Fin k → ℝ) (hl : ∀ s, 0 < l s) :
    ∏ s, c s * l (s + 1) / l s = ∏ s, c s := by
  have hshift : ∏ s, l (s + 1) = ∏ s, l s :=
    Fintype.prod_equiv (Equiv.addRight (1 : Fin k)) _ _ (fun _ => rfl)
  have hne : ∏ s, l s ≠ 0 := (Finset.prod_pos (fun s _ => hl s)).ne'
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, hshift, mul_div_assoc,
    div_self hne, mul_one]

/-- Seasonal weightings with proportional `w 0` are gauge related. -/
theorem gauge_complete [NeZero k] [NeZero n] {M : Fin k → Matrix (Fin n) (Fin n) ℝ}
    {w w' : Fin k → Fin n → ℝ} {c c' : Fin k → ℝ} (h : IsSeasonalWeighting M w c)
    (h' : IsSeasonalWeighting M w' c') {μ : ℝ} (hμ : 0 < μ) (h0 : w' 0 = μ • w 0) :
    ∃ l : Fin k → ℝ, (∀ s, 0 < l s) ∧ (∀ s, w' s = l s • w s) ∧
      (∀ s, c' s = c s * l (s + 1) / l s) := by
  set l : Fin k → ℝ := fun s => μ * suffixClock c s / suffixClock c' s with hldef
  have hl : ∀ s, 0 < l s := fun s =>
    div_pos (mul_pos hμ (suffixClock_pos c h.c_pos s)) (suffixClock_pos c' h'.c_pos s)
  have hw : ∀ s, w' s = l s • w s := by
    intro s
    have e1 := seasonal_eq_formula h' s
    have e2 := seasonal_eq_formula h s
    rw [e1, h0, smul_vecMul, smul_smul]
    conv_rhs => rw [e2, smul_smul]
    congr 1
    have := (suffixClock_pos c h.c_pos s).ne'
    have := (suffixClock_pos c' h'.c_pos s).ne'
    simp only [hldef]
    field_simp
  refine ⟨l, hl, hw, ?_⟩
  intro s
  have e := h'.eq s
  rw [hw, hw, smul_vecMul, h.eq s, smul_smul, smul_smul] at e
  have i0 : Fin n := ⟨0, Nat.pos_of_neZero n⟩
  have ei := congrFun e i0
  simp only [Pi.smul_apply, smul_eq_mul] at ei
  have hwpos := h.w_pos s i0
  have hcoef : l (s + 1) * c s = c' s * l s := mul_right_cancel₀ hwpos.ne' ei
  have := (hl s).ne'
  field_simp
  linarith

/-- Only the product of the clock factors is determined. -/
theorem clock_factors_free [NeZero k] [NeZero n] {M : Fin k → Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ s i j, 0 < M s i j) {w : Fin k → Fin n → ℝ} {c : Fin k → ℝ}
    (h : IsSeasonalWeighting M w c) {c' : Fin k → ℝ} (hc' : ∀ s, 0 < c' s)
    (hprod : ∏ s, c' s = ∏ s, c s) :
    ∃! w' : Fin k → Fin n → ℝ, IsSeasonalWeighting M w' c' ∧ w' 0 = w 0 :=
  exists_unique_seasonal hM (h.w_pos 0) (cycle_eigen h) hc' hprod

theorem clock_factors_not_proportional :
    IsSeasonalWeighting (k := 2) (n := 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) ∧
    IsSeasonalWeighting (k := 2) (n := 1) (fun _ => 1) ![fun _ => 1, fun _ => 2] ![2, 1 / 2] ∧
    ¬ ∃ r : ℝ, ∀ s : Fin 2, (![2, 1 / 2] : Fin 2 → ℝ) s = r * 1 := by
  refine ⟨⟨fun _ _ => one_pos, fun _ => one_pos, fun s => by simp⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro s i
    fin_cases s <;> norm_num
  · intro s
    fin_cases s <;> norm_num
  · intro s
    rw [vecMul_one]
    fin_cases s
    · funext i
      simp
    · funext i
      simp
  · rintro ⟨r, hr⟩
    have h0 := hr 0
    have h1 := hr 1
    simp at h0 h1
    norm_num at h0 h1
    linarith

/-- Example season matrices for part (4). -/
def exA : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]
def exB : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 1]

theorem exA_pos : ∀ i j, 0 < exA i j := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [exA]

theorem exB_pos : ∀ i j, 0 < exB i j := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [exB]

theorem no_common_left_eigenvector (w : Fin 2 → ℝ) (a b : ℝ)
    (hA : w ᵥ* exA = a • w) (hB : w ᵥ* exB = b • w) : w = 0 := by
  have a0 := congrFun hA 0
  have a1 := congrFun hA 1
  have b0 := congrFun hB 0
  have b1 := congrFun hB 1
  simp [vecMul, dotProduct, Fin.sum_univ_two, exA, exB] at a0 a1 b0 b1
  have hp : w 0 = 0 := by
    by_cases ha : a = 0
    · subst ha
      have hq : w 1 = - w 0 := by linarith
      rw [hq] at b0 b1
      have : b * w 0 = 0 := by linarith
      nlinarith
    · have hpq : w 0 = w 1 := by
        have : a * (w 0 - w 1) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h ha
        · linarith
      rw [← hpq] at b0 b1
      linarith
  have hq : w 1 = 0 := by
    rw [hp] at a0 a1 b0 b1
    nlinarith
  funext i
  fin_cases i
  · exact hp
  · exact hq

/-- Part (4): no season-constant positive weight exists for `exA`, `exB`. -/
theorem no_constant_seasonal_weight :
    ¬ ∃ (w : Fin 2 → ℝ) (a b : ℝ), (∀ i, 0 < w i) ∧ w ᵥ* exA = a • w ∧ w ᵥ* exB = b • w := by
  rintro ⟨w, a, b, hw, hA, hB⟩
  have h := no_common_left_eigenvector w a b hA hB
  have := hw 0
  rw [h] at this
  exact lt_irrefl _ this

/-- Contrast for part (4): a genuinely seasonal weighting for the same pair. -/
theorem example_seasonal :
    IsSeasonalWeighting ![exA, exB] ![![1, 1], ![1, 2 / 3]] ![5 / 3, 3] ∧
      (∏ s, (![5 / 3, 3] : Fin 2 → ℝ) s) = 5 ∧
      (![1, 1] : Fin 2 → ℝ) ᵥ* cycleProd ![exA, exB] = (5 : ℝ) • ![1, 1] := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro s i
    fin_cases s <;> fin_cases i <;> norm_num
  · intro s
    fin_cases s <;> norm_num
  · intro s
    fin_cases s
    · funext i
      fin_cases i <;> simp [vecMul, dotProduct, Fin.sum_univ_two, exA] <;> norm_num
    · funext i
      fin_cases i <;> simp [vecMul, dotProduct, Fin.sum_univ_two, exB] <;> norm_num
  · norm_num [Fin.prod_univ_two]
  · rw [cycleProd_two]
    funext i
    fin_cases i <;>
      simp [vecMul, dotProduct, Fin.sum_univ_two, exA, exB, Matrix.mul_apply] <;> norm_num

end FloquetSeasonalWeights
