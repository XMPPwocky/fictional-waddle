import Mathlib

/-!
# Time sharing versus space sharing

PROVED.

Time (part 1).
* `tickState_stepTime`: at the tick `t k` of its `k`-th step, the scheduled program is in state
  `s^[k] x₀`, for every strictly increasing schedule `t : ℕ → ℕ`.
* `tickState_afterStep`: immediately after its `k`-th step it is in state `s^[k+1] x₀`.
* `trace_eq_orbit`: the observed trace (state at each of the program's own steps) is the orbit
  `fun k => s^[k] x₀`.
* `trace_schedule_invariant`: for any two schedules `t t'` and any observable
  `F : (ℕ → σ) → α`, `F (trace s x₀ t) = F (trace s x₀ t')`.
* `tickState_mem_orbit`: at every tick (idle or not) the state is some `s^[m] x₀`; the tick-level
  history is a stuttering of the orbit.

Space (part 2). `k` programs each pick one slot of `Fin n` uniformly and independently, i.e. a
uniformly random `f : Fin k → Fin n`; a collision is `¬ Function.Injective f`.
* `collisionProb_eq_prod`: for `0 < n` and every `k`,
  `collisionProb n k = 1 - ∏ i ∈ range k, (1 - i / n)` (exact product formula, all `k`).
* `collisionProb_two`: `collisionProb n 2 = 1 / n`.
* `pairCollisionProb_eq`: `P(f 0 = f 1) = 1 / n` for two programs.
* `collisionProb_three`: `collisionProb n 3 = 1 - (1 - 1 / n) * (1 - 2 / n)`.
* `collisionProb_pos`: for `0 < n` and `2 ≤ k`, the collision probability is positive.
* `card_image_eq_of_injective`: with no collision the number of distinct slots used is `k`.
* `expectedDistinct_lt`: for `0 < n` and `2 ≤ k`, the expected number of distinct slots used is
  strictly less than `k`.

INTERPRETED.
* A scheduler is a strictly increasing `t : ℕ → ℕ`; the program steps at tick `τ` iff `τ = t j`
  for some `j`, and is idle otherwise. `tickState s x₀ t τ` is the state at the start of tick `τ`.
* "The sequence of states the program passes through" is `trace s x₀ t k = tickState s x₀ t (t k)`,
  the state at the tick of its `k`-th step. "No function of the program's own state sequence can
  detect the schedule" is `trace_schedule_invariant`.
* Probabilities are uniform counting measures: `|event| / n ^ k` over `Fin k → Fin n`.
* "Expected number of distinct slots" is `(∑ f, |image f|) / n ^ k`. "n finite" is `0 < n`.
* The bound `≥ 1 - exp (-k(k-1)/(2n))` is not formalized (the target says it is not required).
-/

namespace TimeVsSpaceSharingB

open Finset

/-! ## Part 1: time sharing -/

section Time

variable {σ : Type*}

/-- State at the start of tick `τ` when the program `s` starting at `x₀` steps exactly at the ticks
in the range of the schedule `t`. -/
noncomputable def tickState (s : σ → σ) (x₀ : σ) (t : ℕ → ℕ) : ℕ → σ
  | 0 => x₀
  | τ + 1 => by
      classical
      exact if ∃ j, t j = τ then s (tickState s x₀ t τ) else tickState s x₀ t τ

/-- The observed trace: the state at the tick of the program's `k`-th step. -/
noncomputable def trace (s : σ → σ) (x₀ : σ) (t : ℕ → ℕ) (k : ℕ) : σ :=
  tickState s x₀ t (t k)

theorem tickState_succ_step (s : σ → σ) (x₀ : σ) (t : ℕ → ℕ) (τ : ℕ) (h : ∃ j, t j = τ) :
    tickState s x₀ t (τ + 1) = s (tickState s x₀ t τ) := by
  simp [tickState, h]

theorem tickState_succ_idle (s : σ → σ) (x₀ : σ) (t : ℕ → ℕ) (τ : ℕ) (h : ¬ ∃ j, t j = τ) :
    tickState s x₀ t (τ + 1) = tickState s x₀ t τ := by
  simp only [tickState]
  exact ite_eq_right_of_eq_false _ _ (eq_false h)

/-- Idle ticks do not change the state. -/
theorem tickState_idle (s : σ → σ) (x₀ : σ) (t : ℕ → ℕ) (a : ℕ) :
    ∀ d : ℕ, (∀ τ, a ≤ τ → τ < a + d → ¬ ∃ j, t j = τ) →
      tickState s x₀ t (a + d) = tickState s x₀ t a := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro h
    rw [← Nat.add_assoc, tickState_succ_idle s x₀ t (a + d) (h _ (by omega) (by omega))]
    exact ih (fun τ h1 h2 => h τ h1 (by omega))

theorem tickState_stepTime (s : σ → σ) (x₀ : σ) {t : ℕ → ℕ} (ht : StrictMono t) (k : ℕ) :
    tickState s x₀ t (t k) = s^[k] x₀ := by
  induction k with
  | zero =>
    have := tickState_idle s x₀ t 0 (t 0) (by
      rintro τ - hτ ⟨j, rfl⟩
      rw [zero_add] at hτ
      exact absurd (ht.lt_iff_lt.mp hτ) (Nat.not_lt_zero j))
    rw [zero_add] at this
    rw [this]
    rfl
  | succ k ih =>
    have hlt : t k < t (k + 1) := ht (Nat.lt_succ_self k)
    have hidle := tickState_idle s x₀ t (t k + 1) (t (k + 1) - (t k + 1)) (by
      rintro τ h1 h2 ⟨j, rfl⟩
      have a1 : k < j := ht.lt_iff_lt.mp (by omega)
      have a2 : j < k + 1 := ht.lt_iff_lt.mp (by omega)
      omega)
    have e : t k + 1 + (t (k + 1) - (t k + 1)) = t (k + 1) := by omega
    rw [e] at hidle
    rw [hidle, tickState_succ_step s x₀ t (t k) ⟨k, rfl⟩, ih,
      Function.iterate_succ_apply']

theorem tickState_afterStep (s : σ → σ) (x₀ : σ) {t : ℕ → ℕ} (ht : StrictMono t) (k : ℕ) :
    tickState s x₀ t (t k + 1) = s^[k + 1] x₀ := by
  rw [tickState_succ_step s x₀ t (t k) ⟨k, rfl⟩, tickState_stepTime s x₀ ht k,
    Function.iterate_succ_apply']

theorem trace_eq_orbit (s : σ → σ) (x₀ : σ) {t : ℕ → ℕ} (ht : StrictMono t) :
    trace s x₀ t = fun k => s^[k] x₀ := by
  funext k
  exact tickState_stepTime s x₀ ht k

theorem trace_schedule_invariant {α : Sort*} (s : σ → σ) (x₀ : σ) {t t' : ℕ → ℕ}
    (ht : StrictMono t) (ht' : StrictMono t') (F : (ℕ → σ) → α) :
    F (trace s x₀ t) = F (trace s x₀ t') := by
  rw [trace_eq_orbit s x₀ ht, trace_eq_orbit s x₀ ht']

theorem tickState_mem_orbit (s : σ → σ) (x₀ : σ) (t : ℕ → ℕ) (τ : ℕ) :
    ∃ m, tickState s x₀ t τ = s^[m] x₀ := by
  induction τ with
  | zero => exact ⟨0, rfl⟩
  | succ τ ih =>
    obtain ⟨m, hm⟩ := ih
    by_cases h : ∃ j, t j = τ
    · exact ⟨m + 1, by rw [tickState_succ_step s x₀ t τ h, hm, Function.iterate_succ_apply']⟩
    · exact ⟨m, by rw [tickState_succ_idle s x₀ t τ h, hm]⟩

end Time

/-! ## Part 2: space sharing -/

section Space

/-- Probability that `k` programs, each picking a uniform slot of `Fin n` independently,
have at least one collision. -/
noncomputable def collisionProb (n k : ℕ) : ℝ :=
  ((univ.filter (fun f : Fin k → Fin n => ¬ Function.Injective f)).card : ℝ) / (n : ℝ) ^ k

/-- Expected number of distinct slots used by `k` programs on `n` slots. -/
noncomputable def expectedDistinct (n k : ℕ) : ℝ :=
  ((∑ f : Fin k → Fin n, (univ.image f).card : ℕ) : ℝ) / (n : ℝ) ^ k

theorem card_injective (n k : ℕ) :
    (univ.filter (fun f : Fin k → Fin n => Function.Injective f)).card = n.descFactorial k := by
  classical
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fin n)),
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]

theorem descFactorial_cast (n k : ℕ) :
    ((n.descFactorial k : ℕ) : ℝ) = ∏ i ∈ range k, ((n : ℝ) - i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases le_or_gt k n with h | h
    · rw [Nat.descFactorial_succ, prod_range_succ, Nat.cast_mul, ih, mul_comm, Nat.cast_sub h]
    · have h0 : n.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr h
      have h0' : n.descFactorial (k + 1) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [h0', prod_range_succ, ← ih, h0]
      simp

theorem noCollisionProb_eq_prod (n k : ℕ) (hn : 0 < n) :
    ((univ.filter (fun f : Fin k → Fin n => Function.Injective f)).card : ℝ) / (n : ℝ) ^ k
      = ∏ i ∈ range k, (1 - (i : ℝ) / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [card_injective, descFactorial_cast,
    show (n : ℝ) ^ k = ∏ _i ∈ range k, (n : ℝ) by simp, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  field_simp

theorem card_inj_add_card_noninj (n k : ℕ) :
    ((univ.filter (fun f : Fin k → Fin n => Function.Injective f)).card : ℝ)
      + ((univ.filter (fun f : Fin k → Fin n => ¬ Function.Injective f)).card : ℝ)
      = (n : ℝ) ^ k := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin k → Fin n)))
    (fun f : Fin k → Fin n => Function.Injective f)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
  exact_mod_cast h

theorem collisionProb_eq_prod (n k : ℕ) (hn : 0 < n) :
    collisionProb n k = 1 - ∏ i ∈ range k, (1 - (i : ℝ) / n) := by
  have hn' : (n : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne')
  rw [← noCollisionProb_eq_prod n k hn, collisionProb, eq_sub_iff_add_eq, ← add_div,
    div_eq_one_iff_eq hn', add_comm]
  exact card_inj_add_card_noninj n k

theorem collisionProb_two (n : ℕ) (hn : 0 < n) : collisionProb n 2 = 1 / n := by
  rw [collisionProb_eq_prod n 2 hn]
  simp [Finset.prod_range_succ]

theorem injective_fin_two_iff {β : Type*} (f : Fin 2 → β) :
    Function.Injective f ↔ f 0 ≠ f 1 := by
  constructor
  · intro h e
    exact absurd (h e) (by decide)
  · intro h a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]

theorem pairCollisionProb_eq (n : ℕ) (hn : 0 < n) :
    ((univ.filter (fun f : Fin 2 → Fin n => f 0 = f 1)).card : ℝ) / (n : ℝ) ^ 2 = 1 / n := by
  rw [← collisionProb_two n hn, collisionProb]
  congr 3
  ext f
  simp [injective_fin_two_iff]

theorem collisionProb_three (n : ℕ) (hn : 0 < n) :
    collisionProb n 3 = 1 - (1 - 1 / (n : ℝ)) * (1 - 2 / n) := by
  rw [collisionProb_eq_prod n 3 hn]
  simp [Finset.prod_range_succ]

theorem collisionProb_pos (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) : 0 < collisionProb n k := by
  unfold collisionProb
  apply div_pos _ (pow_pos (by exact_mod_cast hn) _)
  have hne : (univ.filter (fun f : Fin k → Fin n => ¬ Function.Injective f)).Nonempty := by
    refine ⟨fun _ => ⟨0, hn⟩, ?_⟩
    simp only [mem_filter, mem_univ, true_and]
    intro h
    have := @h ⟨0, by omega⟩ ⟨1, by omega⟩ rfl
    simp [Fin.ext_iff] at this
  exact_mod_cast hne.card_pos

theorem card_image_eq_of_injective {n k : ℕ} (f : Fin k → Fin n) (hf : Function.Injective f) :
    (univ.image f).card = k := by
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

theorem expectedDistinct_lt (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) : expectedDistinct n k < k := by
  unfold expectedDistinct
  have hpos : (0 : ℝ) < (n : ℝ) ^ k := pow_pos (by exact_mod_cast hn) _
  rw [div_lt_iff₀ hpos]
  have hlt : (∑ f : Fin k → Fin n, (univ.image f).card) < ∑ _f : Fin k → Fin n, k := by
    apply Finset.sum_lt_sum
    · intro f _
      calc (univ.image f).card ≤ (univ : Finset (Fin k)).card := Finset.card_image_le
        _ = k := by simp
    · refine ⟨fun _ => ⟨0, hn⟩, mem_univ _, ?_⟩
      have : (univ.image (fun _ : Fin k => (⟨0, hn⟩ : Fin n))) = {⟨0, hn⟩} := by
        apply Finset.image_const
        exact ⟨⟨0, by omega⟩, mem_univ _⟩
      rw [this, Finset.card_singleton]
      omega
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, smul_eq_mul] at hlt
  have : ((∑ f : Fin k → Fin n, (univ.image f).card : ℕ) : ℝ) < ((n ^ k * k : ℕ) : ℝ) := by
    exact_mod_cast hlt
  rw [Nat.cast_mul, Nat.cast_pow] at this
  linarith

end Space

end TimeVsSpaceSharingB
