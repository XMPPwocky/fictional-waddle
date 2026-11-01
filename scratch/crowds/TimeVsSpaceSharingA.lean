import Mathlib

/-!
# Time sharing versus space sharing

PROVED

Time (part 1). For a step function `s : σ → σ`, an initial state `x₀`, and a schedule
`sched : ℕ → ℕ` (the tick times at which the program steps):
* `run_eq_iterate`: for every schedule (no monotonicity needed), the global state at tick `T`
  is `s^[stepsBefore sched T] x₀`, where `stepsBefore sched T` counts scheduled ticks `< T`.
* `stepsBefore_sched`: if `sched` is strictly increasing, `stepsBefore sched (sched k) = k`.
* `trace_eq_iterate`: the state the program is in at its `k`-th step time is `s^[k] x₀`;
  `trace_after_eq_iterate`: the state right after its `k`-th step is `s^[k+1] x₀`.
* `trace_indep`, `no_detector`: for any two strictly increasing schedules the traces are equal,
  hence every function `F` of the trace takes the same value on both.

Space (part 2). `k` programs each pick one of `n` slots; the joint outcome is uniform on
`Fin k → Fin n`, probabilities are counting ratios (`prob`).
* `prob_point`: every joint assignment has probability `∏_{i<k} (1/n)` (independent uniform).
* `card_noCollision`: the number of collision-free assignments is `n.descFactorial k`.
* `descFactorial_div_pow`: `descFactorial n k / n^k = ∏_{i<k} (1 - i/n)` for `0 < n`.
* `prob_collision`: for all `k` and `0 < n`,
  `P(at least one collision) = 1 - ∏_{i<k} (1 - i/n)`.
* `prob_collision_two`: for `k = 2` this is `1 - (1 - 0/n)(1 - 1/n) = 1/n`.
* `prob_collision_three`: for `k = 3` this is `1 - (1 - 0/n)(1 - 1/n)(1 - 2/n)
  = (3n - 2)/n^2`.
* `distinct_lt_iff_collision`: the number of distinct slots used is `< k` iff a collision occurs.
* `expDistinct_lt`: for `2 ≤ k` and `0 < n`, the expected number of distinct slots used is
  strictly less than `k`.

INTERPRETED
* "Run with a scheduler that inserts pauses": tick `T → T+1` applies `s` iff `T` is in the range
  of `sched`, otherwise the state is unchanged. The program's own trace is the state sampled at
  its step times, `run (sched k)`; the post-step samples `run (sched k + 1)` are also covered.
* "No function of the program's own state sequence can detect the schedule": any
  `F : (ℕ → σ) → α` gives equal values on the traces of any two strictly increasing schedules.
* "Uniformly and independently per step": the uniform (counting) distribution on joint
  assignments `Fin k → Fin n`; `prob_point` shows it is the product of `k` uniform marginals.
  "Collision" = the assignment is not injective. "n finite" = `n : ℕ` with `0 < n`.
* The optional bound `≥ 1 - exp(-k(k-1)/(2n))` is not formalized (the target says not required).
-/

namespace TimeVsSpaceSharingA

open Classical

section Time

variable {σ : Type*} (s : σ → σ) (x₀ : σ)

/-- Global state at tick `T` under schedule `sched`: the transition from tick `T` to `T+1`
applies `s` iff `T` is a scheduled time; otherwise the program idles. -/
noncomputable def run (sched : ℕ → ℕ) : ℕ → σ
  | 0 => x₀
  | T + 1 => if T ∈ Set.range sched then s (run sched T) else run sched T

/-- Number of scheduled ticks strictly before `T`. -/
noncomputable def stepsBefore (sched : ℕ → ℕ) (T : ℕ) : ℕ :=
  ((Finset.range T).filter (fun t => t ∈ Set.range sched)).card

theorem run_eq_iterate (sched : ℕ → ℕ) (T : ℕ) :
    run s x₀ sched T = s^[stepsBefore sched T] x₀ := by
  induction T with
  | zero => simp [run, stepsBefore]
  | succ T ih =>
    unfold stepsBefore
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : T ∈ Set.range sched
    · simp only [h, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp), Function.iterate_succ_apply']
      simp only [run, h, ↓reduceIte]
      rw [ih]; rfl
    · simp only [h, ↓reduceIte]
      simp only [run, h, ↓reduceIte]
      exact ih

theorem stepsBefore_sched {sched : ℕ → ℕ} (hs : StrictMono sched) (k : ℕ) :
    stepsBefore sched (sched k) = k := by
  unfold stepsBefore
  have : (Finset.range (sched k)).filter (fun t => t ∈ Set.range sched)
      = (Finset.range k).image sched := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨ht, j, rfl⟩
      exact ⟨j, hs.lt_iff_lt.mp ht, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hs hj, j, rfl⟩
  rw [this, Finset.card_image_of_injective _ hs.injective, Finset.card_range]

/-- The program's own state sequence: its state at each of its step times. -/
noncomputable def trace (sched : ℕ → ℕ) : ℕ → σ :=
  fun k => run s x₀ sched (sched k)

theorem trace_eq_iterate {sched : ℕ → ℕ} (hs : StrictMono sched) (k : ℕ) :
    trace s x₀ sched k = s^[k] x₀ := by
  unfold trace
  rw [run_eq_iterate, stepsBefore_sched hs]

theorem trace_after_eq_iterate {sched : ℕ → ℕ} (hs : StrictMono sched) (k : ℕ) :
    run s x₀ sched (sched k + 1) = s^[k + 1] x₀ := by
  have h : sched k ∈ Set.range sched := ⟨k, rfl⟩
  simp only [run, h, ↓reduceIte]
  rw [run_eq_iterate, stepsBefore_sched hs, Function.iterate_succ_apply']

theorem trace_indep {sched₁ sched₂ : ℕ → ℕ} (h₁ : StrictMono sched₁) (h₂ : StrictMono sched₂) :
    trace s x₀ sched₁ = trace s x₀ sched₂ := by
  funext k
  rw [trace_eq_iterate s x₀ h₁, trace_eq_iterate s x₀ h₂]

theorem no_detector {α : Type*} (F : (ℕ → σ) → α) {sched₁ sched₂ : ℕ → ℕ}
    (h₁ : StrictMono sched₁) (h₂ : StrictMono sched₂) :
    F (trace s x₀ sched₁) = F (trace s x₀ sched₂) := by
  rw [trace_indep s x₀ h₁ h₂]

end Time

section Space

/-- Probability of an event under the uniform distribution on joint slot assignments. -/
noncomputable def prob (k n : ℕ) (E : (Fin k → Fin n) → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ) / (Fintype.card (Fin k → Fin n) : ℝ)

/-- At least two programs touch the same slot. -/
def collision {k n : ℕ} (f : Fin k → Fin n) : Prop := ¬ Function.Injective f

theorem card_assign (k n : ℕ) : Fintype.card (Fin k → Fin n) = n ^ k := by simp

theorem prob_point (k n : ℕ) (a : Fin k → Fin n) :
    prob k n (fun f => f = a) = ∏ _i : Fin k, (1 / (n : ℝ)) := by
  unfold prob
  have h1 : ∀ S : Finset (Fin k → Fin n), (∀ f, f ∈ S ↔ f = a) → S.card = 1 :=
    fun S hS => Finset.card_eq_one.mpr ⟨a, by ext f; simp [hS]⟩
  rw [h1 _ (by simp), card_assign, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rw [one_div_pow]

theorem card_noCollision (k n : ℕ) :
    (Finset.univ.filter (fun f : Fin k → Fin n => Function.Injective f)).card
      = n.descFactorial k := by
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding
    (Fin k) (Fin n)), Fintype.card_embedding_eq]
  simp

theorem descFactorial_div_pow {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (n.descFactorial k : ℝ) / (n : ℝ) ^ k = ∏ i ∈ Finset.range k, (1 - (i : ℝ) / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k + 1 ≤ n
    · rw [Nat.descFactorial_succ, Finset.prod_range_succ, ← ih, Nat.cast_mul,
        Nat.cast_sub (by omega)]
      field_simp
      ring
    · have h0 : n.descFactorial (k + 1) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [h0, Nat.cast_zero, zero_div, eq_comm]
      apply Finset.prod_eq_zero (i := n) (Finset.mem_range.mpr (by omega))
      rw [div_self hn', sub_self]

theorem prob_collision (k : ℕ) {n : ℕ} (hn : 0 < n) :
    prob k n collision = 1 - ∏ i ∈ Finset.range k, (1 - (i : ℝ) / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpow : (n : ℝ) ^ k ≠ 0 := pow_ne_zero _ hn'
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k → Fin n)))
    (fun f => Function.Injective f)
  rw [card_noCollision, Finset.card_univ, card_assign] at hsplit
  have hR : ((n.descFactorial k : ℕ) : ℝ)
      + ((Finset.univ.filter (fun f : Fin k → Fin n => ¬ Function.Injective f)).card : ℝ)
      = (n : ℝ) ^ k := by exact_mod_cast hsplit
  unfold prob collision
  rw [card_assign, ← descFactorial_div_pow hn]
  push_cast
  rw [eq_sub_iff_add_eq, ← add_div, add_comm, div_eq_one_iff_eq hpow]
  convert hR using 4
  ext f; simp

theorem prob_collision_two {n : ℕ} (hn : 0 < n) :
    prob 2 n collision = 1 - (1 - (0 : ℝ) / n) * (1 - (1 : ℝ) / n) ∧
    prob 2 n collision = 1 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [prob_collision 2 hn]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  push_cast
  refine ⟨by ring, ?_⟩
  field_simp
  ring

theorem prob_collision_three {n : ℕ} (hn : 0 < n) :
    prob 3 n collision
      = 1 - (1 - (0 : ℝ) / n) * (1 - (1 : ℝ) / n) * (1 - (2 : ℝ) / n) ∧
    prob 3 n collision = (3 * (n : ℝ) - 2) / (n : ℝ) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [prob_collision 3 hn]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  push_cast
  refine ⟨by ring, ?_⟩
  field_simp
  ring

/-- Number of distinct slots used by an assignment. -/
def distinct {k n : ℕ} (f : Fin k → Fin n) : ℕ := (Finset.univ.image f).card

theorem distinct_le {k n : ℕ} (f : Fin k → Fin n) : distinct f ≤ k := by
  unfold distinct
  exact (Finset.card_image_le).trans (by simp)

theorem distinct_lt_iff_collision {k n : ℕ} (f : Fin k → Fin n) :
    distinct f < k ↔ collision f := by
  unfold distinct collision
  have hcard : (Finset.univ : Finset (Fin k)).card = k := by simp
  have hiff := Finset.card_image_iff (s := (Finset.univ : Finset (Fin k))) (f := f)
  rw [Finset.coe_univ, Set.injOn_univ, hcard] at hiff
  rw [← hiff]
  have := distinct_le f
  unfold distinct at this
  omega

/-- Expected number of distinct slots used under the uniform joint distribution. -/
noncomputable def expDistinct (k n : ℕ) : ℝ :=
  (∑ f : Fin k → Fin n, (distinct f : ℝ)) / (Fintype.card (Fin k → Fin n) : ℝ)

theorem expDistinct_lt {k n : ℕ} (hk : 2 ≤ k) (hn : 0 < n) : expDistinct k n < k := by
  have hpos : (0 : ℝ) < (Fintype.card (Fin k → Fin n) : ℝ) := by
    rw [card_assign]; exact_mod_cast pow_pos hn k
  unfold expDistinct
  rw [div_lt_iff₀ hpos]
  have hsum : ∑ f : Fin k → Fin n, (distinct f : ℝ) < ∑ _f : Fin k → Fin n, (k : ℝ) := by
    apply Finset.sum_lt_sum
    · intro f _
      exact_mod_cast distinct_le f
    · refine ⟨fun _ => ⟨0, hn⟩, Finset.mem_univ _, ?_⟩
      have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      have h1 : distinct (fun _ : Fin k => (⟨0, hn⟩ : Fin n)) = 1 := by
        unfold distinct
        rw [Finset.image_const hne, Finset.card_singleton]
      rw [h1]
      exact_mod_cast (by omega : 1 < k)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  linarith

end Space

end TimeVsSpaceSharingA
