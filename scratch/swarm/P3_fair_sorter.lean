import Mathlib

/-!
# P3: a fair, total-conserving sorter gives Born statistics (gambler's ruin)

**What is proved (pure mathematics):**
* `path_harmonic_affine`: on the path `0..N` (`N ≥ 1`), any `h : ℕ → ℝ` with the
  discrete mean-value property `h i = (h (i-1) + h (i+1)) / 2` for `0 < i < N` is affine:
  `h i = h 0 + (h N - h 0) * i / N` for all `i ≤ N`.
* `fair_sorter_born`: with boundary values `h 0 = 0`, `h N = 1`, such an `h` equals `i / N`.
* `fair_sorter_born_exists`: `i / N` does satisfy these conditions (so the solution exists
  and is unique).
* `fair_sorter_born_fin`: the same uniqueness statement for `h : Fin (N+1) → ℝ`.
* `path_max_principle`: on the path, a harmonic `h` is bounded by its boundary values.
* `graph_max_principle` / `graph_harmonic_unique`: maximum principle and uniqueness for
  functions harmonic w.r.t. an arbitrary stochastic kernel `P` (nonnegative, rows summing to 1 off `B`) on a finite vertex set,
  off an absorbing boundary set `B`, assuming every vertex can reach `B` by positive-weight
  steps through non-boundary vertices.
* `ruin_kernel_born`: the gambler's-ruin kernel on `Fin (N+1)` satisfies all hypotheses of
  `graph_harmonic_unique` (proved, so they are not vacuous), and the graph theorem recovers
  `h i = i / N` for functions harmonic for that kernel.

**What is only interpreted (not formalised):** that the function `h` is the absorption
probability of a fair ±1 random walk ("a branch's share in a fair two-branch competition"),
i.e. that the probability of winning satisfies the mean-value equations (first-step analysis).
We do not construct the Markov chain or its hitting probabilities; the "Born statistics"
reading — win probability = initial share `i / N` — is the interpretation of
`fair_sorter_born`. No claim about quantum mechanics is formalised.
-/

namespace FairSorter

/-- Discrete harmonicity on the interior of the path `0..N`. -/
def PathHarmonic (N : ℕ) (h : ℕ → ℝ) : Prop :=
  ∀ i, 0 < i → i < N → h i = (h (i - 1) + h (i + 1)) / 2

/-- **Proved.** Harmonic functions on the path are affine (interpolate their boundary values). -/
theorem path_harmonic_affine (N : ℕ) (hN : 1 ≤ N) (h : ℕ → ℝ) (harm : PathHarmonic N h) :
    ∀ i, i ≤ N → h i = h 0 + (h N - h 0) * (i : ℝ) / (N : ℝ) := by
  set d := h 1 - h 0 with hd
  have key : ∀ i, i + 1 ≤ N → h i = h 0 + (i : ℝ) * d ∧ h (i + 1) = h 0 + ((i : ℝ) + 1) * d := by
    intro i
    induction i with
    | zero => intro _; simp [hd]
    | succ k ih =>
      intro hk
      obtain ⟨_, h2⟩ := ih (by omega)
      have e := harm (k + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at e
      obtain ⟨h1, _⟩ := ih (by omega)
      refine ⟨by push_cast; linarith, ?_⟩
      push_cast
      have : h (k + 1 + 1) = 2 * h (k + 1) - h k := by linarith
      rw [this, h1, h2]; ring
  have lin : ∀ i, i ≤ N → h i = h 0 + (i : ℝ) * d := by
    intro i hi
    rcases Nat.lt_or_ge i N with hlt | hge
    · exact (key i (by omega)).1
    · have hiN : i = N := le_antisymm hi hge
      obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
      subst hiN
      have := (key k le_rfl).2
      push_cast; linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hdN : d = (h N - h 0) / N := by
    have := lin N le_rfl
    field_simp
    linarith
  intro i hi
  rw [lin i hi, hdN]
  field_simp

/-- **Proved.** Gambler's-ruin uniqueness: boundary values `0` and `1` force `h i = i / N`.
*Interpretation:* the probability that a branch holding share `i` of `N` wins a fair
±1 competition equals its initial share `i / N` ("Born statistics from a martingale sorter"). -/
theorem fair_sorter_born (N : ℕ) (hN : 1 ≤ N) (h : ℕ → ℝ)
    (h0 : h 0 = 0) (hNv : h N = 1) (harm : PathHarmonic N h) :
    ∀ i, i ≤ N → h i = (i : ℝ) / (N : ℝ) := by
  intro i hi
  rw [path_harmonic_affine N hN h harm i hi, h0, hNv]
  ring

/-- **Proved.** Existence: `i ↦ i / N` satisfies the boundary conditions and harmonicity. -/
theorem fair_sorter_born_exists (N : ℕ) (hN : 1 ≤ N) :
    (fun i : ℕ => (i : ℝ) / (N : ℝ)) 0 = 0 ∧
    (fun i : ℕ => (i : ℝ) / (N : ℝ)) N = 1 ∧
    PathHarmonic N (fun i : ℕ => (i : ℝ) / (N : ℝ)) := by
  have hNpos : (N : ℝ) ≠ 0 := by have : (0:ℝ) < N := by exact_mod_cast hN
                                 exact this.ne'
  refine ⟨by simp, by simp [hNpos], ?_⟩
  intro i hi _
  have : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  simp only
  rw [this]
  push_cast
  field_simp
  ring

/-- **Proved.** The `Fin (N+1)` form of `fair_sorter_born`. -/
theorem fair_sorter_born_fin (N : ℕ) (hN : 1 ≤ N) (h : Fin (N + 1) → ℝ)
    (h0 : h 0 = 0) (hNv : h (Fin.last N) = 1)
    (harm : ∀ (i : Fin (N + 1)) (hi : 0 < i.val) (hi' : i.val < N),
      h i = (h ⟨i.val - 1, by omega⟩ + h ⟨i.val + 1, by omega⟩) / 2) :
    ∀ i : Fin (N + 1), h i = (i.val : ℝ) / (N : ℝ) := by
  let g : ℕ → ℝ := fun n => if hn : n < N + 1 then h ⟨n, hn⟩ else 0
  have hg : ∀ (n : ℕ) (hn : n < N + 1), g n = h ⟨n, hn⟩ := fun n hn => by simp only [g, hn, ↓reduceDIte]
  have g0 : g 0 = 0 := by rw [hg 0 (by omega)]; exact h0
  have gN : g N = 1 := by rw [hg N (by omega)]; exact hNv
  have gh : PathHarmonic N g := by
    intro i hi hi'
    rw [hg i (by omega), hg (i - 1) (by omega), hg (i + 1) (by omega)]
    exact harm ⟨i, by omega⟩ hi hi'
  intro i
  have := fair_sorter_born N hN g g0 gN gh i.val (by omega)
  rw [hg i.val i.isLt] at this
  exact this

/-- **Proved.** Maximum/minimum principle on the path. -/
theorem path_max_principle (N : ℕ) (hN : 1 ≤ N) (h : ℕ → ℝ) (harm : PathHarmonic N h) :
    ∀ i, i ≤ N → min (h 0) (h N) ≤ h i ∧ h i ≤ max (h 0) (h N) := by
  intro i hi
  have e := path_harmonic_affine N hN h harm i hi
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set t : ℝ := (i : ℝ) / N with ht
  have t0 : 0 ≤ t := by positivity
  have t1 : t ≤ 1 := by
    rw [ht, div_le_one hNpos]; exact_mod_cast hi
  have e' : h i = h 0 + (h N - h 0) * t := by rw [e, ht]; ring
  rcases le_total (h 0) (h N) with hle | hle
  · rw [min_eq_left hle, max_eq_right hle]
    constructor <;> nlinarith
  · rw [min_eq_right hle, max_eq_left hle]
    constructor <;> nlinarith

/-- One step of the kernel that is allowed before absorption: leave a non-boundary vertex
along a positive-weight edge. -/
def Step {V : Type*} (P : V → V → ℝ) (B : Set V) (u w : V) : Prop :=
  u ∉ B ∧ 0 < P u w

/-- **Proved.** Maximum principle on a finite graph with absorbing boundary `B`:
if `P` is a nonnegative kernel with rows summing to `1` off `B`, `h` is `P`-harmonic off `B`,
and every vertex can reach `B`, then every value of `h` is bounded by some boundary value. -/
theorem graph_max_principle {V : Type*} [Fintype V] (P : V → V → ℝ) (B : Set V)
    (hP0 : ∀ u w, 0 ≤ P u w) (hP1 : ∀ u, u ∉ B → ∑ w, P u w = 1)
    (h : V → ℝ) (harm : ∀ u, u ∉ B → h u = ∑ w, P u w * h w)
    (reach : ∀ v, ∃ b ∈ B, Relation.ReflTransGen (Step P B) v b) :
    ∀ v, ∃ b ∈ B, h v ≤ h b := by
  intro v
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image (Finset.univ : Finset V) h ⟨v, Finset.mem_univ v⟩
  have hmax : ∀ w, h w ≤ h m := fun w => hm w (Finset.mem_univ w)
  -- one step from a maximiser stays at the maximum
  have stepmax : ∀ x y, Step P B x y → h x = h m → h y = h m := by
    rintro x y ⟨hxB, hpos⟩ hx
    have hsum : ∑ w, P x w * (h m - h w) = 0 := by
      have : ∑ w, P x w * (h m - h w) = h m * ∑ w, P x w - ∑ w, P x w * h w := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun w _ => by ring
      rw [this, hP1 x hxB, ← harm x hxB, hx]; ring
    have hnn : ∀ w ∈ (Finset.univ : Finset V), 0 ≤ P x w * (h m - h w) :=
      fun w _ => mul_nonneg (hP0 x w) (sub_nonneg.mpr (hmax w))
    have hy := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum y (Finset.mem_univ y)
    rcases mul_eq_zero.mp hy with h1 | h1
    · exact absurd h1 hpos.ne'
    · linarith
  obtain ⟨b, hbB, hpath⟩ := reach m
  have : h b = h m := by
    clear hbB
    induction hpath with
    | refl => rfl
    | tail _ hst ih => exact stepmax _ _ hst ih
  exact ⟨b, hbB, this ▸ hmax v⟩

/-- **Proved.** Uniqueness of harmonic functions with given boundary values on a finite graph
with absorbing boundary reachable from everywhere. -/
theorem graph_harmonic_unique {V : Type*} [Fintype V] (P : V → V → ℝ) (B : Set V)
    (hP0 : ∀ u w, 0 ≤ P u w) (hP1 : ∀ u, u ∉ B → ∑ w, P u w = 1)
    (reach : ∀ v, ∃ b ∈ B, Relation.ReflTransGen (Step P B) v b)
    (h₁ h₂ : V → ℝ)
    (harm₁ : ∀ u, u ∉ B → h₁ u = ∑ w, P u w * h₁ w)
    (harm₂ : ∀ u, u ∉ B → h₂ u = ∑ w, P u w * h₂ w)
    (hB : ∀ b ∈ B, h₁ b = h₂ b) :
    h₁ = h₂ := by
  have harmD : ∀ (f g : V → ℝ), (∀ u, u ∉ B → f u = ∑ w, P u w * f w) →
      (∀ u, u ∉ B → g u = ∑ w, P u w * g w) →
      ∀ u, u ∉ B → (f - g) u = ∑ w, P u w * (f - g) w := by
    intro f g hf hg u hu
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [← hf u hu, ← hg u hu]
  funext v
  obtain ⟨b, hb, hle⟩ := graph_max_principle P B hP0 hP1 (h₁ - h₂) (harmD h₁ h₂ harm₁ harm₂) reach v
  obtain ⟨b', hb', hle'⟩ := graph_max_principle P B hP0 hP1 (h₂ - h₁) (harmD h₂ h₁ harm₂ harm₁) reach v
  simp only [Pi.sub_apply] at hle hle'
  have := hB b hb
  have := hB b' hb'
  linarith

/-- Left neighbour on the path `0..N` (stays at `0` at `0`). -/
def predF (N : ℕ) (u : Fin (N + 1)) : Fin (N + 1) := ⟨u.val - 1, by omega⟩

/-- Right neighbour on the path `0..N` (stays at `N` at `N`). -/
def succF (N : ℕ) (u : Fin (N + 1)) : Fin (N + 1) := ⟨min (u.val + 1) N, by omega⟩

/-- The fair ±1 kernel of gambler's ruin on `Fin (N+1)`. -/
noncomputable def ruinKernel (N : ℕ) (u w : Fin (N + 1)) : ℝ :=
  (if w = predF N u then 1 / 2 else 0) + (if w = succF N u then 1 / 2 else 0)

/-- Absorbing boundary `{0, N}`. -/
def ruinBoundary (N : ℕ) : Set (Fin (N + 1)) := {u | u.val = 0 ∨ u.val = N}

theorem ruinKernel_sum (N : ℕ) (u : Fin (N + 1)) (f : Fin (N + 1) → ℝ) :
    ∑ w, ruinKernel N u w * f w = (f (predF N u) + f (succF N u)) / 2 := by
  simp only [ruinKernel, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- **Proved.** ("down": the general graph theorem instantiated on the motivating chain.)
For the fair ±1 gambler's-ruin kernel `ruinKernel N` on `Fin (N+1)` with absorbing boundary
`{0, N}`: the kernel is nonnegative, its interior rows sum to `1`, every vertex reaches the
boundary by positive-weight interior steps (so the hypotheses of `graph_harmonic_unique` are
*satisfiable*, not vacuous), and any `h` that is harmonic for this kernel off the boundary with
`h 0 = 0`, `h N = 1` equals `i / N`. Derived from `graph_harmonic_unique`, independently of
`fair_sorter_born_fin`. *Interpretation only:* `h` as the win probability of the walk. -/
theorem ruin_kernel_born (N : ℕ) (hN : 1 ≤ N) (h : Fin (N + 1) → ℝ)
    (h0 : h 0 = 0) (hNv : h (Fin.last N) = 1)
    (harm : ∀ u, u ∉ ruinBoundary N → h u = ∑ w, ruinKernel N u w * h w) :
    (∀ u w, 0 ≤ ruinKernel N u w) ∧
    (∀ u, u ∉ ruinBoundary N → ∑ w, ruinKernel N u w = 1) ∧
    (∀ v, ∃ b ∈ ruinBoundary N,
      Relation.ReflTransGen (Step (ruinKernel N) (ruinBoundary N)) v b) ∧
    ∀ i : Fin (N + 1), h i = (i.val : ℝ) / (N : ℝ) := by
  have hP0 : ∀ u w, 0 ≤ ruinKernel N u w := by
    intro u w; unfold ruinKernel; split_ifs <;> norm_num
  have hP1 : ∀ u, u ∉ ruinBoundary N → ∑ w, ruinKernel N u w = 1 := by
    intro u _
    have := ruinKernel_sum N u (fun _ => 1)
    simp only [mul_one] at this
    rw [this]; norm_num
  have reach : ∀ v, ∃ b ∈ ruinBoundary N,
      Relation.ReflTransGen (Step (ruinKernel N) (ruinBoundary N)) v b := by
    intro v
    obtain ⟨n, hn⟩ : ∃ n, v.val = n := ⟨_, rfl⟩
    induction n generalizing v with
    | zero => exact ⟨v, Or.inl hn, Relation.ReflTransGen.refl⟩
    | succ k ih =>
      by_cases hvB : v ∈ ruinBoundary N
      · exact ⟨v, hvB, Relation.ReflTransGen.refl⟩
      · obtain ⟨b, hb, hpath⟩ := ih (predF N v) (by simp [predF, hn])
        refine ⟨b, hb, Relation.ReflTransGen.head ⟨hvB, ?_⟩ hpath⟩
        unfold ruinKernel
        split_ifs with h1 h2 <;> first | exact absurd rfl h1 | norm_num
  refine ⟨hP0, hP1, reach, ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have key := graph_harmonic_unique (ruinKernel N) (ruinBoundary N) hP0 hP1 reach h
    (fun i => (i.val : ℝ) / (N : ℝ)) harm ?_ ?_
  · intro i; exact congrFun key i
  · intro u hu
    rw [ruinKernel_sum]
    simp only [ruinBoundary, Set.mem_ofPred_eq, not_or] at hu
    have hlt : u.val < N := by have := u.isLt; omega
    simp only [predF, succF]
    rw [min_eq_left (by omega), Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  · intro b hb
    rcases hb with hb | hb
    · have : b = 0 := Fin.ext hb
      subst this; simp [h0]
    · have : b = Fin.last N := Fin.ext hb
      subst this; simp [hNv, hNpos.ne']

/-- Concrete numeric instance: in a fair competition with `N = 10`, a branch holding share `3`
wins with probability `3/10`. -/
example (h : ℕ → ℝ) (h0 : h 0 = 0) (h10 : h 10 = 1) (harm : PathHarmonic 10 h) :
    h 3 = 3 / 10 := by
  have := fair_sorter_born 10 (by norm_num) h h0 h10 harm 3 (by norm_num)
  rw [this]; norm_num

/-- The hypotheses of `fair_sorter_born` are jointly satisfiable (by `i / N` itself). -/
example : ∃ h : ℕ → ℝ, h 0 = 0 ∧ h 7 = 1 ∧ PathHarmonic 7 h :=
  ⟨fun i : ℕ => (i : ℝ) / ((7 : ℕ) : ℝ), fair_sorter_born_exists 7 (by norm_num)⟩

/-- The hypotheses of `ruin_kernel_born` are satisfiable (`N = 4`, `h = i / 4`), and the
graph route yields `h 1 = 1/4`. -/
example : ∃ h : Fin 5 → ℝ, h 0 = 0 ∧ h (Fin.last 4) = 1 ∧
    (∀ u, u ∉ ruinBoundary 4 → h u = ∑ w, ruinKernel 4 u w * h w) ∧ h 1 = 1 / 4 := by
  refine ⟨fun i => (i.val : ℝ) / 4, by simp, by simp, ?_, by simp⟩
  intro u hu
  rw [ruinKernel_sum]
  simp only [ruinBoundary, Set.mem_ofPred_eq, not_or] at hu
  have hlt : u.val < 4 := by have := u.isLt; omega
  simp only [predF, succF]
  rw [min_eq_left (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

end FairSorter
