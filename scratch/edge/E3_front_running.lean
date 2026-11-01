import Mathlib

/-!
# E3: front-running a predictable trader (proofs)

Model. A trader samples an action `a` from a distribution `p` over a finite nonempty type `A`;
action `a` has edge `e a ≥ 0`. An adversary who knows `p` (not the sample) guesses one action `b`;
if it matches it steals a fraction `lam ∈ [0,1]` of that trade's edge, so guess `b` steals
`lam * p b * e b` in expectation. The adversary's best guess attains `stolenMax p e = max_b p b * e b`
(lemmas `le_stolenMax`, `exists_eq_stolenMax`). The trader's net expected edge is
`net lam p e = gross p e - lam * stolenMax p e`.

Proved (this file; statements identical to `E3_front_running.statements.lean`, plus two
helper lemmas `stolenMax_fin2`, `net_fin2`; no original statement was changed. The adversarial
pass added theorem (5) and the concrete `example`s at the end to BOTH files):
* (1) `net_le_gross`: `net ≤ gross` (front-running never helps the trader).
* (2) `net_point_mass`: point mass on `astar` gives `net = (1 - lam) * e astar`.
  (Optimality of `astar` is NOT used: the formula holds for any point mass with `e ≥ 0`.)
* (3) `net_uniform`, `stolen_uniform`: uniform over a `k`-element set `S` with common edge `E ≥ 0`
  gives `net = E * (1 - lam / k)`; the stolen amount is `(lam * E) / k`, i.e. `1/k` of the
  point-mass loss `lam * E`. `net_uniform_fin` is the same for `A = Fin k`.
* (4) Two actions (`A = Fin 2`), edges `e1 ≥ e2 > 0`, `p = (q, 1 - q)`:
  - `two_action_mixed_optimum`: if `lam > 1 - e2/e1`, the UNIQUE optimum over all distributions on
    `Fin 2` is `q* = e2 / (e1 + e2)` (it equalizes `q e1 = (1-q) e2`), with `0 < q* < 1` (strictly
    mixed) and optimal value `(2 - lam) e1 e2 / (e1 + e2)`.
  - `two_action_pure_optimum`: if `0 ≤ lam ≤ 1 - e2/e1`, the pure policy `q = 1` is optimal, value
    `(1 - lam) e1`. Together these give the exact threshold.
* (5) `net_le_one_sub_div_card` (NEW, added by the adversarial pass, so it has no counterpart in the
  original statement list): for `lam ≥ 0` and any `p, e`, `N(p) ≤ (1 - lam/|A|) * gross p e`; with
  equal edges `E` and `Σ p = 1`, `N(p) ≤ E (1 - lam/|A|)`. So the factor-`k` reduction in (3) is the
  best possible, and uniform is optimal among all distributions when edges are equal.

Proof notes: in (4a) the hypotheses `hl0`, `hl1` and `p ≥ 0` are mathematically redundant: `lam > 0`
follows from the threshold (derived as `hlpos`), and the tent bound `N(q) ≤ N(q*)`, strict for
`q ≠ q*`, holds for every real `q`. (`hl1` may still be picked up silently by `nlinarith`.) In (4b)
`0 ≤ q ≤ 1` is used; `hl0` is passed as an `nlinarith` hint but is likely redundant (the linter
reports it unreferenced). It is in fact redundant: for `lam < 0`, `max ≤ e1` still gives the bound.
They are kept as model hypotheses (`lam ∈ [0,1]`, `p` a distribution).

Interpreted (not proved): that this risk-neutral expected-edge objective, with an adversary who
best-responds to the known `p` with a single guess, is the right model of front-running; and the
reading "spreading across k equally good markets reduces the stolen share by a factor k".
-/

namespace FrontRunning

open Finset

section General

variable {A : Type*} [Fintype A] [Nonempty A]

/-- Gross expected edge `Σ_a p a * e a`. -/
noncomputable def gross (p e : A → ℝ) : ℝ := ∑ a, p a * e a

/-- The adversary's best single-guess catch `max_b p b * e b`. -/
noncomputable def stolenMax (p e : A → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun b => p b * e b)

/-- Net expected edge `N(p) = Σ p a e a - lam * max_b (p b e b)`. -/
noncomputable def net (lam : ℝ) (p e : A → ℝ) : ℝ := gross p e - lam * stolenMax p e

/-- Every guess `b` catches at most `stolenMax`. -/
theorem le_stolenMax (p e : A → ℝ) (b : A) : p b * e b ≤ stolenMax p e := by
  exact Finset.le_sup' (fun b => p b * e b) (Finset.mem_univ b)

/-- Some guess attains `stolenMax` (so it is the adversary's best response). -/
theorem exists_eq_stolenMax (p e : A → ℝ) : ∃ b, p b * e b = stolenMax p e := by
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun b => p b * e b)
  exact ⟨b, hb.symm⟩

/-- **(1)** Front-running never helps: `N(p) ≤ Σ p a e a`. -/
theorem net_le_gross (lam : ℝ) (p e : A → ℝ) (hl : 0 ≤ lam)
    (hp : ∀ a, 0 ≤ p a) (he : ∀ a, 0 ≤ e a) :
    net lam p e ≤ gross p e := by
  have h0 : 0 ≤ stolenMax p e :=
    le_trans (mul_nonneg (hp (Classical.arbitrary A)) (he _)) (le_stolenMax p e _)
  unfold net
  nlinarith [mul_nonneg hl h0]

/-- **(2)** A point mass on `astar` nets `(1 - lam) * e astar`. -/
theorem net_point_mass [DecidableEq A] (lam : ℝ) (e : A → ℝ) (he : ∀ a, 0 ≤ e a) (astar : A) :
    net lam (fun a => if a = astar then 1 else 0) e = (1 - lam) * e astar := by
  have hs : stolenMax (fun a => if a = astar then (1:ℝ) else 0) e = e astar := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro b _
      by_cases h : b = astar
      · simp [h]
      · simp [h, he astar]
    · simpa using le_stolenMax (fun a => if a = astar then (1:ℝ) else 0) e astar
  have hg : gross (fun a => if a = astar then (1:ℝ) else 0) e = e astar := by
    simp [gross]
  rw [net, hs, hg]; ring

/-- **(3a)** Uniform over `S` (with `#S = k`), common edge `E ≥ 0` on `S`: stolen amount is `lam * E / k`. -/
theorem stolen_uniform [DecidableEq A] (lam : ℝ) (e : A → ℝ) (S : Finset A) (hS : S.Nonempty)
    (E : ℝ) (hE : 0 ≤ E) (heS : ∀ a ∈ S, e a = E) :
    lam * stolenMax (fun a => if a ∈ S then (1 : ℝ) / S.card else 0) e = (lam * E) / S.card := by
  have hs : stolenMax (fun a => if a ∈ S then (1 : ℝ) / S.card else 0) e = E / S.card := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro b _
      by_cases h : b ∈ S
      · simp [h, heS b h, div_eq_inv_mul]
      · simp [h]; positivity
    · obtain ⟨a, ha⟩ := hS
      have := le_stolenMax (fun a => if a ∈ S then (1 : ℝ) / S.card else 0) e a
      simp [ha, heS a ha] at this
      simpa [div_eq_inv_mul] using this
  rw [hs]; ring

/-- **(3b)** Uniform over `S` (with `#S = k`), common edge `E ≥ 0` on `S`: `N = E * (1 - lam / k)`. -/
theorem net_uniform [DecidableEq A] (lam : ℝ) (e : A → ℝ) (S : Finset A) (hS : S.Nonempty)
    (E : ℝ) (hE : 0 ≤ E) (heS : ∀ a ∈ S, e a = E) :
    net lam (fun a => if a ∈ S then (1 : ℝ) / S.card else 0) e = E * (1 - lam / S.card) := by
  have hc : (S.card : ℝ) ≠ 0 := by
    have := hS.card_pos; positivity
  have hg : gross (fun a => if a ∈ S then (1 : ℝ) / S.card else 0) e = E := by
    unfold gross
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_congr rfl
      (fun a ha => by rw [heS a ha] : ∀ a ∈ S, (1:ℝ) / S.card * e a = 1 / S.card * E)]
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [net, hg, stolen_uniform lam e S hS E hE heS]; ring

end General

/-- **(3c)** `k` markets `Fin k`, all with edge `E ≥ 0`, uniform policy: `N = E * (1 - lam / k)`. -/
theorem net_uniform_fin (k : ℕ) [NeZero k] (lam E : ℝ) (hE : 0 ≤ E) :
    net lam (fun _ : Fin k => (1 : ℝ) / k) (fun _ => E) = E * (1 - lam / k) := by
  have h := net_uniform lam (fun _ : Fin k => E) Finset.univ Finset.univ_nonempty E hE
    (fun _ _ => rfl)
  simpa using h

/-- Two-action policy `(q, 1 - q)`. -/
def mix2 (q : ℝ) : Fin 2 → ℝ := ![q, 1 - q]

/-- Two-action edges `(e1, e2)`. -/
def edges2 (e1 e2 : ℝ) : Fin 2 → ℝ := ![e1, e2]

/-- Helper (not in the statements file): on two actions the adversary's best catch is a binary `max`. -/
theorem stolenMax_fin2 (p e : Fin 2 → ℝ) : stolenMax p e = max (p 0 * e 0) (p 1 * e 1) :=
by
  apply le_antisymm
  · apply Finset.sup'_le
    intro b _
    fin_cases b
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (le_stolenMax p e 0) (le_stolenMax p e 1)

/-- Helper (not in the statements file): closed form of `net` on two actions. -/
theorem net_fin2 (lam e1 e2 : ℝ) (p : Fin 2 → ℝ) :
    net lam p (edges2 e1 e2) = p 0 * e1 + p 1 * e2 - lam * max (p 0 * e1) (p 1 * e2) :=
by
  simp [net, gross, stolenMax_fin2, Fin.sum_univ_two, edges2]

/-- **(4a)** If `lam > 1 - e2/e1` (with `e1 ≥ e2 > 0`), the unique optimal policy over all
distributions on two actions is the strictly mixed `q* = e2/(e1+e2)`, with value
`(2 - lam) e1 e2 / (e1 + e2)`. -/
theorem two_action_mixed_optimum (lam e1 e2 : ℝ) (he : e2 ≤ e1) (he2 : 0 < e2)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hl : 1 - e2 / e1 < lam) :
    0 < e2 / (e1 + e2) ∧ e2 / (e1 + e2) < 1 ∧
    net lam (mix2 (e2 / (e1 + e2))) (edges2 e1 e2) = (2 - lam) * e1 * e2 / (e1 + e2) ∧
    ∀ p : Fin 2 → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
      net lam p (edges2 e1 e2) ≤ net lam (mix2 (e2 / (e1 + e2))) (edges2 e1 e2) ∧
      (net lam p (edges2 e1 e2) = net lam (mix2 (e2 / (e1 + e2))) (edges2 e1 e2) →
        p = mix2 (e2 / (e1 + e2))) := by
  have he1 : 0 < e1 := lt_of_lt_of_le he2 he
  have hs : 0 < e1 + e2 := by linarith
  -- the threshold condition, cleared of the division
  have hc : e1 * (1 - lam) < e2 := by
    have h' : 1 - lam < e2 / e1 := by linarith
    rw [lt_div_iff₀ he1] at h'; linarith
  have hlpos : 0 < lam := by nlinarith
  set qs := e2 / (e1 + e2) with hqs
  have hqss : qs * (e1 + e2) = e2 := by rw [hqs]; field_simp
  have hV : net lam (mix2 qs) (edges2 e1 e2) = (2 - lam) * e1 * e2 / (e1 + e2) := by
    rw [net_fin2]
    simp only [mix2, Matrix.cons_val_zero, Matrix.cons_val_one]
    have heq : qs * e1 = (1 - qs) * e2 := by nlinarith
    rw [heq, max_self, eq_div_iff hs.ne']
    linear_combination (-(2 - lam) * e2) * hqss
  -- the tent bound, for every real q
  have key : ∀ q : ℝ,
      (q * e1 + (1 - q) * e2 - lam * max (q * e1) ((1 - q) * e2)) * (e1 + e2)
        ≤ (2 - lam) * e1 * e2 ∧
      (q ≠ qs → (q * e1 + (1 - q) * e2 - lam * max (q * e1) ((1 - q) * e2)) * (e1 + e2)
        < (2 - lam) * e1 * e2) := by
    intro q
    have hne : q ≠ qs → q * (e1 + e2) ≠ e2 := by
      intro h h'; apply h
      have : (q - qs) * (e1 + e2) = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h0
      · linarith
      · linarith
    rcases le_total (q * e1) ((1 - q) * e2) with h | h
    · rw [max_eq_right h]
      have hsl : 0 < e1 - e2 * (1 - lam) := by nlinarith
      refine ⟨by nlinarith [mul_nonneg (by nlinarith : (0:ℝ) ≤ e2 - q * (e1 + e2)) hsl.le], ?_⟩
      intro hq
      have hlt : 0 < e2 - q * (e1 + e2) := by
        rcases lt_or_eq_of_le (by nlinarith : q * (e1 + e2) ≤ e2) with h1 | h1
        · linarith
        · exact absurd h1 (hne hq)
      nlinarith [mul_pos hlt hsl]
    · rw [max_eq_left h]
      have hsr : 0 < e2 - e1 * (1 - lam) := by linarith
      refine ⟨by nlinarith [mul_nonneg (by nlinarith : (0:ℝ) ≤ q * (e1 + e2) - e2) hsr.le], ?_⟩
      intro hq
      have hlt : 0 < q * (e1 + e2) - e2 := by
        rcases lt_or_eq_of_le (by nlinarith : e2 ≤ q * (e1 + e2)) with h1 | h1
        · linarith
        · exact absurd h1.symm (hne hq)
      nlinarith [mul_pos hlt hsr]
  refine ⟨div_pos he2 hs, (div_lt_one hs).mpr (by linarith), hV, ?_⟩
  intro p _ hsum
  have hp1 : p 1 = 1 - p 0 := by rw [Fin.sum_univ_two] at hsum; linarith
  have hN : net lam p (edges2 e1 e2) =
      p 0 * e1 + (1 - p 0) * e2 - lam * max (p 0 * e1) ((1 - p 0) * e2) := by
    rw [net_fin2, hp1]
  rw [hN, hV, le_div_iff₀ hs]
  refine ⟨(key (p 0)).1, ?_⟩
  intro heq
  have hq : p 0 = qs := by
    by_contra hq
    have := (key (p 0)).2 hq
    rw [heq, div_mul_cancel₀ _ hs.ne'] at this
    exact lt_irrefl _ this
  funext i
  fin_cases i
  · simp [mix2, hq]
  · simp [mix2, hp1, hq]

/-- **(4b)** If `0 ≤ lam ≤ 1 - e2/e1` (with `e1 ≥ e2 > 0`), the pure policy on action 1 is optimal,
with value `(1 - lam) e1`. -/
theorem two_action_pure_optimum (lam e1 e2 : ℝ) (he : e2 ≤ e1) (he2 : 0 < e2)
    (hl0 : 0 ≤ lam) (hl : lam ≤ 1 - e2 / e1) :
    net lam (mix2 1) (edges2 e1 e2) = (1 - lam) * e1 ∧
    ∀ p : Fin 2 → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
      net lam p (edges2 e1 e2) ≤ net lam (mix2 1) (edges2 e1 e2) := by
  have he1 : 0 < e1 := lt_of_lt_of_le he2 he
  have hc : e2 ≤ e1 * (1 - lam) := by
    have h' : e2 / e1 ≤ 1 - lam := by linarith
    rw [div_le_iff₀ he1] at h'; linarith
  have hV : net lam (mix2 1) (edges2 e1 e2) = (1 - lam) * e1 := by
    rw [net_fin2]
    simp only [mix2, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [max_eq_left (by simp; linarith)]
    ring
  refine ⟨hV, ?_⟩
  intro p hp hsum
  have hp1 : p 1 = 1 - p 0 := by rw [Fin.sum_univ_two] at hsum; linarith
  have hq0 : 0 ≤ p 0 := hp 0
  have hq1 : p 0 ≤ 1 := by have := hp 1; linarith
  rw [net_fin2, hp1, hV]
  rcases le_total (p 0 * e1) ((1 - p 0) * e2) with h | h
  · rw [max_eq_right h]
    nlinarith [mul_nonneg hq0 (by linarith : (0:ℝ) ≤ e1 * (1 - lam) - e2),
      mul_nonneg hl0 (sub_nonneg.mpr h), mul_nonneg hq0 hl0, mul_nonneg hl0 (sub_nonneg.mpr he)]
  · rw [max_eq_left h]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - p 0) (by linarith : (0:ℝ) ≤ e1 * (1 - lam) - e2)]

/-- **(5, added by the adversarial pass; going up to general `k`)** Converse of (3): the adversary
always takes at least the average, `max_b p b e b ≥ (1/k) Σ_b p b e b` with `k = |A|`. So for `lam ≥ 0`
EVERY policy (no sign conditions on `p` or `e`) nets at most `(1 - lam/k) * gross`, so no policy
cuts the stolen share below `1/k`. With equal edges `E` and `Σ p = 1`, every policy nets at most
`E * (1 - lam/k)`, which (3c) shows the uniform policy attains: uniform is optimal. -/
theorem net_le_one_sub_div_card {A : Type*} [Fintype A] [Nonempty A]
    (lam : ℝ) (hl : 0 ≤ lam) (p e : A → ℝ) :
    net lam p e ≤ (1 - lam / Fintype.card A) * gross p e ∧
    (∀ E : ℝ, (∀ a, e a = E) → ∑ a, p a = 1 →
      net lam p e ≤ E * (1 - lam / Fintype.card A)) := by
  have hk : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have havg : gross p e ≤ Fintype.card A * stolenMax p e := by
    unfold gross
    calc ∑ a, p a * e a ≤ ∑ _a : A, stolenMax p e :=
          Finset.sum_le_sum (fun a _ => le_stolenMax p e a)
      _ = Fintype.card A * stolenMax p e := by simp
  have h1 : net lam p e ≤ (1 - lam / Fintype.card A) * gross p e := by
    have : lam * gross p e ≤ Fintype.card A * (lam * stolenMax p e) := by nlinarith
    have h2 : lam / Fintype.card A * gross p e ≤ lam * stolenMax p e := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hk]; linarith
    unfold net; nlinarith
  refine ⟨h1, fun E hE hsum => ?_⟩
  have hg : gross p e = E := by
    simp only [gross, hE, ← Finset.sum_mul, hsum, one_mul]
  rw [hg] at h1; linarith

/-! ### Concrete non-vacuity examples (added by the adversarial pass)
`e = (2, 1)`, `lam = 1`: the threshold `1 - e2/e1 = 1/2 < 1` holds; the mixed `q* = 1/3` nets `2/3`
while the pure policy nets `0`, and (4a) certifies that `2/3` is the optimum.
`e = (4, 1)`, `lam = 1/2`: the threshold is `3/4 ≥ 1/2`, so the pure policy is optimal at `2`
and the equalizing mix `q = 1/5` nets only `6/5`.
Three equal markets with edge `6` and `lam = 1`: uniform nets `4 = 6 (1 - 1/3)`, and (5) gives `≤ 4`
for every distribution. -/

example : net 1 (mix2 (1/3)) (edges2 2 1) = 2/3 ∧ net 1 (mix2 1) (edges2 2 1) = 0 := by
  constructor <;> (rw [net_fin2]; simp [mix2]; try norm_num)

example : ∀ p : Fin 2 → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
    net 1 p (edges2 2 1) ≤ 2/3 := by
  intro p hp hs
  obtain ⟨-, -, hV, hopt⟩ := two_action_mixed_optimum 1 2 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have := (hopt p hp hs).1
  rw [hV] at this; norm_num at this; linarith

example : net (1/2) (mix2 1) (edges2 4 1) = 2 ∧ net (1/2) (mix2 (1/5)) (edges2 4 1) = 6/5 := by
  constructor <;> (rw [net_fin2]; simp [mix2]; try norm_num)

example : ∀ p : Fin 2 → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
    net (1/2) p (edges2 4 1) ≤ 2 := by
  intro p hp hs
  obtain ⟨hV, hopt⟩ := two_action_pure_optimum (1/2) 4 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have := hopt p hp hs
  rw [hV] at this; norm_num at this; linarith

example : net 1 (fun _ : Fin 3 => (1:ℝ)/3) (fun _ => 6) = 4 ∧
    ∀ p : Fin 3 → ℝ, ∑ a, p a = 1 → net 1 p (fun _ => 6) ≤ 4 := by
  refine ⟨?_, fun p hs => ?_⟩
  · have h := net_uniform_fin 3 1 6 (by norm_num)
    norm_num at h ⊢; linarith
  · have := (net_le_one_sub_div_card 1 (by norm_num) p (fun _ => 6)).2 6 (fun _ => rfl) hs
    norm_num at this; linarith

end FrontRunning
