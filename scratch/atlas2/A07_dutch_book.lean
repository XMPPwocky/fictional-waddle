import Mathlib

/-!
# A07 Dutch book on a finite partition — proofs

Convention: `s i` is the number of unit tickets on outcome `i` that the bettor BUYS
from the bookie at the bettor's posted price `q i` (negative `s i` = the bettor SELLS).
The bookie receives `Σ i, s i * q i` up front and pays `s j` when outcome `j` occurs.

Docstrings below marked **Proved** are fully proved (no placeholders) in `A07_dutch_book.lean`, which has
the identical statements. Deviations from the task text: the main theorem `dutch_book_iff`
drops the `Nonempty ι` hypothesis (strictly more general; it is true for empty `ι`);
`dutch_book_iff_nonempty` restates it verbatim-unfolded with `[Nonempty ι]`.
`sureWin_of_neg` carries `[DecidableEq ι]` only so that the indicator book can be written.

Adversarial-pass additions (new declarations only; no existing statement changed):
`payoff_smul` (linearity helper), `dutch_book_unbounded` / `dutch_book_unbounded_iff`
(generalization: incoherent prices admit books with arbitrarily large guaranteed gain),
and concrete non-vacuity instances `example_overround`, `example_fair_coin`,
`example_negative_price`.
-/

open Finset

namespace A07

variable {ι : Type*} [Fintype ι]

/-- Bookie's net payoff in outcome `j` for book `s` at prices `q`. -/
noncomputable def payoff (q s : ι → ℝ) (j : ι) : ℝ := (∑ i, s i * q i) - s j

/-- `q` is a probability vector. -/
def IsProb (q : ι → ℝ) : Prop := (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1

/-- `s` is a sure win (Dutch book) for the bookie: strictly positive in every outcome. -/
def SureWin (q s : ι → ℝ) : Prop := ∀ j, 0 < payoff q s j

/-- **Proved (algebraic identity).** Averaging the bookie's payoff with weights `q`:
`Σ_j q_j · payoff_j = (Σ q − 1) · Σ_i s_i q_i`. When `Σ q = 1` the `q`-weighted payoff is
zero, which is the whole mechanism behind the converse Dutch book theorem. -/
theorem weighted_payoff (q s : ι → ℝ) :
    ∑ j, q j * payoff q s j = ((∑ j, q j) - 1) * ∑ i, s i * q i := by
  unfold payoff
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have : ∑ j, q j * s j = ∑ i, s i * q i := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [this]; ring

/-- **Proved.** If `q` is a probability vector, there is no book that gives the bookie a strictly
positive payoff in every outcome. (Interpretation: coherent prices cannot be Dutch-booked.) -/
theorem no_sureWin_of_isProb {q : ι → ℝ} (hq : IsProb q) (s : ι → ℝ) : ¬ SureWin q s := by
  intro hs
  obtain ⟨hnn, hsum⟩ := hq
  have hw := weighted_payoff q s
  rw [hsum, sub_self, zero_mul] at hw
  have hex : ∃ j ∈ (Finset.univ : Finset ι), 0 < q j := by
    by_contra hne
    simp only [Finset.mem_univ, true_and, not_exists, not_lt] at hne
    have : ∑ i, q i ≤ 0 := Finset.sum_nonpos (fun i _ => hne i)
    linarith
  have hpos : 0 < ∑ j, q j * payoff q s j := by
    obtain ⟨j, -, hj⟩ := hex
    exact Finset.sum_pos' (fun i _ => mul_nonneg (hnn i) (hs i).le)
      ⟨j, Finset.mem_univ _, mul_pos hj (hs j)⟩
  linarith

/-- **Proved.** If some price `q k < 0`, the book where the bettor *sells* one ticket on `k`
(`s k = -1`, i.e. the bookie buys it at the negative price, so the bettor pays the bookie
`-q k` to take it) is a sure win: payoff `-q k` off `k` and `1 - q k` on `k`. -/
theorem sureWin_of_neg [DecidableEq ι] {q : ι → ℝ} {k : ι} (hk : q k < 0) :
    SureWin q (fun i => if i = k then -1 else 0) := by
  intro j
  unfold payoff
  simp only [ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hj : j = k
  · simp only [hj, ite_true]; linarith
  · simp only [hj, ite_false]; linarith

/-- **Proved.** If `Σ q > 1`, selling the bettor one ticket on every outcome is a sure win:
payoff `Σ q - 1 > 0` in every outcome. -/
theorem sureWin_of_sum_gt {q : ι → ℝ} (h : 1 < ∑ i, q i) : SureWin q (fun _ => 1) := by
  intro j
  unfold payoff
  simp only [one_mul]
  linarith

/-- **Proved.** If `Σ q < 1`, buying one ticket on every outcome from the bettor
(`s ≡ -1`) is a sure win: payoff `1 - Σ q > 0` in every outcome. -/
theorem sureWin_of_sum_lt {q : ι → ℝ} (h : ∑ i, q i < 1) : SureWin q (fun _ => -1) := by
  intro j
  unfold payoff
  simp only [neg_one_mul, Finset.sum_neg_distrib]
  linarith

/-- **Proved (main theorem, A07).** A sure-win book exists iff `q` is not a probability vector.
No `Nonempty ι` hypothesis is needed: for empty `ι` both sides are true (sure-win is vacuous,
and `Σ q = 0 ≠ 1`). Interpretation (de Finetti / Ramsey): incoherent betting prices are exactly
the exploitable ones; this formal statement covers only unit tickets on a finite partition with
arbitrary real (positive or negative) stakes and the *strict* every-outcome notion of sure loss. -/
theorem dutch_book_iff (q : ι → ℝ) : (∃ s, SureWin q s) ↔ ¬ IsProb q := by
  constructor
  · rintro ⟨s, hs⟩ hq
    exact no_sureWin_of_isProb hq s hs
  · intro h
    classical
    by_cases hnn : ∀ i, 0 ≤ q i
    · have hne : ∑ i, q i ≠ 1 := fun he => h ⟨hnn, he⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨_, sureWin_of_sum_lt hlt⟩
      · exact ⟨_, sureWin_of_sum_gt hgt⟩
    · simp only [not_forall, not_le] at hnn
      obtain ⟨k, hk⟩ := hnn
      exact ⟨_, sureWin_of_neg hk⟩

/-- **Proved.** The same theorem in the task's original form, fully unfolded and with the
`Nonempty ι` hypothesis the task statement mentions (which is not used). -/
theorem dutch_book_iff_nonempty [Nonempty ι] (q : ι → ℝ) :
    (∃ s : ι → ℝ, ∀ j, 0 < (∑ i, s i * q i) - s j) ↔
      ¬ ((∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) := by
  exact dutch_book_iff q

/-- **Proved (helper, adversarial pass).** The payoff is linear in the book: scaling every
stake by `c` scales the bookie's payoff in each outcome by `c`. -/
theorem payoff_smul (q s : ι → ℝ) (c : ℝ) (j : ι) :
    payoff q (fun i => c * s i) j = c * payoff q s j := by
  unfold payoff
  rw [mul_sub, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- **Proved (generalization, adversarial pass).** Unbounded exploitation: if `q` is not a
probability vector then for every target `M` there is a book paying the bookie strictly more
than `M` in every outcome. (Interpretation: incoherence is not a small leak; with unrestricted
stakes the bookie's guaranteed gain is unbounded. Proof: take a sure-win book, let `ε > 0` be its
minimum payoff over the finitely many outcomes, and scale it by `(|M| + 1) / ε`.) -/
theorem dutch_book_unbounded {q : ι → ℝ} (h : ¬ IsProb q) (M : ℝ) :
    ∃ s : ι → ℝ, ∀ j, M < payoff q s j := by
  obtain ⟨s, hs⟩ := (dutch_book_iff q).2 h
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨s, fun j => (IsEmpty.false j).elim⟩
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image (Finset.univ : Finset ι) (payoff q s)
    Finset.univ_nonempty
  have hε : 0 < payoff q s j₀ := hs j₀
  refine ⟨fun i => ((|M| + 1) / payoff q s j₀) * s i, fun j => ?_⟩
  rw [payoff_smul]
  have hj : payoff q s j₀ ≤ payoff q s j := hj₀ j (Finset.mem_univ j)
  have hc : 0 < (|M| + 1) / payoff q s j₀ := div_pos (by positivity) hε
  calc M < |M| + 1 := by linarith [le_abs_self M]
    _ = (|M| + 1) / payoff q s j₀ * payoff q s j₀ := by field_simp
    _ ≤ (|M| + 1) / payoff q s j₀ * payoff q s j := mul_le_mul_of_nonneg_left hj hc.le

/-- **Proved (converse of the generalization).** For a probability vector `q`, no book clears
even `M = 0` everywhere, so the unbounded form is also an iff. -/
theorem dutch_book_unbounded_iff (q : ι → ℝ) :
    (∀ M : ℝ, ∃ s : ι → ℝ, ∀ j, M < payoff q s j) ↔ ¬ IsProb q := by
  constructor
  · intro hM
    obtain ⟨s, hs⟩ := hM 0
    exact (dutch_book_iff q).1 ⟨s, hs⟩
  · intro h M
    exact dutch_book_unbounded h M

/-! ### Concrete instances (non-vacuity checks) -/

/-- **Proved (concrete).** Two outcomes priced `0.6` each (total `1.2`): the bettor buying one
ticket on each is a sure win for the bookie, paying `0.2` in both outcomes. -/
theorem example_overround :
    SureWin (![3/5, 3/5] : Fin 2 → ℝ) (fun _ => 1) := by
  intro j
  unfold payoff
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- **Proved (concrete).** The fair coin `![1/2, 1/2]` admits no sure-win book at all. -/
theorem example_fair_coin : ¬ ∃ s, SureWin (![1/2, 1/2] : Fin 2 → ℝ) s := by
  rw [dutch_book_iff, not_not]
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

/-- **Proved (concrete).** Prices `![-1/10, 1/2, 1/2]` sum to `0.9` and have a negative entry,
so by the main theorem a Dutch book exists; here obtained from `dutch_book_iff`. -/
theorem example_negative_price : ∃ s, SureWin (![-1/10, 1/2, 1/2] : Fin 3 → ℝ) s := by
  rw [dutch_book_iff]
  rintro ⟨hnn, -⟩
  have := hnn 0
  norm_num at this

end A07
