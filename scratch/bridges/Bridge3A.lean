import Mathlib

/-!
# Coase with action-dependent breakdown risk

Setting of `CoaseNashTUA` (definitions repeated verbatim below): action `x : X`, transfer `t`
from party 2 to party 1, payoffs `v₁ x + t` and `v₂ x - t`, joint surplus `S x = v₁ x + v₂ x`,
disagreement payoffs `d₁, d₂`. In addition `eps : X → ℝ` with `0 < eps x ≤ 1` is the
probability that the bargain at action `x` is realised. The eps-weighted gains are
`G₁ = eps x * gain₁ v₁ d₁ x t` and `G₂ = eps x * gain₂ v₂ d₂ x t`; `IsNashEps x t` says both
are positive and their product is maximal among all `(y, s)` with both weighted gains positive.
Write `D = d₁ + d₂`.

PROVED
* `isNashEps_iff` (a): `IsNashEps x t` iff `D < S x`, `eps y * (S y - D) ≤ eps x * (S x - D)`
  for every `y` with `D < S y`, and `t = halfTransfer v₁ v₂ d₁ d₂ x` (the transfer does not
  involve `eps`).
* `isNashEps_iff_max` (b): equivalently, `x ∈ {y | D < S y}` maximizes
  `D + eps y * (S y - D)` over that set, and `t = halfTransfer v₁ v₂ d₁ d₂ x`.
* `exists_isNashEps_iff`: `(∃ t, IsNashEps x t)` iff the action condition of (a).
* `nashEpsActions_eq_of_sum_eq` (c, first part): if `d₁ + d₂ = d₁' + d₂'` then
  `{x | ∃ t, IsNashEps x t}` is the same set under `(d₁, d₂)` and `(d₁', d₂')`.
* `nashEpsActions_const` (c, second part): if `eps` is constant (with positive value) this set
  equals `{x | ∃ t, IsNash v₁ v₂ d₁ d₂ x t}`.
* `threshold_lt` (d): if `eps y < eps x` and `S x < S y` then
  `D* = (eps x * S x - eps y * S y) / (eps x - eps y) < S x`.
* `threshold_compare` (d): under the same hypotheses, for every `D`,
  `eps x * (S x - D) - eps y * (S y - D) = (eps x - eps y) * (D* - D)`; hence
  `D < D*` gives `eps y * (S y - D) < eps x * (S x - D)`, `D* < D` gives the reverse strict
  inequality, and `D = D*` gives equality.
* `not_exists_isNashEps_of_le`: if `S x ≤ D` then `x` is not the action of any `IsNashEps`
  outcome (so `y` is the only possible option in a two-action set when `S x ≤ D`).
* `instance_x_unique`, `instance_y_unique`, `instance_both`, `instance_none`: for
  `X = Act = {a, b}` with `S a = 3`, `eps a = 9/10`, `S b = 5`, `eps b = 1/2` (any `v₁, v₂`
  with these sums), `threshold = 1/2`; the set of `IsNashEps` actions is `{a}` iff `D < 1/2`,
  is `{b}` iff `1/2 < D < 5`, is `{a, b}` iff `D = 1/2`, and is empty iff `5 ≤ D`.

The hypothesis `eps x ≤ 1` is never used; only `0 < eps x` is assumed.

INTERPRETED
* Rights `(d₁, d₂)` affect the bargained action only through the total threat value
  `D = d₁ + d₂`, and with action-dependent breakdown risk they do affect it (unlike the
  `eps`-constant Coase case). A safe action `x` (high `eps`) with lower surplus wins at low
  outside options; once `D` exceeds `D*` the riskier, higher-surplus action `y` wins.
-/

namespace Bridge3A

variable {X : Type*}

/-- Joint surplus. -/
def S (v₁ v₂ : X → ℝ) (x : X) : ℝ := v₁ x + v₂ x

/-- Party 1's gain over disagreement. -/
def gain₁ (v₁ : X → ℝ) (d₁ : ℝ) (x : X) (t : ℝ) : ℝ := v₁ x + t - d₁

/-- Party 2's gain over disagreement. -/
def gain₂ (v₂ : X → ℝ) (d₂ : ℝ) (x : X) (t : ℝ) : ℝ := v₂ x - t - d₂

/-- Both parties gain strictly. -/
def Feasible (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ) (x : X) (t : ℝ) : Prop :=
  0 < gain₁ v₁ d₁ x t ∧ 0 < gain₂ v₂ d₂ x t

/-- The Nash product. -/
def nashProduct (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ) (x : X) (t : ℝ) : ℝ :=
  gain₁ v₁ d₁ x t * gain₂ v₂ d₂ x t

/-- A feasible outcome maximizing the Nash product over all feasible outcomes. -/
def IsNash (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ) (x : X) (t : ℝ) : Prop :=
  Feasible v₁ v₂ d₁ d₂ x t ∧
    ∀ y s, Feasible v₁ v₂ d₁ d₂ y s → nashProduct v₁ v₂ d₁ d₂ y s ≤ nashProduct v₁ v₂ d₁ d₂ x t

/-- The transfer splitting the gain at action `x` equally. -/
noncomputable def halfTransfer (v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ) (x : X) : ℝ :=
  (v₂ x - v₁ x + d₁ - d₂) / 2

/-- Party 1's eps-weighted gain. -/
def G₁ (eps v₁ : X → ℝ) (d₁ : ℝ) (x : X) (t : ℝ) : ℝ := eps x * gain₁ v₁ d₁ x t

/-- Party 2's eps-weighted gain. -/
def G₂ (eps v₂ : X → ℝ) (d₂ : ℝ) (x : X) (t : ℝ) : ℝ := eps x * gain₂ v₂ d₂ x t

/-- Nash solution for eps-weighted gains. -/
def IsNashEps (eps v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ) (x : X) (t : ℝ) : Prop :=
  0 < G₁ eps v₁ d₁ x t ∧ 0 < G₂ eps v₂ d₂ x t ∧
    ∀ y s, 0 < G₁ eps v₁ d₁ y s → 0 < G₂ eps v₂ d₂ y s →
      G₁ eps v₁ d₁ y s * G₂ eps v₂ d₂ y s ≤ G₁ eps v₁ d₁ x t * G₂ eps v₂ d₂ x t

/-- The threshold `D*`. -/
noncomputable def threshold (eps : X → ℝ) (Sx Sy : ℝ) (x y : X) : ℝ :=
  (eps x * Sx - eps y * Sy) / (eps x - eps y)

section General

variable (eps v₁ v₂ : X → ℝ) (d₁ d₂ : ℝ)

theorem gain_add (x : X) (t : ℝ) :
    gain₁ v₁ d₁ x t + gain₂ v₂ d₂ x t = S v₁ v₂ x - (d₁ + d₂) := by
  unfold gain₁ gain₂ S; ring

theorem gain_mul_le (x : X) (t : ℝ) :
    gain₁ v₁ d₁ x t * gain₂ v₂ d₂ x t ≤ (S v₁ v₂ x - (d₁ + d₂)) ^ 2 / 4 := by
  rw [← gain_add v₁ v₂ d₁ d₂ x t]
  nlinarith [sq_nonneg (gain₁ v₁ d₁ x t - gain₂ v₂ d₂ x t)]

theorem gain₁_half (x : X) :
    gain₁ v₁ d₁ x (halfTransfer v₁ v₂ d₁ d₂ x) = (S v₁ v₂ x - (d₁ + d₂)) / 2 := by
  unfold gain₁ halfTransfer S; ring

theorem gain₂_half (x : X) :
    gain₂ v₂ d₂ x (halfTransfer v₁ v₂ d₁ d₂ x) = (S v₁ v₂ x - (d₁ + d₂)) / 2 := by
  unfold gain₂ halfTransfer S; ring

theorem GG_half (x : X) :
    G₁ eps v₁ d₁ x (halfTransfer v₁ v₂ d₁ d₂ x) * G₂ eps v₂ d₂ x (halfTransfer v₁ v₂ d₁ d₂ x)
      = (eps x * (S v₁ v₂ x - (d₁ + d₂))) ^ 2 / 4 := by
  unfold G₁ G₂; rw [gain₁_half, gain₂_half]; ring

theorem GG_le (x : X) (t : ℝ) :
    G₁ eps v₁ d₁ x t * G₂ eps v₂ d₂ x t ≤ (eps x * (S v₁ v₂ x - (d₁ + d₂))) ^ 2 / 4 := by
  have h := gain_mul_le v₁ v₂ d₁ d₂ x t
  have e : G₁ eps v₁ d₁ x t * G₂ eps v₂ d₂ x t
      = eps x ^ 2 * (gain₁ v₁ d₁ x t * gain₂ v₂ d₂ x t) := by unfold G₁ G₂; ring
  rw [e]
  have := mul_le_mul_of_nonneg_left h (sq_nonneg (eps x))
  nlinarith

variable {eps} (hpos : ∀ x, 0 < eps x)
include hpos

theorem gains_pos {x : X} {t : ℝ} (h1 : 0 < G₁ eps v₁ d₁ x t) (h2 : 0 < G₂ eps v₂ d₂ x t) :
    0 < gain₁ v₁ d₁ x t ∧ 0 < gain₂ v₂ d₂ x t :=
  ⟨pos_of_mul_pos_right h1 (hpos x).le, pos_of_mul_pos_right h2 (hpos x).le⟩

theorem lt_S_of_G_pos {x : X} {t : ℝ} (h1 : 0 < G₁ eps v₁ d₁ x t)
    (h2 : 0 < G₂ eps v₂ d₂ x t) : d₁ + d₂ < S v₁ v₂ x := by
  obtain ⟨g1, g2⟩ := gains_pos v₁ v₂ d₁ d₂ hpos h1 h2
  have := gain_add v₁ v₂ d₁ d₂ x t
  linarith

theorem G_pos_half {x : X} (hx : d₁ + d₂ < S v₁ v₂ x) :
    0 < G₁ eps v₁ d₁ x (halfTransfer v₁ v₂ d₁ d₂ x) ∧
      0 < G₂ eps v₂ d₂ x (halfTransfer v₁ v₂ d₁ d₂ x) := by
  unfold G₁ G₂; rw [gain₁_half, gain₂_half]
  have := hpos x
  constructor <;> apply mul_pos this <;> linarith

/-- (a) Characterization of `IsNashEps`. -/
theorem isNashEps_iff (x : X) (t : ℝ) :
    IsNashEps eps v₁ v₂ d₁ d₂ x t ↔
      (d₁ + d₂ < S v₁ v₂ x ∧
        ∀ y, d₁ + d₂ < S v₁ v₂ y →
          eps y * (S v₁ v₂ y - (d₁ + d₂)) ≤ eps x * (S v₁ v₂ x - (d₁ + d₂))) ∧
        t = halfTransfer v₁ v₂ d₁ d₂ x := by
  constructor
  · rintro ⟨h1, h2, hmax⟩
    have hx := lt_S_of_G_pos v₁ v₂ d₁ d₂ hpos h1 h2
    have hex := hpos x
    have bx : 0 < eps x * (S v₁ v₂ x - (d₁ + d₂)) := mul_pos hex (by linarith)
    have hup := GG_le eps v₁ v₂ d₁ d₂ x t
    refine ⟨⟨hx, fun y hy => ?_⟩, ?_⟩
    · obtain ⟨p1, p2⟩ := G_pos_half v₁ v₂ d₁ d₂ hpos hy
      have hle := hmax y _ p1 p2
      rw [GG_half] at hle
      have ay : 0 < eps y * (S v₁ v₂ y - (d₁ + d₂)) := mul_pos (hpos y) (by linarith)
      nlinarith
    · obtain ⟨p1, p2⟩ := G_pos_half v₁ v₂ d₁ d₂ hpos hx
      have hle := hmax x _ p1 p2
      rw [GG_half] at hle
      have hs := gain_add v₁ v₂ d₁ d₂ x t
      have e : G₁ eps v₁ d₁ x t * G₂ eps v₂ d₂ x t
          = eps x ^ 2 * (gain₁ v₁ d₁ x t * gain₂ v₂ d₂ x t) := by unfold G₁ G₂; ring
      rw [e] at hle
      have hsq : eps x ^ 2 * (gain₁ v₁ d₁ x t - gain₂ v₂ d₂ x t) ^ 2 = 0 := by
        have : eps x ^ 2 * (gain₁ v₁ d₁ x t - gain₂ v₂ d₂ x t) ^ 2
            = (eps x * (S v₁ v₂ x - (d₁ + d₂))) ^ 2
              - 4 * (eps x ^ 2 * (gain₁ v₁ d₁ x t * gain₂ v₂ d₂ x t)) := by
          rw [← hs]; ring
        rw [this]
        nlinarith [mul_nonneg (sq_nonneg (eps x)) (sq_nonneg (gain₁ v₁ d₁ x t - gain₂ v₂ d₂ x t))]
      have hne : eps x ^ 2 ≠ 0 := by positivity
      have h0 : (gain₁ v₁ d₁ x t - gain₂ v₂ d₂ x t) ^ 2 = 0 :=
        (mul_eq_zero.1 hsq).resolve_left hne
      have heq : gain₁ v₁ d₁ x t = gain₂ v₂ d₂ x t := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
        linarith
      unfold gain₁ gain₂ at heq
      unfold halfTransfer
      linarith
  · rintro ⟨⟨hx, hmax⟩, rfl⟩
    obtain ⟨p1, p2⟩ := G_pos_half v₁ v₂ d₁ d₂ hpos hx
    refine ⟨p1, p2, fun y s q1 q2 => ?_⟩
    have hy := lt_S_of_G_pos v₁ v₂ d₁ d₂ hpos q1 q2
    have h1 := GG_le eps v₁ v₂ d₁ d₂ y s
    have h2 := hmax y hy
    rw [GG_half]
    have ay : 0 < eps y * (S v₁ v₂ y - (d₁ + d₂)) := mul_pos (hpos y) (by linarith)
    have : (eps y * (S v₁ v₂ y - (d₁ + d₂))) ^ 2 ≤ (eps x * (S v₁ v₂ x - (d₁ + d₂))) ^ 2 :=
      pow_le_pow_left₀ ay.le h2 2
    linarith

/-- (b) Equivalent maximization form. -/
theorem isNashEps_iff_max (x : X) (t : ℝ) :
    IsNashEps eps v₁ v₂ d₁ d₂ x t ↔
      (x ∈ {y | d₁ + d₂ < S v₁ v₂ y} ∧
        ∀ y ∈ {y | d₁ + d₂ < S v₁ v₂ y},
          (d₁ + d₂) + eps y * (S v₁ v₂ y - (d₁ + d₂))
            ≤ (d₁ + d₂) + eps x * (S v₁ v₂ x - (d₁ + d₂))) ∧
        t = halfTransfer v₁ v₂ d₁ d₂ x := by
  rw [isNashEps_iff v₁ v₂ d₁ d₂ hpos]
  simp only [Set.mem_ofPred_eq, add_le_add_iff_left]

theorem exists_isNashEps_iff (x : X) :
    (∃ t, IsNashEps eps v₁ v₂ d₁ d₂ x t) ↔
      d₁ + d₂ < S v₁ v₂ x ∧
        ∀ y, d₁ + d₂ < S v₁ v₂ y →
          eps y * (S v₁ v₂ y - (d₁ + d₂)) ≤ eps x * (S v₁ v₂ x - (d₁ + d₂)) := by
  constructor
  · rintro ⟨t, ht⟩
    exact ((isNashEps_iff v₁ v₂ d₁ d₂ hpos x t).1 ht).1
  · intro h
    exact ⟨_, (isNashEps_iff v₁ v₂ d₁ d₂ hpos x _).2 ⟨h, rfl⟩⟩

theorem not_exists_isNashEps_of_le {x : X} (hx : S v₁ v₂ x ≤ d₁ + d₂) :
    ¬ ∃ t, IsNashEps eps v₁ v₂ d₁ d₂ x t := by
  rw [exists_isNashEps_iff v₁ v₂ d₁ d₂ hpos]
  rintro ⟨h, -⟩
  linarith

/-- (c) The set of `IsNashEps` actions depends on `(d₁, d₂)` only through `d₁ + d₂`. -/
theorem nashEpsActions_eq_of_sum_eq (d₁' d₂' : ℝ) (hD : d₁ + d₂ = d₁' + d₂') :
    {x | ∃ t, IsNashEps eps v₁ v₂ d₁ d₂ x t} = {x | ∃ t, IsNashEps eps v₁ v₂ d₁' d₂' x t} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [exists_isNashEps_iff v₁ v₂ d₁ d₂ hpos, exists_isNashEps_iff v₁ v₂ d₁' d₂' hpos, hD]

omit hpos in
theorem exists_isNash_iff (x : X) :
    (∃ t, IsNash v₁ v₂ d₁ d₂ x t) ↔
      d₁ + d₂ < S v₁ v₂ x ∧ ∀ y, d₁ + d₂ < S v₁ v₂ y → S v₁ v₂ y ≤ S v₁ v₂ x := by
  have hc : ∀ y s, IsNashEps (fun _ => (1 : ℝ)) v₁ v₂ d₁ d₂ y s ↔ IsNash v₁ v₂ d₁ d₂ y s := by
    intro y s
    unfold IsNashEps IsNash Feasible nashProduct G₁ G₂
    simp only [one_mul]
    constructor
    · rintro ⟨a, b, c⟩
      exact ⟨⟨a, b⟩, fun z r ⟨u, w⟩ => c z r u w⟩
    · rintro ⟨⟨a, b⟩, c⟩
      exact ⟨a, b, fun z r u w => c z r ⟨u, w⟩⟩
  simp only [← hc]
  rw [exists_isNashEps_iff v₁ v₂ d₁ d₂ (fun _ => one_pos)]
  constructor
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, fun y hy => by have := hmax y hy; linarith⟩
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, fun y hy => by have := hmax y hy; linarith⟩

omit hpos in
/-- (c) With constant `eps`, the `IsNashEps` actions are the `IsNash` actions. -/
theorem nashEpsActions_const (c : ℝ) (hc : 0 < c) :
    {x | ∃ t, IsNashEps (fun _ => c) v₁ v₂ d₁ d₂ x t} = {x | ∃ t, IsNash v₁ v₂ d₁ d₂ x t} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [exists_isNashEps_iff v₁ v₂ d₁ d₂ (fun _ => hc), exists_isNash_iff]
  constructor
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, fun y hy => le_of_mul_le_mul_left (by have := hmax y hy; linarith) hc⟩
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, fun y hy => by have := hmax y hy; nlinarith⟩

end General

section Threshold

variable {eps : X → ℝ} (hpos : ∀ x, 0 < eps x)
include hpos

/-- (d) `D* < S x`. -/
theorem threshold_lt {x y : X} {Sx Sy : ℝ} (he : eps y < eps x) (hS : Sx < Sy) :
    threshold eps Sx Sy x y < Sx := by
  unfold threshold
  have hd : 0 < eps x - eps y := by linarith
  rw [div_lt_iff₀ hd]
  have := hpos y
  nlinarith

omit hpos in
theorem threshold_identity {x y : X} {Sx Sy : ℝ} (he : eps y < eps x) (D : ℝ) :
    eps x * (Sx - D) - eps y * (Sy - D) = (eps x - eps y) * (threshold eps Sx Sy x y - D) := by
  unfold threshold
  have hd : eps x - eps y ≠ 0 := by linarith
  field_simp
  ring

omit hpos in
/-- (d) The comparison flips at `D*`. -/
theorem threshold_compare {x y : X} {Sx Sy : ℝ} (he : eps y < eps x) (D : ℝ) :
    (D < threshold eps Sx Sy x y → eps y * (Sy - D) < eps x * (Sx - D)) ∧
      (threshold eps Sx Sy x y < D → eps x * (Sx - D) < eps y * (Sy - D)) ∧
      (D = threshold eps Sx Sy x y → eps x * (Sx - D) = eps y * (Sy - D)) := by
  have e := threshold_identity he (Sx := Sx) (Sy := Sy) D
  have hd : 0 < eps x - eps y := by linarith
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have : 0 < (eps x - eps y) * (threshold eps Sx Sy x y - D) := mul_pos hd (by linarith)
    linarith
  · have : (eps x - eps y) * (threshold eps Sx Sy x y - D) < 0 :=
      mul_neg_of_pos_of_neg hd (by linarith)
    linarith
  · subst h
    rw [sub_self, mul_zero] at e
    linarith

end Threshold

section Instance

/-- Two actions. -/
inductive Act
  | a
  | b
  deriving DecidableEq

open Act

/-- `eps a = 9/10`, `eps b = 1/2`. -/
noncomputable def epsI : Act → ℝ
  | a => 9 / 10
  | b => 1 / 2

theorem epsI_pos : ∀ z, 0 < epsI z := by
  intro z; cases z <;> norm_num [epsI]

theorem threshold_instance : threshold epsI 3 5 a b = 1 / 2 := by
  norm_num [threshold, epsI]

variable (v₁ v₂ : Act → ℝ) (hSa : S v₁ v₂ a = 3) (hSb : S v₁ v₂ b = 5) (d₁ d₂ : ℝ)
include hSa hSb

theorem mem_a_iff :
    (∃ t, IsNashEps epsI v₁ v₂ d₁ d₂ a t) ↔ d₁ + d₂ ≤ 1 / 2 := by
  rw [exists_isNashEps_iff v₁ v₂ d₁ d₂ epsI_pos]
  constructor
  · rintro ⟨ha, h⟩
    rw [hSa] at ha
    by_contra hc
    push Not at hc
    have := h b (by rw [hSb]; linarith)
    rw [hSa, hSb] at this
    norm_num [epsI] at this
    linarith
  · intro hD
    refine ⟨by rw [hSa]; linarith, fun y _ => ?_⟩
    cases y
    · exact le_rfl
    · rw [hSa, hSb]; norm_num [epsI]; linarith

theorem mem_b_iff :
    (∃ t, IsNashEps epsI v₁ v₂ d₁ d₂ b t) ↔ 1 / 2 ≤ d₁ + d₂ ∧ d₁ + d₂ < 5 := by
  rw [exists_isNashEps_iff v₁ v₂ d₁ d₂ epsI_pos]
  constructor
  · rintro ⟨hb, h⟩
    rw [hSb] at hb
    refine ⟨?_, hb⟩
    by_contra hc
    push Not at hc
    have := h a (by rw [hSa]; linarith)
    rw [hSa, hSb] at this
    norm_num [epsI] at this
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [hSb]; linarith, fun y _ => ?_⟩
    cases y
    · rw [hSa, hSb]; norm_num [epsI]; linarith
    · exact le_rfl

/-- `a` is the unique `IsNashEps` action iff `D < 1/2`. -/
theorem instance_x_unique :
    {z | ∃ t, IsNashEps epsI v₁ v₂ d₁ d₂ z t} = {a} ↔ d₁ + d₂ < 1 / 2 := by
  have ha := mem_a_iff v₁ v₂ hSa hSb d₁ d₂
  have hb := mem_b_iff v₁ v₂ hSa hSb d₁ d₂
  constructor
  · intro h
    have h1 : a ∈ {z | ∃ t, IsNashEps epsI v₁ v₂ d₁ d₂ z t} := by rw [h]; rfl
    have h2 : b ∉ {z | ∃ t, IsNashEps epsI v₁ v₂ d₁ d₂ z t} := by rw [h]; simp
    simp only [Set.mem_ofPred_eq] at h1 h2
    rw [ha] at h1; rw [hb] at h2
    push Not at h2
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exact absurd (h2 h.ge) (by linarith)
  · intro hD
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    cases z
    · simp only [iff_true]; exact ha.2 hD.le
    · rw [hb]; simp only [reduceCtorEq, iff_false, not_and, not_lt]; intro h; linarith

/-- `b` is the unique `IsNashEps` action iff `1/2 < D < 5`. -/
theorem instance_y_unique :
    {z | ∃ t, IsNashEps epsI v₁ v₂ d₁ d₂ z t} = {b} ↔ 1 / 2 < d₁ + d₂ ∧ d₁ + d₂ < 5 := by
  have ha := mem_a_iff v₁ v₂ hSa hSb d₁ d₂
  have hb := mem_b_iff v₁ v₂ hSa hSb d₁ d₂
  constructor
  · intro h
    have h1 : b ∈ {z | ∃ t, IsNashEps epsI v₁ v₂ d₁ d₂ z t} := by rw [h]; rfl
    have h2 : a ∉ {z | ∃ t, IsNashEps epsI v₁ v₂ d₁ d₂ z t} := by rw [h]; simp
    simp only [Set.mem_ofPred_eq] at h1 h2
    rw [hb] at h1; rw [ha] at h2
    push Not at h2
    exact ⟨h2, h1.2⟩
  · rintro ⟨h1, h2⟩
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    cases z
    · rw [ha]; simp only [reduceCtorEq, iff_false, not_le]; exact h1
    · simp only [iff_true]; exact hb.2 ⟨h1.le, h2⟩

/-- Both actions are `IsNashEps` actions iff `D = 1/2`. -/
theorem instance_both :
    {z | ∃ t, IsNashEps epsI v₁ v₂ d₁ d₂ z t} = Set.univ ↔ d₁ + d₂ = 1 / 2 := by
  have ha := mem_a_iff v₁ v₂ hSa hSb d₁ d₂
  have hb := mem_b_iff v₁ v₂ hSa hSb d₁ d₂
  constructor
  · intro h
    have h1 : a ∈ {z | ∃ t, IsNashEps epsI v₁ v₂ d₁ d₂ z t} := by rw [h]; trivial
    have h2 : b ∈ {z | ∃ t, IsNashEps epsI v₁ v₂ d₁ d₂ z t} := by rw [h]; trivial
    simp only [Set.mem_ofPred_eq] at h1 h2
    rw [ha] at h1; rw [hb] at h2
    linarith [h2.1]
  · intro hD
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    cases z
    · exact ha.2 hD.le
    · exact hb.2 ⟨hD.ge, by linarith⟩

/-- No `IsNashEps` action exists iff `5 ≤ D`. -/
theorem instance_none :
    {z | ∃ t, IsNashEps epsI v₁ v₂ d₁ d₂ z t} = ∅ ↔ 5 ≤ d₁ + d₂ := by
  have ha := mem_a_iff v₁ v₂ hSa hSb d₁ d₂
  have hb := mem_b_iff v₁ v₂ hSa hSb d₁ d₂
  constructor
  · intro h
    have h1 : a ∉ {z | ∃ t, IsNashEps epsI v₁ v₂ d₁ d₂ z t} := by rw [h]; simp
    have h2 : b ∉ {z | ∃ t, IsNashEps epsI v₁ v₂ d₁ d₂ z t} := by rw [h]; simp
    simp only [Set.mem_ofPred_eq] at h1 h2
    rw [ha] at h1; rw [hb] at h2
    push Not at h1 h2
    exact h2 h1.le
  · intro hD
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    cases z
    · rw [ha]; linarith
    · rw [hb]; rintro ⟨-, h⟩; linarith

end Instance

end Bridge3A
