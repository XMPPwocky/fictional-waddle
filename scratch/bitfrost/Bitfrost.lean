/-
# Bitfrost, four mechanisms as small models

From Krstić and Garfinkel, "Bitfrost: the One Laptop per Child Security Model" (SOUPS 2007).
Time is ℕ.

PROVED
1. No prompts. `requests_change_nothing`: if the only events are programs asking, the permission
   table never changes; grants come only from the Security Center. `denied_stays_denied`: a program
   that starts without a permission still lacks it after asking any number of times.
2. Key continuity. `impostor_detected`: once a name is bound to a key, a different key under that
   name gets a warning. `first_use_blind`: at first contact, any two keys get the same verdict, so
   the one attack key continuity cannot see is the first meeting.
3. Activation leases. `cut_off_unusable`: if every renewal happened by time r, the laptop is
   unusable from r + L on (L = lease length). `renewal_usable`: a renewal at s makes it usable
   on [s, s + L).
4. Developer key delay. `urgent_request_fails`: a key requested at t₀ with delay D is unavailable
   at every time before t₀ + D, so an attack that needs the key within a window shorter than D fails.

INTERPRETED (not formalized)
- `cut_off_unusable` never says why renewals stopped. The same theorem that disables a stolen laptop
  disables any laptop whose server stops renewing it: the anti-theft mechanism is also a kill switch
  for whoever runs the server.
- Key continuity binds identity across time without a certificate authority: a name means "the same
  key as before", which is identity as continuity.
-/

import Mathlib

namespace Bitfrost

/-! ## 1. No prompts -/

inductive Event (P R : Type*)
  | request (p : P) (r : R)
  | grant (p : P) (r : R)

def IsRequest {P R : Type*} : Event P R → Prop
  | .request _ _ => True
  | .grant _ _ => False

def step {P R : Type*} [DecidableEq P] (g : P → Set R) : Event P R → P → Set R
  | .request _ _ => g
  | .grant p r => Function.update g p (insert r (g p))

def run {P R : Type*} [DecidableEq P] (g : P → Set R) (es : List (Event P R)) : P → Set R :=
  es.foldl step g

theorem requests_change_nothing {P R : Type*} [DecidableEq P] (g : P → Set R)
    (es : List (Event P R)) (h : ∀ e ∈ es, IsRequest e) : run g es = g := by
  induction es generalizing g with
  | nil => rfl
  | cons e es ih =>
    have he := h e (List.mem_cons_self ..)
    have hrest : ∀ e' ∈ es, IsRequest e' := fun e' he' => h e' (List.mem_cons_of_mem _ he')
    cases e with
    | request p r =>
      show run (step g (.request p r)) es = g
      exact ih g hrest
    | grant p r => exact absurd he id

theorem denied_stays_denied {P R : Type*} [DecidableEq P] (g : P → Set R) (p : P) (r : R)
    (hden : r ∉ g p) (es : List (Event P R)) (h : ∀ e ∈ es, IsRequest e) :
    r ∉ run g es p := by
  rw [requests_change_nothing g es h]
  exact hden

/-! ## 2. Key continuity -/

inductive Verdict
  | firstUse
  | same
  | warn

def check {N K : Type*} [DecidableEq K] (store : N → Option K) (n : N) (k : K) : Verdict :=
  match store n with
  | none => .firstUse
  | some k' => if k' = k then .same else .warn

theorem impostor_detected {N K : Type*} [DecidableEq K] (store : N → Option K) (n : N)
    (k k' : K) (hs : store n = some k) (hne : k' ≠ k) : check store n k' = .warn := by
  have : k ≠ k' := fun e => hne e.symm
  simp [check, hs, this]

theorem first_use_blind {N K : Type*} [DecidableEq K] (store : N → Option K) (n : N)
    (k k' : K) (hs : store n = none) : check store n k = check store n k' := by
  simp [check, hs]

/-! ## 3. Activation leases -/

def usable (L : ℕ) (renewals : Finset ℕ) (t : ℕ) : Prop :=
  ∃ s ∈ renewals, s ≤ t ∧ t < s + L

theorem cut_off_unusable (L r : ℕ) (renewals : Finset ℕ) (h : ∀ s ∈ renewals, s ≤ r)
    (t : ℕ) (ht : r + L ≤ t) : ¬ usable L renewals t := by
  rintro ⟨s, hs, _, hlt⟩
  have := h s hs
  omega

theorem renewal_usable (L : ℕ) (renewals : Finset ℕ) (s t : ℕ) (hs : s ∈ renewals)
    (h1 : s ≤ t) (h2 : t < s + L) : usable L renewals t :=
  ⟨s, hs, h1, h2⟩

/-! ## 4. Developer key delay -/

def keyAvailable (t₀ D t : ℕ) : Prop := t₀ + D ≤ t

theorem urgent_request_fails (t₀ D W : ℕ) (hW : W ≤ D) (t : ℕ) (ht : t < t₀ + W) :
    ¬ keyAvailable t₀ D t := by
  unfold keyAvailable
  omega

end Bitfrost

#print axioms Bitfrost.requests_change_nothing
#print axioms Bitfrost.denied_stays_denied
#print axioms Bitfrost.impostor_detected
#print axioms Bitfrost.first_use_blind
#print axioms Bitfrost.cut_off_unusable
#print axioms Bitfrost.renewal_usable
#print axioms Bitfrost.urgent_request_fails
