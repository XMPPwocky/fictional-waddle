/-
# Bell–LaPadula and Biba are one rule on opposite orders

Subjects and objects carry levels in a preorder L. A state records which source levels each subject
holds and each object contains. `read s o` copies the object's contents into the subject; `write s o`
copies the subject's holdings into the object.

PROVED
1. `blp_flow_up`: under Bell–LaPadula (read only if level o ≤ level s, "no read up"; write only if
   level s ≤ level o, "no write down"), starting from a state where everything holds only its own level
   or below, every reachable object contains only levels ≤ its own. Information flows only upward.
2. `biba_eq_blp_dual`: the Biba rules (no read down, no write up) on L are exactly the Bell–LaPadula
   rules on the reversed order Lᵒᵈ.
3. `biba_flow_down`: hence under Biba every reachable object contains only levels ≥ its own:
   low-integrity data never reaches a high-integrity object. The proof is item 1 applied to Lᵒᵈ.
4. `write_down_leaks`: without the write rule, a two-level system leaks: a high subject reads a high
   object and writes it into a low object.
5. `isolation`: in a partial order, if every operation satisfies BOTH Bell–LaPadula and Biba (the
   policy that order reversal leaves unchanged), every reachable object contains only its own level
   and every subject only its own: nothing crosses levels.
6. `involution_split`, `involution_split_unique`: any linear involution τ (τ ∘ τ = id) on a real
   vector space splits each v uniquely as a fixed part plus a negated part:
   v = (v + τv)/2 + (v − τv)/2, with τ fixing the first and negating the second.
7. `coco_is_swap_split`: the CoCo decomposition is that split for the involution that swaps the two
   payoff labels, (A, B) ↦ (B, A): the fixed part is (coop, coop), the negated part is (comp, −comp).
8. `coco_swap`: for a two-player game with payoff matrices (A, B), the cooperative part (A + B)/2 and
   the competitive part (A − B)/2. Swapping the players (A, B) ↦ (Bᵀ, Aᵀ) transposes the cooperative
   part and negates (and transposes) the competitive part.

INTERPRETED (not formalized)
- Confidentiality and integrity are the same flow law read in opposite directions: order by secrecy and
  you get "no read up, no write down"; order by trust and you get "no write up, no read down".
- Items 5 and 7 have one shape: an order-2 symmetry, and the part it leaves fixed. For CoCo the
  fixed part is the shared payoff; for flow policies the fixed policy is isolation.
- Item 8, the full player swap (A, B) ↦ (Bᵀ, Aᵀ), transposes the shared part and negates and transposes
  the conflict part.
-/

import Mathlib

namespace LatticeFlow

structure State (Sub Obj X : Type*) where
  held : Sub → Set X
  content : Obj → Set X

inductive Op (Sub Obj : Type*)
  | read (s : Sub) (o : Obj)
  | write (s : Sub) (o : Obj)

variable {Sub Obj : Type*} [DecidableEq Sub] [DecidableEq Obj]

def apply {X : Type*} (σ : State Sub Obj X) : Op Sub Obj → State Sub Obj X
  | .read s o => { σ with held := Function.update σ.held s (σ.held s ∪ σ.content o) }
  | .write s o => { σ with content := Function.update σ.content o (σ.content o ∪ σ.held s) }

def run {X : Type*} (σ : State Sub Obj X) (ops : List (Op Sub Obj)) : State Sub Obj X :=
  ops.foldl apply σ

variable {L : Type*} [Preorder L]

/-- Bell–LaPadula: no read up, no write down. -/
def blpAllowed (ls : Sub → L) (lo : Obj → L) : Op Sub Obj → Prop
  | .read s o => lo o ≤ ls s
  | .write s o => ls s ≤ lo o

/-- Biba: no read down, no write up. -/
def bibaAllowed (ls : Sub → L) (lo : Obj → L) : Op Sub Obj → Prop
  | .read s o => ls s ≤ lo o
  | .write s o => lo o ≤ ls s

/-- Everything holds only levels at or below its own. -/
def FlowsUp (ls : Sub → L) (lo : Obj → L) (σ : State Sub Obj L) : Prop :=
  (∀ o, ∀ a ∈ σ.content o, a ≤ lo o) ∧ ∀ s, ∀ a ∈ σ.held s, a ≤ ls s

theorem step_flowsUp (ls : Sub → L) (lo : Obj → L) (σ : State Sub Obj L) (op : Op Sub Obj)
    (hσ : FlowsUp ls lo σ) (hop : blpAllowed ls lo op) : FlowsUp ls lo (apply σ op) := by
  obtain ⟨hc, hh⟩ := hσ
  cases op with
  | read s o =>
    refine ⟨hc, fun s' a ha => ?_⟩
    simp only [apply, Function.update_apply] at ha
    split_ifs at ha with h
    · subst h
      rcases ha with ha | ha
      · exact hh s' a ha
      · exact le_trans (hc o a ha) hop
    · exact hh s' a ha
  | write s o =>
    refine ⟨fun o' a ha => ?_, hh⟩
    simp only [apply, Function.update_apply] at ha
    split_ifs at ha with h
    · subst h
      rcases ha with ha | ha
      · exact hc o' a ha
      · exact le_trans (hh s a ha) hop
    · exact hc o' a ha

theorem blp_flow_up (ls : Sub → L) (lo : Obj → L) (σ : State Sub Obj L) (ops : List (Op Sub Obj))
    (hσ : FlowsUp ls lo σ) (hops : ∀ op ∈ ops, blpAllowed ls lo op) :
    FlowsUp ls lo (run σ ops) := by
  induction ops generalizing σ with
  | nil => exact hσ
  | cons op ops ih =>
    exact ih (apply σ op) (step_flowsUp ls lo σ op hσ (hops op (List.mem_cons_self ..)))
      (fun op' h => hops op' (List.mem_cons_of_mem _ h))

/-- The initial state: each object contains only its own level, subjects hold nothing. -/
def initial (lo : Obj → L) : State Sub Obj L := ⟨fun _ => ∅, fun o => {lo o}⟩

theorem initial_flowsUp (ls : Sub → L) (lo : Obj → L) : FlowsUp ls lo (initial (Sub := Sub) lo) := by
  refine ⟨fun o a ha => ?_, fun s a ha => absurd ha (Set.notMem_empty a)⟩
  rw [Set.mem_singleton_iff.mp ha]

theorem biba_eq_blp_dual (ls : Sub → L) (lo : Obj → L) (op : Op Sub Obj) :
    bibaAllowed ls lo op ↔
      blpAllowed (fun s => OrderDual.toDual (ls s)) (fun o => OrderDual.toDual (lo o)) op := by
  cases op <;> simp [bibaAllowed, blpAllowed]

theorem biba_flow_down (ls : Sub → L) (lo : Obj → L) (ops : List (Op Sub Obj))
    (hops : ∀ op ∈ ops, bibaAllowed ls lo op) :
    ∀ o, ∀ a ∈ (run (initial (Sub := Sub) (fun o => OrderDual.toDual (lo o))) ops).content o,
      lo o ≤ OrderDual.ofDual a := by
  have h := blp_flow_up (L := Lᵒᵈ) (fun s => OrderDual.toDual (ls s))
    (fun o => OrderDual.toDual (lo o)) (initial (Sub := Sub) (fun o => OrderDual.toDual (lo o))) ops
    (initial_flowsUp _ _) (fun op hop => (biba_eq_blp_dual ls lo op).mp (hops op hop))
  exact fun o a ha => OrderDual.le_toDual.mp (h.1 o a ha)

/-- Two levels, one high subject, a high and a low object: reading high then writing low leaks. -/
theorem write_down_leaks :
    let ls : Unit → Bool := fun _ => true
    let lo : Bool → Bool := id
    let ops : List (Op Unit Bool) := [.read () true, .write () false]
    (∀ op ∈ ops, match op with | .read s o => lo o ≤ ls s | .write _ _ => True) ∧
      true ∈ (run (initial (Sub := Unit) lo) ops).content false ∧ ¬ blpAllowed ls lo (.write () false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl <;> simp
  · simp [run, apply, initial]
  · simp [blpAllowed]

/-! ## The self-dual policy: Bell–LaPadula and Biba together -/

section Isolation

variable {L' : Type*} [PartialOrder L']

def Isolated (ls : Sub → L') (lo : Obj → L') (σ : State Sub Obj L') : Prop :=
  (∀ o, ∀ a ∈ σ.content o, a = lo o) ∧ ∀ s, ∀ a ∈ σ.held s, a = ls s

theorem isolation (ls : Sub → L') (lo : Obj → L') (ops : List (Op Sub Obj))
    (hops : ∀ op ∈ ops, blpAllowed ls lo op ∧ bibaAllowed ls lo op) :
    Isolated ls lo (run (initial (Sub := Sub) lo) ops) := by
  suffices h : ∀ σ : State Sub Obj L', Isolated ls lo σ → Isolated ls lo (run σ ops) by
    apply h
    exact ⟨fun o a ha => Set.mem_singleton_iff.mp ha, fun s a ha => absurd ha (Set.notMem_empty a)⟩
  induction ops with
  | nil => exact fun σ hσ => hσ
  | cons op ops ih =>
    intro σ hσ
    have hop := hops op (List.mem_cons_self ..)
    have ih' := ih (fun op' h => hops op' (List.mem_cons_of_mem _ h))
    apply ih'
    obtain ⟨hc, hh⟩ := hσ
    cases op with
    | read s o =>
      have heq : lo o = ls s := le_antisymm hop.1 hop.2
      refine ⟨hc, fun s' a ha => ?_⟩
      simp only [apply, Function.update_apply] at ha
      split_ifs at ha with h
      · subst h
        rcases ha with ha | ha
        · exact hh s' a ha
        · rw [hc o a ha, heq]
      · exact hh s' a ha
    | write s o =>
      have heq : ls s = lo o := le_antisymm hop.1 hop.2
      refine ⟨fun o' a ha => ?_, hh⟩
      simp only [apply, Function.update_apply] at ha
      split_ifs at ha with h
      · subst h
        rcases ha with ha | ha
        · exact hc o' a ha
        · rw [hh s a ha, heq]
      · exact hc o' a ha

end Isolation

/-! ## Involutions split into a fixed and a negated part -/

section Involution

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

noncomputable def fixPart (τ : W →ₗ[ℝ] W) (v : W) : W := (1 / 2 : ℝ) • (v + τ v)
noncomputable def negPart (τ : W →ₗ[ℝ] W) (v : W) : W := (1 / 2 : ℝ) • (v - τ v)

theorem involution_split (τ : W →ₗ[ℝ] W) (hτ : ∀ v, τ (τ v) = v) (v : W) :
    v = fixPart τ v + negPart τ v ∧ τ (fixPart τ v) = fixPart τ v ∧
      τ (negPart τ v) = -negPart τ v := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [fixPart, negPart, ← smul_add]
    rw [show v + τ v + (v - τ v) = (2 : ℝ) • v by rw [two_smul]; abel, smul_smul]
    norm_num
  · simp only [fixPart, map_smul, map_add, hτ]
    rw [add_comm]
  · simp only [negPart, map_smul, map_sub, hτ, ← smul_neg, neg_sub]

theorem involution_split_unique (τ : W →ₗ[ℝ] W) (hτ : ∀ v, τ (τ v) = v) (v a b : W)
    (hv : v = a + b) (ha : τ a = a) (hb : τ b = -b) : a = fixPart τ v ∧ b = negPart τ v := by
  subst hv
  have htv : τ (a + b) = a - b := by rw [map_add, ha, hb, sub_eq_add_neg]
  constructor
  · simp only [fixPart, htv]
    rw [show a + b + (a - b) = (2 : ℝ) • a by rw [two_smul]; abel, smul_smul]
    norm_num
  · simp only [negPart, htv]
    rw [show a + b - (a - b) = (2 : ℝ) • b by rw [two_smul]; abel, smul_smul]
    norm_num

end Involution

/-! ## The CoCo split under swapping players -/

open Matrix

variable {m n : Type*}

noncomputable def coop (A B : Matrix m n ℝ) : Matrix m n ℝ := (1 / 2 : ℝ) • (A + B)
noncomputable def comp (A B : Matrix m n ℝ) : Matrix m n ℝ := (1 / 2 : ℝ) • (A - B)

theorem coco_decomp (A B : Matrix m n ℝ) : A = coop A B + comp A B ∧ B = coop A B - comp A B := by
  constructor <;> ext i j <;> simp [coop, comp] <;> ring

theorem coco_swap (A B : Matrix m n ℝ) :
    coop Bᵀ Aᵀ = (coop A B)ᵀ ∧ comp Bᵀ Aᵀ = -(comp A B)ᵀ := by
  constructor <;> ext i j <;> simp [coop, comp] <;> ring

/-- Swap the two players' payoffs. -/
def payoffSwap : (Matrix m n ℝ × Matrix m n ℝ) →ₗ[ℝ] (Matrix m n ℝ × Matrix m n ℝ) where
  toFun p := (p.2, p.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coco_is_swap_split (A B : Matrix m n ℝ) :
    fixPart payoffSwap (A, B) = (coop A B, coop A B) ∧
      negPart payoffSwap (A, B) = (comp A B, -comp A B) := by
  constructor <;> ext i j <;> simp [fixPart, negPart, payoffSwap, coop, comp] <;> ring

end LatticeFlow

#print axioms LatticeFlow.blp_flow_up
#print axioms LatticeFlow.initial_flowsUp
#print axioms LatticeFlow.biba_eq_blp_dual
#print axioms LatticeFlow.biba_flow_down
#print axioms LatticeFlow.write_down_leaks
#print axioms LatticeFlow.coco_decomp
#print axioms LatticeFlow.coco_swap
#print axioms LatticeFlow.isolation
#print axioms LatticeFlow.involution_split
#print axioms LatticeFlow.involution_split_unique
#print axioms LatticeFlow.coco_is_swap_split
