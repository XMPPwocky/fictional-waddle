import Mathlib

/-!
# Bell–LaPadula, Biba, taint creep and robust declassification

Information-flow model: subjects carry a taint set (the labels of everything they have read), objects carry the
labels of everything written into them. A read merges the object's taint into the subject; a write merges the
subject's taint into the object.

PROVED:
* `step_inv`, `trace_inv`, `basic_security`: if every read satisfies simple security (no read up) and every write
  satisfies the star property against the subject's whole taint (no write down), then after any trace from the
  initial state every label found in an object is at most that object's label. `no_flow_down`: information from
  an object never reaches an object whose label is not above it.
* `biba`: the same theorem in the order dual is Biba's integrity model (no read down, no write up): everything
  that has influenced an object has integrity at least the object's. The rules unfold to Biba's (`biba_read_rule`,
  `biba_write_rule`).
* `basic_security_reads_free`: object safety survives with NO read restriction, as long as writes are checked
  against the accumulated taint (high-water / low-water mark).
* `taint_mono_run`, `read_once_bound`: taint only grows, so once a subject has read something at label `h`, every
  later write it is allowed must go to a label at least `h`. One context window that reads everything loses write
  authority monotonically.
* `separated_robust`: a release function whose choice of what to reveal depends only on trusted input is robust
  against attacker input. `steered_not_robust`: a release whose selector is attacker-controlled is not, and
  `steered_reveals` shows the attacker can extract any field.
INTERPRETED (not formalized): subjects as model contexts, prompt injection as attacker-controlled selection, the
dual-LLM / CaMeL split as `separated_robust`; covert channels are outside this model.
-/

namespace InfoFlow

structure Sys (S O L : Type*) where
  clr : S → L
  lab : O → L

structure St (S O L : Type*) where
  ts : S → Set L
  tobj : O → Set L

inductive Op (S O : Type*) where
  | read : S → O → Op S O
  | write : S → O → Op S O

variable {S O L : Type*} [DecidableEq S] [DecidableEq O]

def step (st : St S O L) : Op S O → St S O L
  | .read s o => ⟨Function.update st.ts s (st.ts s ∪ st.tobj o), st.tobj⟩
  | .write s o => ⟨st.ts, Function.update st.tobj o (st.tobj o ∪ st.ts s)⟩

def run (st : St S O L) : List (Op S O) → St S O L
  | [] => st
  | op :: ops => run (step st op) ops

section Lattice
variable [Preorder L]

def allowed (sys : Sys S O L) (st : St S O L) : Op S O → Prop
  | .read s o => sys.lab o ≤ sys.clr s
  | .write s o => ∀ x ∈ st.ts s, x ≤ sys.lab o

def okTrace (sys : Sys S O L) : St S O L → List (Op S O) → Prop
  | _, [] => True
  | st, op :: ops => allowed sys st op ∧ okTrace sys (step st op) ops

abbrev ObjInv (sys : Sys S O L) (st : St S O L) : Prop := ∀ o, ∀ x ∈ st.tobj o, x ≤ sys.lab o
abbrev SubjInv (sys : Sys S O L) (st : St S O L) : Prop := ∀ s, ∀ x ∈ st.ts s, x ≤ sys.clr s
abbrev Inv (sys : Sys S O L) (st : St S O L) : Prop := ObjInv sys st ∧ SubjInv sys st

def init (sys : Sys S O L) : St S O L := ⟨fun _ => ∅, fun o => {sys.lab o}⟩

theorem init_inv (sys : Sys S O L) : Inv sys (init sys) := by
  refine ⟨fun o x hx => ?_, fun s x hx => ?_⟩
  · simp only [init, Set.mem_singleton_iff] at hx; exact hx ▸ le_rfl
  · simp [init] at hx

theorem step_inv {sys : Sys S O L} {st : St S O L} {op : Op S O} (h : Inv sys st)
    (ha : allowed sys st op) : Inv sys (step st op) := by
  obtain ⟨ho, hs⟩ := h
  cases op with
  | read s o =>
    simp only [allowed] at ha
    refine ⟨fun o' x hx => ho o' x hx, fun s' x hx => ?_⟩
    simp only [step] at hx
    rw [Function.update_apply] at hx
    split_ifs at hx with hss
    · subst hss
      rcases hx with hx | hx
      · exact hs _ x hx
      · exact le_trans (ho o x hx) ha
    · exact hs s' x hx
  | write s o =>
    simp only [allowed] at ha
    refine ⟨fun o' x hx => ?_, fun s' x hx => hs s' x hx⟩
    simp only [step] at hx
    rw [Function.update_apply] at hx
    split_ifs at hx with hoo
    · subst hoo
      rcases hx with hx | hx
      · exact ho _ x hx
      · exact ha x hx
    · exact ho o' x hx

theorem trace_inv {sys : Sys S O L} :
    ∀ (ops : List (Op S O)) (st : St S O L), Inv sys st → okTrace sys st ops → Inv sys (run st ops)
  | [], _, h, _ => h
  | _ :: ops, _, h, ⟨ha, ht⟩ => trace_inv ops _ (step_inv h ha) ht

/-- **Basic security theorem.** -/
theorem basic_security (sys : Sys S O L) (ops : List (Op S O)) (hok : okTrace sys (init sys) ops)
    (o : O) (h : L) (hh : h ∈ (run (init sys) ops).tobj o) : h ≤ sys.lab o :=
  (trace_inv ops _ (init_inv sys) hok).1 o h hh

theorem no_flow_down (sys : Sys S O L) (ops : List (Op S O)) (hok : okTrace sys (init sys) ops)
    (o o' : O) (hlt : ¬ sys.lab o ≤ sys.lab o') : sys.lab o ∉ (run (init sys) ops).tobj o' :=
  fun hm => hlt (basic_security sys ops hok o' _ hm)

/-! Reads unrestricted, writes checked against accumulated taint. -/

def allowedW (sys : Sys S O L) (st : St S O L) : Op S O → Prop
  | .read _ _ => True
  | .write s o => ∀ x ∈ st.ts s, x ≤ sys.lab o

def okTraceW (sys : Sys S O L) : St S O L → List (Op S O) → Prop
  | _, [] => True
  | st, op :: ops => allowedW sys st op ∧ okTraceW sys (step st op) ops

theorem stepW_obj {sys : Sys S O L} {st : St S O L} {op : Op S O} (h : ObjInv sys st)
    (ha : allowedW sys st op) : ObjInv sys (step st op) := by
  cases op with
  | read s o => exact fun o' x hx => h o' x hx
  | write s o =>
    simp only [allowedW] at ha
    intro o' x hx
    simp only [step] at hx
    rw [Function.update_apply] at hx
    split_ifs at hx with hoo
    · subst hoo
      rcases hx with hx | hx
      · exact h _ x hx
      · exact ha x hx
    · exact h o' x hx

theorem traceW_obj {sys : Sys S O L} :
    ∀ (ops : List (Op S O)) (st : St S O L), ObjInv sys st → okTraceW sys st ops → ObjInv sys (run st ops)
  | [], _, h, _ => h
  | _ :: ops, _, h, ⟨ha, ht⟩ => traceW_obj ops _ (stepW_obj h ha) ht

theorem basic_security_reads_free (sys : Sys S O L) (ops : List (Op S O))
    (hok : okTraceW sys (init sys) ops) (o : O) (h : L) (hh : h ∈ (run (init sys) ops).tobj o) :
    h ≤ sys.lab o :=
  traceW_obj ops _ (init_inv sys).1 hok o h hh

end Lattice

/-! Taint creep. -/

theorem taint_mono (st : St S O L) (op : Op S O) (s : S) : st.ts s ⊆ (step st op).ts s := by
  cases op with
  | read s' o =>
    intro x hx
    show x ∈ Function.update st.ts s' (st.ts s' ∪ st.tobj o) s
    rw [Function.update_apply]
    split_ifs with h
    · subst h; exact Or.inl hx
    · exact hx
  | write s' o => exact fun x hx => hx

theorem taint_mono_run : ∀ (ops : List (Op S O)) (st : St S O L) (s : S), st.ts s ⊆ (run st ops).ts s
  | [], _, _ => fun _ hx => hx
  | op :: ops, st, s => fun x hx => taint_mono_run ops (step st op) s (taint_mono st op s hx)

theorem read_once_bound [Preorder L] (sys : Sys S O L) (ops : List (Op S O)) (st : St S O L) (s : S) (o : O)
    (h : L) (hh : h ∈ st.ts s) (hw : allowed sys (run st ops) (.write s o)) : h ≤ sys.lab o :=
  hw h (taint_mono_run ops st s hh)

/-! Biba is Bell–LaPadula in the order dual. -/

section Biba
variable [Preorder L]

theorem biba_read_rule (sys : Sys S O Lᵒᵈ) (st : St S O Lᵒᵈ) (s : S) (o : O) :
    allowed sys st (.read s o) ↔ OrderDual.ofDual (sys.clr s) ≤ OrderDual.ofDual (sys.lab o) := Iff.rfl

theorem biba_write_rule (sys : Sys S O Lᵒᵈ) (st : St S O Lᵒᵈ) (s : S) (o : O) :
    allowed sys st (.write s o) ↔ ∀ x ∈ st.ts s, OrderDual.ofDual (sys.lab o) ≤ OrderDual.ofDual x := Iff.rfl

theorem biba (sys : Sys S O Lᵒᵈ) (ops : List (Op S O)) (hok : okTrace sys (init sys) ops)
    (o : O) (h : Lᵒᵈ) (hh : h ∈ (run (init sys) ops).tobj o) :
    OrderDual.ofDual (sys.lab o) ≤ OrderDual.ofDual h :=
  basic_security sys ops hok o h hh

end Biba

/-! Robust declassification. -/

def RobustAgainst {Sec T A Out : Type*} (d : Sec → T → A → Out) : Prop :=
  ∀ (t : T) (a a' : A) (s s' : Sec), (d s t a = d s' t a ↔ d s t a' = d s' t a')

theorem separated_robust {Sec T A Out : Type*} (rel : T → Sec → Out) :
    RobustAgainst (fun (s : Sec) (t : T) (_ : A) => rel t s) :=
  fun _ _ _ _ _ => Iff.rfl

def steered : (Fin 2 → Bool) → Unit → Fin 2 → Bool := fun s _ i => s i

theorem steered_reveals (s s' : Fin 2 → Bool) (i : Fin 2) (hi : s i ≠ s' i) :
    steered s () i ≠ steered s' () i := hi

theorem steered_not_robust : ¬ RobustAgainst steered := by
  intro h
  have h2 := (h () 0 1 (fun _ => false) (fun i => decide (i = 0))).2 (by decide)
  exact absurd h2 (by decide)

end InfoFlow
