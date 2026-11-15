import ProteinFolding.Common.TM2ProductMap
import ProteinFolding.Common.TM2RenamingExtra

/-! A finite controller for bounded stateful iteration. Its input is an
encoded state and a unary iteration count. Each round runs the actual child
transition machine, collecting its entire output as the next state. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.Iterate

open Computability Turing TM2

noncomputable section

variable {A : Type} {ea : FinEncoding A} {f : A → A}
variable (h : TM2ComputableInPolyTime ea ea f) [Inhabited ea.Γ]

abbrev InputSymbol := PairSymbol ea.Γ Bool

inductive Extra where
  | input | buffer | remaining | output
  deriving DecidableEq, Fintype

inductive Phase where
  | readState | readCount | loop | prepare | collect | finish | done
  deriving DecidableEq, Fintype

abbrev Stack := h.tm.K ⊕ Extra
abbrev Label := h.tm.Λ ⊕ Phase
abbrev Control := Option ea.Γ × Bool
abbrev State := h.tm.σ × Control (ea := ea)

def ExtraAlphabet : Extra → Type
  | .input => InputSymbol (ea := ea)
  | .buffer | .output => ea.Γ
  | .remaining => Unit

abbrev Alphabet := Sum.elim h.tm.Γ (ExtraAlphabet (ea := ea))

structure Data where
  input : List (InputSymbol (ea := ea))
  buffer : List ea.Γ
  remaining : ℕ
  output : List ea.Γ

def extraContents (d : Data (ea := ea)) : ∀ k, List (ExtraAlphabet (ea := ea) k)
  | .input => d.input
  | .buffer => d.buffer
  | .remaining => List.replicate d.remaining ()
  | .output => d.output

def contents (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea)) :
    ∀ k, List (Alphabet h k) := TM2Embedding.joinStacks S (extraContents d)

def emptyStacks : ∀ k, List (h.tm.Γ k) := fun _ => []
def oneStack (k : h.tm.K) (w : List (h.tm.Γ k)) : ∀ j, List (h.tm.Γ j) :=
  Function.update (emptyStacks h) k w

def initialState : State h := (h.tm.initialState, (none, false))
def clearControl (st : State h) : State h := (st.1, (none, false))

def cfg (l : Label h) (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea)) :
    Cfg (Alphabet h) (Label h) (State h) := ⟨some l, initialState h, contents h S d⟩

def transferEquiv : ((h.tm.σ × Bool) × Option ea.Γ) ≃ State h where
  toFun st := (st.1.1, (st.2, st.1.2))
  invFun st := ((st.1, st.2.2), st.2.1)
  left_inv st := by obtain ⟨⟨s, b⟩, r⟩ := st; rfl
  right_inv st := by obtain ⟨s, r, b⟩ := st; rfl

def leftHead : Option (InputSymbol (ea := ea)) → Option ea.Γ
  | some (.left a) => some a
  | _ => none

instance : Inhabited (Alphabet h (.inr .buffer)) := ⟨(default : ea.Γ)⟩

def program : Label h → Stmt (Alphabet h) (Label h) (State h)
  | .inl l => TM2Embedding.liftStmt Sum.inl (some (.inr .collect)) (h.tm.m l)
  | .inr .readState => .pop (.inr .input) (fun st head => (st.1, (leftHead head, false)))
    (.branch (fun st => st.2.1.isSome)
      (.push (.inr .buffer) (fun st => st.2.1.getD default)
        (.load (clearControl h) (.goto (fun _ => .inr .readState))))
      (.load (clearControl h) (.goto (fun _ => .inr .readCount))))
  | .inr .readCount => .pop (.inr .input) (fun st head => (st.1, (none, head.isSome)))
    (.branch (fun st => st.2.2)
      (.push (.inr .remaining) (fun _ => ())
        (.load (clearControl h) (.goto (fun _ => .inr .readCount))))
      (.load (clearControl h) (.goto (fun _ => .inr .loop))))
  | .inr .loop => .pop (.inr .remaining) (fun st head => (st.1, (none, head.isSome)))
    (.branch (fun st => st.2.2)
      (.load (clearControl h) (.goto (fun _ => .inr .prepare)))
      (.load (clearControl h) (.goto (fun _ => .inr .finish))))
  | .inr .prepare => TM2Renaming.relabelStmt (transferEquiv h)
    (TM2Transfer.transferStmt (Γ := Alphabet h) (σ := h.tm.σ × Bool)
      (.inr .buffer) (.inl h.tm.k₀) h.inputAlphabet.symm (.inr .prepare) (.inl h.tm.main))
  | .inr .collect => .pop (.inl h.tm.k₁) (fun st head => (st.1, (head.map h.outputAlphabet, false)))
    (.branch (fun st => st.2.1.isSome)
      (.push (.inr .buffer) (fun st => st.2.1.getD default)
        (.load (clearControl h) (.goto (fun _ => .inr .collect))))
      (.load (fun _ => initialState h) (.goto (fun _ => .inr .loop))))
  | .inr .finish => TM2Renaming.relabelStmt (transferEquiv h)
    (TM2Transfer.transferStmt (Γ := Alphabet h) (σ := h.tm.σ × Bool)
      (.inr .buffer) (.inr .output) id (.inr .finish) (.inr .done))
  | .inr .done => .load (fun _ => initialState h) .halt

def run (n : ℕ) (q : Cfg (Alphabet h) (Label h) (State h)) : Option (Cfg (Alphabet h) (Label h) (State h)) :=
  (fun x : Option (Cfg (Alphabet h) (Label h) (State h)) => x.bind (step (program h)))^[n] (some q)

theorem run_step {q q' : Cfg (Alphabet h) (Label h) (State h)}
    (hs : step (program h) q = some q') (n : ℕ) : run h (n + 1) q = run h n q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, hs]

theorem run_add {q q' : Cfg (Alphabet h) (Label h) (State h)} {n : ℕ}
    (hs : run h n q = some q') (m : ℕ) : run h (n + m) q = run h m q' := by
  rw [Nat.add_comm n m]
  simp only [run, Function.iterate_add_apply, show
    (fun x : Option (Cfg (Alphabet h) (Label h) (State h)) => x.bind (step (program h)))^[n]
      (some q) = some q' from hs]

end
end ProteinFolding.Tetrahedral.ReductionTM2.Iterate
