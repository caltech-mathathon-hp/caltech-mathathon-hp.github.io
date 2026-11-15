import ProteinFolding.Common.TM2BoundedSearchModel
import ProteinFolding.Common.TM2Renaming

/-! Explicit bounded-search controller around an actual predicate machine.
Independent pairing first augments each predicate result with the original
encoded argument. The controller stores that saved argument in reverse order,
appends one unary index symbol after a failed test, and calls the same finite
machine again. Its five extra stacks never store an unbounded control value.
-/

namespace ProteinFolding.TM2BoundedSearch

open Computability Turing TM2

noncomputable section

variable {A : Type} {ea : FinEncoding A} {test : A × ℕ → Bool}
variable (hp : TM2ComputableInPolyTime (pairEncoding ea unaryFinEncodingNat) finEncodingBoolBool test)

abbrev InputSymbol := PairSymbol ea.Γ Bool
abbrev SavedSymbol := PairSymbol (InputSymbol (ea := ea)) Bool

def savedEncoding : FinEncoding ((A × ℕ) × Bool) :=
  pairEncoding (pairEncoding ea unaryFinEncodingNat) finEncodingBoolBool

def savedPredicate : TM2ComputableInPolyTime (pairEncoding ea unaryFinEncodingNat) (savedEncoding (ea := ea))
    (fun x => (x, test x)) :=
  TM2ProductMap.pairComputable (idComputableInPolyTime (pairEncoding ea unaryFinEncodingNat)) hp

inductive Extra where
  | input | buffer | current | remaining | output
  deriving DecidableEq, Fintype

inductive Phase where
  | scanX | scanRemaining | loop | prepare | readWord | readBool
  | drainRemaining | drainBuffer | emit
  deriving DecidableEq, Fintype

abbrev Stack := (savedPredicate hp).tm.K ⊕ Extra
abbrev Label := (savedPredicate hp).tm.Λ ⊕ Phase
abbrev Control := Option (InputSymbol (ea := ea)) × Bool
abbrev State := (savedPredicate hp).tm.σ × Control (ea := ea)

def ExtraAlphabet : Extra → Type
  | .input | .buffer => InputSymbol (ea := ea)
  | .current | .remaining => Unit
  | .output => Bool

abbrev Alphabet := Sum.elim (savedPredicate hp).tm.Γ (ExtraAlphabet (ea := ea))

structure Data where
  input : List (InputSymbol (ea := ea))
  buffer : List (InputSymbol (ea := ea))
  current : ℕ
  remaining : ℕ
  output : List Bool

def auxContents (d : Data (ea := ea)) : ∀ k, List (ExtraAlphabet (ea := ea) k)
  | .input => d.input
  | .buffer => d.buffer
  | .current => List.replicate d.current ()
  | .remaining => List.replicate d.remaining ()
  | .output => d.output

def contents (S : ∀ k, List ((savedPredicate hp).tm.Γ k)) (d : Data (ea := ea)) :
    ∀ k, List (Alphabet hp k) := TM2Embedding.joinStacks S (auxContents d)

def emptyStacks : ∀ k, List ((savedPredicate hp).tm.Γ k) := fun _ => []

def oneStack (k : (savedPredicate hp).tm.K) (w : List ((savedPredicate hp).tm.Γ k)) :
    ∀ j, List ((savedPredicate hp).tm.Γ j) := Function.update (emptyStacks hp) k w

def initialState : State hp := ((savedPredicate hp).tm.initialState, (none, false))

def cfg (l : Label hp) (S : ∀ k, List ((savedPredicate hp).tm.Γ k)) (d : Data (ea := ea)) :
    Cfg (Alphabet hp) (Label hp) (State hp) := ⟨some l, initialState hp, contents hp S d⟩

def clearControl (st : State hp) : State hp := (st.1, (none, false))

def transferEquiv : (((savedPredicate hp).tm.σ × Bool) × Option (InputSymbol (ea := ea))) ≃ State hp where
  toFun st := (st.1.1, (st.2, st.1.2))
  invFun st := ((st.1, st.2.2), st.2.1)
  left_inv st := by obtain ⟨⟨s, b⟩, r⟩ := st; rfl
  right_inv st := by obtain ⟨s, r, b⟩ := st; rfl

def leftHead : Option (InputSymbol (ea := ea)) → Option (InputSymbol (ea := ea))
  | some (.left a) => some (.left a)
  | _ => none

def savedHead (head : Option ((savedPredicate hp).tm.Γ (savedPredicate hp).tm.k₁)) :
    Option (InputSymbol (ea := ea)) :=
  head.bind fun a => match (savedPredicate hp).outputAlphabet a with
    | .left s => some s
    | _ => none

def savedAnswer (head : Option ((savedPredicate hp).tm.Γ (savedPredicate hp).tm.k₁)) : Bool :=
  match head.map (savedPredicate hp).outputAlphabet with
  | some (.right b) => b
  | _ => false

instance : Inhabited (Alphabet hp (.inr .buffer)) := ⟨PairSymbol.sep⟩

def program : Label hp → Stmt (Alphabet hp) (Label hp) (State hp)
  | .inl l => TM2Embedding.liftStmt Sum.inl (some (.inr .readWord)) ((savedPredicate hp).tm.m l)
  | .inr .scanX => .pop (.inr .input) (fun st h => (st.1, (leftHead h, false)))
    (.branch (fun st => st.2.1.isSome)
      (.push (.inr .buffer) (fun st => st.2.1.getD .sep)
        (.load (clearControl hp) (.goto (fun _ => .inr .scanX))))
      (.push (.inr .buffer) (fun _ => .sep)
        (.load (clearControl hp) (.goto (fun _ => .inr .scanRemaining)))))
  | .inr .scanRemaining => .pop (.inr .input) (fun st h => (st.1, (none, h.isSome)))
    (.branch (fun st => st.2.2)
      (.push (.inr .remaining) (fun _ => ())
        (.load (clearControl hp) (.goto (fun _ => .inr .scanRemaining))))
      (.load (clearControl hp) (.goto (fun _ => .inr .loop))))
  | .inr .loop => .peek (.inr .remaining) (fun st h => (st.1, (none, h.isSome)))
    (.branch (fun st => st.2.2)
      (.load (clearControl hp) (.goto (fun _ => .inr .prepare)))
      (.load (clearControl hp) (.goto (fun _ => .inr .drainBuffer))))
  | .inr .prepare => TM2Renaming.relabelStmt (transferEquiv hp)
    (TM2Transfer.transferStmt (Γ := Alphabet hp) (σ := (savedPredicate hp).tm.σ × Bool)
      (.inr .buffer) (.inl (savedPredicate hp).tm.k₀) (savedPredicate hp).inputAlphabet.symm
      (.inr .prepare) (.inl (savedPredicate hp).tm.main))
  | .inr .readWord => .pop (.inl (savedPredicate hp).tm.k₁)
    (fun st h => (st.1, (savedHead hp h, false)))
    (.branch (fun st => st.2.1.isSome)
      (.push (.inr .buffer) (fun st => st.2.1.getD .sep)
        (.load (clearControl hp) (.goto (fun _ => .inr .readWord))))
      (.load (clearControl hp) (.goto (fun _ => .inr .readBool))))
  | .inr .readBool => .pop (.inl (savedPredicate hp).tm.k₁)
    (fun st h => (st.1, (none, savedAnswer hp h)))
    (.branch (fun st => st.2.2)
      (.load (clearControl hp) (.goto (fun _ => .inr .drainRemaining)))
      (.pop (.inr .remaining) (fun st _ => clearControl hp st)
        (.push (.inr .current) (fun _ => ())
          (.push (.inr .buffer) (fun _ => .right true) (.goto (fun _ => .inr .loop))))))
  | .inr .drainRemaining => .pop (.inr .remaining) (fun st h => (st.1, (none, h.isSome)))
    (.branch (fun st => st.2.2)
      (.load (clearControl hp) (.goto (fun _ => .inr .drainRemaining)))
      (.load (clearControl hp) (.goto (fun _ => .inr .drainBuffer))))
  | .inr .drainBuffer => .pop (.inr .buffer) (fun st h => (st.1, (h, false)))
    (.branch (fun st => st.2.1.isSome)
      (.load (clearControl hp) (.goto (fun _ => .inr .drainBuffer)))
      (.load (clearControl hp) (.goto (fun _ => .inr .emit))))
  | .inr .emit => .pop (.inr .current) (fun st h => (st.1, (none, h.isSome)))
    (.branch (fun st => st.2.2)
      (.push (.inr .output) (fun _ => true)
        (.load (clearControl hp) (.goto (fun _ => .inr .emit))))
      (.load (fun _ => initialState hp) .halt))

def run (n : ℕ) (q : Cfg (Alphabet hp) (Label hp) (State hp)) :
    Option (Cfg (Alphabet hp) (Label hp) (State hp)) :=
  (fun x : Option (Cfg (Alphabet hp) (Label hp) (State hp)) => x.bind (step (program hp)))^[n] (some q)

theorem run_step {q q' : Cfg (Alphabet hp) (Label hp) (State hp)}
    (h : step (program hp) q = some q') (n : ℕ) : run hp (n + 1) q = run hp n q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]

theorem run_add {q q' : Cfg (Alphabet hp) (Label hp) (State hp)} {n : ℕ}
    (h : run hp n q = some q') (m : ℕ) : run hp (n + m) q = run hp m q' := by
  rw [Nat.add_comm n m]
  simp only [run, Function.iterate_add_apply, show
    (fun x : Option (Cfg (Alphabet hp) (Label hp) (State hp)) => x.bind (step (program hp)))^[n]
      (some q) = some q' from h]

end
end ProteinFolding.TM2BoundedSearch
