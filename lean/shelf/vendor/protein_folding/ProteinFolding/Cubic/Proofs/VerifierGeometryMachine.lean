import ProteinFolding.Cubic.Proofs.VerifierGeometry
import ProteinFolding.Common.TM2WalkCopy

/-! An explicit finite-stack TM2 implementation of the geometric verifier.
Each outer iteration copies the remaining suffix, runs the three-step-per-record
row checker, and drains its six unary displacement counters. No unbounded value
is stored in the finite control state. -/

namespace ProteinFolding.CubicVerifier.GeometryMachine

open Turing TM2 Computability

abbrev Letter := Option Record

inductive Extra where
  | remaining | first | second | output
  deriving DecidableEq, Fintype

def ExtraAlphabet : Extra → Type
  | .remaining | .first | .second => Letter
  | .output => PairSymbol Bool Bool

abbrev Stack := Row.Stack ⊕ Extra
abbrev Alphabet : Stack → Type := Sum.elim Row.Alphabet ExtraAlphabet
abbrev State := Row.State × Option Letter

inductive Phase where
  | outer | copy | restoreFirst | restoreSecond
  | row : Row.Phase → Phase
  | drain : Fin 6 → Phase
  | emit
  deriving DecidableEq, Fintype

abbrev remaining : Stack := .inr .remaining
abbrev first : Stack := .inr .first
abbrev second : Stack := .inr .second
abbrev output : Stack := .inr .output
abbrev input : Stack := .inl (.inl .input)
abbrev counter (d : Fin 6) : Stack := .inl (.inl (.counter d))
abbrev bonds : Stack := .inl (.inr ())

instance : Inhabited (Alphabet remaining) := ⟨none⟩
instance : Inhabited (Alphabet first) := ⟨none⟩
instance : Inhabited (Alphabet second) := ⟨none⟩

def extraContents (r u v : List Letter) (o : List (PairSymbol Bool Bool)) :
    ∀ k, List (ExtraAlphabet k)
  | .remaining => r
  | .first => u
  | .second => v
  | .output => o

def contents (w : List Letter) (c : TM2WalkCounters.Counts) (b : ℕ)
    (r u v : List Letter) (o : List (PairSymbol Bool Bool)) : ∀ k, List (Alphabet k) :=
  TM2Embedding.joinStacks (Row.rowStacks w c b) (extraContents r u v o)

def cfg (phase : Phase) (ctx : Row.Context) (w : List Letter)
    (c : TM2WalkCounters.Counts) (b : ℕ) (r u v : List Letter)
    (o : List (PairSymbol Bool Bool)) (reg : Option Letter := none) :
    Cfg Alphabet Phase State :=
  ⟨some phase, (((none, false), ctx), reg), contents w c b r u v o⟩

def nextDrain : Fin 6 → Phase
  | 0 => .drain 1 | 1 => .drain 2 | 2 => .drain 3
  | 3 => .drain 4 | 4 => .drain 5 | 5 => .outer

def initialContext : Row.Context := rowContext false true
def initialState : State := (((none, false), initialContext), none)

def outerStmt : Stmt Alphabet Phase State :=
  .pop remaining (fun st head =>
    (((none, false), match head with
      | none => st.1.2
      | some a => rowContext (startLabel a) (st.1.2.valid && a.isSome)), head))
    (.branch (fun st => st.2.isSome)
      (.goto (fun _ => .copy))
      (.goto (fun _ => .emit)))

def drainStmt (d : Fin 6) : Stmt Alphabet Phase State :=
  .pop (counter d) (fun st head => (((st.1.1.1, head.isSome), st.1.2), st.2))
    (.branch (fun st => st.1.1.2)
      (.load (fun st => (((none, false), st.1.2), st.2)) (.goto (fun _ => .drain d)))
      (.load (fun st => (((none, false), st.1.2), st.2)) (.goto (fun _ => nextDrain d))))

def emitStmt : Stmt Alphabet Phase State :=
  .pop bonds (fun st head => (((st.1.1.1, head.isSome), st.1.2), st.2))
    (.branch (fun st => st.1.1.2)
      (.push output (fun _ => .right true)
        (.load (fun st => (((none, false), st.1.2), none)) (.goto (fun _ => .emit))))
      (.push output (fun _ => .sep)
        (.push output (fun st => .left st.1.2.valid)
          (.load (fun _ => initialState) .halt))))

def program : Phase → Stmt Alphabet Phase State
  | .outer => outerStmt
  | .copy => TM2WalkCopy.duplicateStmt remaining first second id id .copy .restoreFirst
  | .restoreFirst => TM2Transfer.transferStmt first remaining id .restoreFirst .restoreSecond
  | .restoreSecond => TM2Transfer.transferStmt second input id .restoreSecond (.row .scan)
  | .row p => TM2Embedding.liftStmt Phase.row (some (.drain 0)) (Row.program p)
  | .drain d => drainStmt d
  | .emit => emitStmt

def run (n : ℕ) (q : Cfg Alphabet Phase State) : Option (Cfg Alphabet Phase State) :=
  (fun x : Option (Cfg Alphabet Phase State) => x.bind (step program))^[n] (some q)

theorem run_zero (q : Cfg Alphabet Phase State) : run 0 q = some q := rfl

theorem run_step {q q' : Cfg Alphabet Phase State} (h : step program q = some q') (n : ℕ) :
    run (n + 1) q = run n q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]

theorem run_add {q q' : Cfg Alphabet Phase State} {n : ℕ}
    (h : run n q = some q') (m : ℕ) : run (n + m) q = run m q' := by
  unfold run at *
  rw [Nat.add_comm n m, Function.iterate_add_apply, h]

theorem update_remaining (w : List Letter) (c : TM2WalkCounters.Counts) (b : ℕ)
    (r r' u v : List Letter) (o : List (PairSymbol Bool Bool)) :
    Function.update (contents w c b r u v o) remaining r' = contents w c b r' u v o := by
  funext k
  rcases k with (k | k)
  · simp [remaining, contents, TM2Embedding.joinStacks]
  · cases k <;> simp [remaining, contents, TM2Embedding.joinStacks, extraContents]

theorem update_first (w : List Letter) (c : TM2WalkCounters.Counts) (b : ℕ)
    (r u u' v : List Letter) (o : List (PairSymbol Bool Bool)) :
    Function.update (contents w c b r u v o) first u' = contents w c b r u' v o := by
  funext k
  rcases k with (k | k)
  · simp [first, contents, TM2Embedding.joinStacks]
  · cases k <;> simp [first, contents, TM2Embedding.joinStacks, extraContents]

theorem update_second (w : List Letter) (c : TM2WalkCounters.Counts) (b : ℕ)
    (r u v v' : List Letter) (o : List (PairSymbol Bool Bool)) :
    Function.update (contents w c b r u v o) second v' = contents w c b r u v' o := by
  funext k
  rcases k with (k | k)
  · simp [second, contents, TM2Embedding.joinStacks]
  · cases k <;> simp [second, contents, TM2Embedding.joinStacks, extraContents]

theorem update_input (w w' : List Letter) (c : TM2WalkCounters.Counts) (b : ℕ)
    (r u v : List Letter) (o : List (PairSymbol Bool Bool)) :
    Function.update (contents w c b r u v o) input w' = contents w' c b r u v o := by
  rw [contents, TM2Embedding.joinStacks_update]
  rw [Row.rowStacks, TM2Embedding.joinStacks_update]
  rw [TM2WalkCounters.update_input]
  rfl

theorem outer_step_cons (ctx : Row.Context) (a : Letter) (r : List Letter) (b : ℕ) :
    step program (cfg .outer ctx [] (fun _ => 0) b (a :: r) [] [] []) =
      some (cfg .copy (rowContext (startLabel a) (ctx.valid && a.isSome))
        [] (fun _ => 0) b r [] [] [] (some a)) := by
  simp [cfg, program, outerStmt, step, stepAux, contents, TM2Embedding.joinStacks,
    extraContents, remaining]
  exact update_remaining [] (fun _ => 0) b (a :: r) r [] [] []

theorem outer_step_nil (ctx : Row.Context) (b : ℕ) :
    step program (cfg .outer ctx [] (fun _ => 0) b [] [] [] []) =
      some (cfg .emit ctx [] (fun _ => 0) b [] [] [] []) := by
  simp [cfg, program, outerStmt, step, stepAux, contents, TM2Embedding.joinStacks,
    extraContents, remaining]

end ProteinFolding.CubicVerifier.GeometryMachine
