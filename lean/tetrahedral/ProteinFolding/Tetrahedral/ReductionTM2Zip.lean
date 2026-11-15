import ProteinFolding.Tetrahedral.ReductionTM2Assembly

namespace ProteinFolding.Tetrahedral.ReductionTM2.Zip

open Computability Turing TM2

abbrev Token := Option Residue
abbrev Letter := Option (PairSymbol Bool Residue)
abbrev Symbol := PairSymbol Token Bool

def zipFields : List Bool → List Sequence → List FlaggedBody
  | _, [] => []
  | fs, u :: us => (fs[0]?.getD false, u) :: zipFields (fs.drop 1) us

inductive Slot where
  | input | bodyBuffer | bodies | outputBuffer | output
  deriving DecidableEq, Fintype
inductive Phase where
  | read | restoreBodies | start | body | drain | restoreOutput | finish
  deriving DecidableEq, Fintype
def Alphabet : Slot → Type
  | .input => Symbol
  | .bodyBuffer | .bodies => Token
  | .outputBuffer | .output => Letter
structure Reg where
  symbol : Option Symbol
  body : Option Token
  output : Option Letter
  deriving DecidableEq, Fintype
def initial : Reg := ⟨none, none, none⟩
def contents (raw : List Symbol) (buf body : List Token) (rev out : List Letter) : ∀ k, List (Alphabet k)
  | .input => raw
  | .bodyBuffer => buf
  | .bodies => body
  | .outputBuffer => rev
  | .output => out
def cfg (p : Phase) (raw : List Symbol) (buf body : List Token) (rev out : List Letter) : Cfg Alphabet Phase Reg :=
  ⟨some p, initial, contents raw buf body rev out⟩

theorem update_input (raw raw' : List Symbol) (buf body : List Token) (rev out : List Letter) :
    Function.update (contents raw buf body rev out) .input raw' = contents raw' buf body rev out := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]
theorem update_bodyBuffer (raw : List Symbol) (buf buf' body : List Token) (rev out : List Letter) :
    Function.update (contents raw buf body rev out) .bodyBuffer buf' = contents raw buf' body rev out := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]
theorem update_bodies (raw : List Symbol) (buf body body' : List Token) (rev out : List Letter) :
    Function.update (contents raw buf body rev out) .bodies body' = contents raw buf body' rev out := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]
theorem update_outputBuffer (raw : List Symbol) (buf body : List Token) (rev rev' out : List Letter) :
    Function.update (contents raw buf body rev out) .outputBuffer rev' = contents raw buf body rev' out := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]
theorem update_output (raw : List Symbol) (buf body : List Token) (rev out out' : List Letter) :
    Function.update (contents raw buf body rev out) .output out' = contents raw buf body rev out' := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

def readBody : Option Symbol → Option Token
  | some (.left a) => some a
  | _ => none
def readFlag : Option Symbol → Bool
  | some (.right b) => b
  | _ => false

def program : Phase → Stmt Alphabet Phase Reg
  | .read => .pop .input (fun s o => {s with symbol := o})
      (.branch (fun s => (readBody s.symbol).isSome)
        (.push .bodyBuffer (fun s => (readBody s.symbol).getD none)
          (.load (fun _ => initial) (.goto (fun _ => .read))))
        (.load (fun _ => initial) (.goto (fun _ => .restoreBodies))))
  | .restoreBodies => .pop .bodyBuffer (fun s o => {s with body := o})
      (.branch (fun s => s.body.isSome)
        (.push .bodies (fun s => s.body.getD none) (.load (fun _ => initial) (.goto (fun _ => .restoreBodies))))
        (.load (fun _ => initial) (.goto (fun _ => .start))))
  | .start => .peek .bodies (fun s o => {s with body := o})
      (.branch (fun s => s.body.isSome)
        (.pop .input (fun s o => {s with symbol := o})
          (.push .outputBuffer (fun s => some (.left (readFlag s.symbol)))
            (.push .outputBuffer (fun _ => some .sep) (.load (fun _ => initial) (.goto (fun _ => .body))))))
        (.load (fun _ => initial) (.goto (fun _ => .drain))))
  | .body => .pop .bodies (fun s o => {s with body := o})
      (.branch (fun s => (s.body.bind id).isSome)
        (.push .outputBuffer (fun s => some (.right ((s.body.bind id).getD .H)))
          (.load (fun _ => initial) (.goto (fun _ => .body))))
        (.push .outputBuffer (fun _ => none) (.load (fun _ => initial) (.goto (fun _ => .start)))))
  | .drain => .pop .input (fun s o => {s with symbol := o})
      (.branch (fun s => s.symbol.isSome)
        (.load (fun _ => initial) (.goto (fun _ => .drain)))
        (.load (fun _ => initial) (.goto (fun _ => .restoreOutput))))
  | .restoreOutput => .pop .outputBuffer (fun s o => {s with output := o})
      (.branch (fun s => s.output.isSome)
        (.push .output (fun s => s.output.getD none) (.load (fun _ => initial) (.goto (fun _ => .restoreOutput))))
        (.load (fun _ => initial) (.goto (fun _ => .finish))))
  | .finish => .halt

def run (n : ℕ) (q : Cfg Alphabet Phase Reg) : Option (Cfg Alphabet Phase Reg) :=
  (fun q : Option (Cfg Alphabet Phase Reg) => q.bind (Turing.TM2.step program))^[n] (some q)
theorem run_step {q q' : Cfg Alphabet Phase Reg} (h : Turing.TM2.step program q = some q') (n : ℕ) :
    run (n + 1) q = run n q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]
theorem run_add {q q' : Cfg Alphabet Phase Reg} {n : ℕ} (h : run n q = some q') (m : ℕ) :
    run (n + m) q = run m q' := by
  unfold run at *
  rw [Nat.add_comm n m, Function.iterate_add_apply, h]

end ProteinFolding.Tetrahedral.ReductionTM2.Zip
