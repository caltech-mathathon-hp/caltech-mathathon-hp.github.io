import ProteinFolding.Common.TM2ArithmeticBits
import ProteinFolding.Common.TM2Transfer

/-! A finite stack program for signed-binary/unary comparison.
The binary magnitude is decremented once per consumed unary symbol. Thus the
program never expands a large binary magnitude to unary. -/

namespace ProteinFolding.TM2Arithmetic.Comparator

open Computability Turing TM2

abbrev Sym := PairSymbol Bool Bool

inductive Slot where
  | input | buffer | bits | unary | output
  deriving DecidableEq, Fintype

inductive Phase where
  | sign | scan | restore | dec | consume | clearBits | clearBuffer | clearUnary | finish
  deriving DecidableEq, Fintype

structure Reg where
  token : Option Sym
  bit : Option Bool
  borrow : Bool
  negative : Bool
  result : Bool
  deriving DecidableEq, Fintype

def regs (borrow negative result : Bool) : Reg := ⟨none, none, borrow, negative, result⟩
def initial : Reg := regs true false false

def Alphabet : Slot → Type
  | .input => Sym
  | _ => Bool

def contents (input : List Sym) (buffer bits unary output : List Bool) : ∀ k, List (Alphabet k)
  | .input => input
  | .buffer => buffer
  | .bits => bits
  | .unary => unary
  | .output => output

theorem update_input (i i' : List Sym) (b w u o : List Bool) :
    Function.update (contents i b w u o) .input i' = contents i' b w u o := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]
theorem update_buffer (i : List Sym) (b b' w u o : List Bool) :
    Function.update (contents i b w u o) .buffer b' = contents i b' w u o := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]
theorem update_bits (i : List Sym) (b w w' u o : List Bool) :
    Function.update (contents i b w u o) .bits w' = contents i b w' u o := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]
theorem update_unary (i : List Sym) (b w u u' o : List Bool) :
    Function.update (contents i b w u o) .unary u' = contents i b w u' o := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]
theorem update_output (i : List Sym) (b w u o o' : List Bool) :
    Function.update (contents i b w u o) .output o' = contents i b w u o' := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

def leftBit : Option Sym → Option Bool
  | some (.left b) => some b
  | _ => none
def rightToken : Option Sym → Bool
  | some (.right _) => true
  | _ => false

def program : Phase → Stmt Alphabet Phase Reg
  | .sign => .pop .input (fun st x => {st with token := x})
      (.load (fun st => {st with negative := (leftBit st.token).getD false, token := none})
        (.goto (fun _ => .scan)))
  | .scan => .pop .input (fun st x => {st with token := x})
      (.branch (fun st => st.token.isSome)
        (.branch (fun st => (leftBit st.token).isSome)
          (.push .buffer (fun st => (leftBit st.token).getD false)
            (.load (fun st => {st with token := none}) (.goto (fun _ => .scan))))
          (.branch (fun st => rightToken st.token)
            (.push .unary (fun _ => true)
              (.load (fun st => {st with token := none}) (.goto (fun _ => .scan))))
            (.load (fun st => {st with token := none}) (.goto (fun _ => .scan)))))
        (.branch (fun st => st.negative)
          (.load (fun st => {st with result := true}) (.goto (fun _ => .clearBits)))
          (.goto (fun _ => .restore))))
  | .restore => .pop .buffer (fun st x => {st with bit := x})
      (.branch (fun st => st.bit.isSome)
        (.push .bits (fun st => st.bit.getD false)
          (.load (fun st => {st with bit := none}) (.goto (fun _ => .restore))))
        (.load (fun st => {st with borrow := true, bit := none}) (.goto (fun _ => .dec))))
  | .dec => .pop .bits (fun st x => {st with bit := x})
      (.branch (fun st => st.bit.isSome)
        (.push .buffer (fun st => if st.borrow then !(st.bit.getD false) else st.bit.getD false)
          (.load (fun st => {st with borrow := st.borrow && !(st.bit.getD false), bit := none})
            (.goto (fun _ => .dec))))
        (.branch (fun st => st.borrow)
          (.load (fun st => {st with result := true}) (.goto (fun _ => .clearBits)))
          (.goto (fun _ => .consume))))
  | .consume => .pop .unary (fun st x => {st with bit := x})
      (.branch (fun st => st.bit.isSome)
        (.load (fun st => {st with bit := none}) (.goto (fun _ => .restore)))
        (.load (fun st => {st with result := false}) (.goto (fun _ => .clearBits))))
  | .clearBits => .pop .bits (fun st x => {st with bit := x})
      (.branch (fun st => st.bit.isSome)
        (.load (fun st => {st with bit := none}) (.goto (fun _ => .clearBits)))
        (.goto (fun _ => .clearBuffer)))
  | .clearBuffer => .pop .buffer (fun st x => {st with bit := x})
      (.branch (fun st => st.bit.isSome)
        (.load (fun st => {st with bit := none}) (.goto (fun _ => .clearBuffer)))
        (.goto (fun _ => .clearUnary)))
  | .clearUnary => .pop .unary (fun st x => {st with bit := x})
      (.branch (fun st => st.bit.isSome)
        (.load (fun st => {st with bit := none}) (.goto (fun _ => .clearUnary)))
        (.goto (fun _ => .finish)))
  | .finish => .push .output (fun st => st.result) (.load (fun _ => initial) .halt)

def cfg (label : Phase) (st : Reg) (i : List Sym) (b w u o : List Bool) :
    Cfg Alphabet Phase Reg := ⟨some label, st, contents i b w u o⟩

def machine : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Phase
  main := .sign
  σ := Reg
  initialState := initial
  Γk₀Fin := inferInstanceAs (Fintype Sym)
  m := program

abbrev tick : Option (Cfg Alphabet Phase Reg) → Option (Cfg Alphabet Phase Reg) :=
  fun x => x.bind (step program)

end ProteinFolding.TM2Arithmetic.Comparator
