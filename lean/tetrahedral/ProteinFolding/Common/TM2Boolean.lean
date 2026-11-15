import ProteinFolding.Common.TM2Constants

/-! Explicit one-step finite TM2 programs for Boolean functions. The canonical
Boolean encoding contains one symbol, so a pair contains exactly three symbols.
Each program consumes that input, writes one Boolean, and resets its register. -/

namespace ProteinFolding.TM2Boolean

open Computability Turing TM2 TM2Constants

abbrev PairBit := PairSymbol Bool Bool

def leftBit : Option PairBit → Bool
  | some (.left b) => b
  | _ => false

def rightBit : Option PairBit → Bool
  | some (.right b) => b
  | _ => false

def binaryProgram (f : Bool → Bool → Bool) : Unit →
    Stmt (Alphabet PairBit Bool) Unit (Bool × Bool) := fun _ =>
  .pop false (fun st x => (leftBit x, st.2))
    (.pop false (fun st _ => st)
      (.pop false (fun st x => (st.1, rightBit x))
        (.push true (fun st => f st.1 st.2)
          (.load (fun _ => (false, false)) .halt))))

def binaryMachine (f : Bool → Bool → Bool) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := Alphabet PairBit Bool
  Λ := Unit
  main := ()
  σ := Bool × Bool
  initialState := (false, false)
  Γk₀Fin := inferInstanceAs (Fintype PairBit)
  m := binaryProgram f

theorem binary_transition (f : Bool → Bool → Bool) (a b : Bool) :
    step (binaryProgram f)
      (⟨some (), (false, false), constantStacks [.left a, .sep, .right b] []⟩ :
        Cfg (Alphabet PairBit Bool) Unit (Bool × Bool)) =
      some ⟨none, (false, false), constantStacks [] [f a b]⟩ := by
  simp [binaryProgram, step, stepAux, constantStacks, update_input, update_output,
    leftBit, rightBit]

def binary_outputs (f : Bool → Bool → Bool) (a b : Bool) :
    TM2OutputsInTime (binaryMachine f) [.left a, .sep, .right b]
      (some [f a b]) 1 := by
  have hi : initList (binaryMachine f) [.left a, .sep, .right b] =
      (⟨some (), (false, false), constantStacks [.left a, .sep, .right b] []⟩ :
        Cfg (Alphabet PairBit Bool) Unit (Bool × Bool)) := by
    apply congrArg (fun S : ∀ k, List (Alphabet PairBit Bool k) =>
      (⟨some (), (false, false), S⟩ : Cfg (Alphabet PairBit Bool) Unit (Bool × Bool)))
    funext k
    cases k <;> rfl
  have ho : haltList (binaryMachine f) [f a b] =
      (⟨none, (false, false), constantStacks [] [f a b]⟩ :
        Cfg (Alphabet PairBit Bool) Unit (Bool × Bool)) := by
    apply congrArg (fun S : ∀ k, List (Alphabet PairBit Bool k) =>
      (⟨none, (false, false), S⟩ : Cfg (Alphabet PairBit Bool) Unit (Bool × Bool)))
    funext k
    cases k <;> rfl
  refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_rfl }
  change step (binaryProgram f)
    (initList (binaryMachine f) [.left a, .sep, .right b]) =
      some (haltList (binaryMachine f) [f a b])
  rw [hi, ho]
  exact binary_transition f a b

noncomputable def binaryComputable (f : Bool → Bool → Bool) :
    TM2ComputableInPolyTime (pairEncoding finEncodingBoolBool finEncodingBoolBool)
      finEncodingBoolBool (fun p => f p.1 p.2) where
  tm := binaryMachine f
  inputAlphabet := Equiv.refl PairBit
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 1
  outputsFun p := by
    rcases p with ⟨a, b⟩
    simpa [Equiv.refl, pairEncoding, finEncodingBoolBool, encodeBool] using
      binary_outputs f a b

def unaryProgram (f : Bool → Bool) : Unit → Stmt (Alphabet Bool Bool) Unit Bool := fun _ =>
  .pop false (fun _ x => x.getD false)
    (.push true f (.load (fun _ => false) .halt))

def unaryMachine (f : Bool → Bool) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := Alphabet Bool Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := unaryProgram f

theorem unary_transition (f : Bool → Bool) (a : Bool) :
    step (unaryProgram f)
      (⟨some (), false, constantStacks [a] []⟩ : Cfg (Alphabet Bool Bool) Unit Bool) =
      some ⟨none, false, constantStacks [] [f a]⟩ := by
  simp [unaryProgram, step, stepAux, constantStacks, update_input, update_output]

def unary_outputs (f : Bool → Bool) (a : Bool) :
    TM2OutputsInTime (unaryMachine f) [a] (some [f a]) 1 := by
  have hi : initList (unaryMachine f) [a] =
      (⟨some (), false, constantStacks [a] []⟩ : Cfg (Alphabet Bool Bool) Unit Bool) := by
    apply congrArg (fun S : ∀ k, List (Alphabet Bool Bool k) =>
      (⟨some (), false, S⟩ : Cfg (Alphabet Bool Bool) Unit Bool))
    funext k
    cases k <;> rfl
  have ho : haltList (unaryMachine f) [f a] =
      (⟨none, false, constantStacks [] [f a]⟩ : Cfg (Alphabet Bool Bool) Unit Bool) := by
    apply congrArg (fun S : ∀ k, List (Alphabet Bool Bool k) =>
      (⟨none, false, S⟩ : Cfg (Alphabet Bool Bool) Unit Bool))
    funext k
    cases k <;> rfl
  refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_rfl }
  change step (unaryProgram f) (initList (unaryMachine f) [a]) =
    some (haltList (unaryMachine f) [f a])
  rw [hi, ho]
  exact unary_transition f a

noncomputable def unaryComputable (f : Bool → Bool) :
    TM2ComputableInPolyTime finEncodingBoolBool finEncodingBoolBool f where
  tm := unaryMachine f
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 1
  outputsFun a := by
    simpa [Equiv.refl, finEncodingBoolBool, encodeBool] using unary_outputs f a

noncomputable def andComputable :
    TM2ComputableInPolyTime (pairEncoding finEncodingBoolBool finEncodingBoolBool)
      finEncodingBoolBool (fun p => p.1 && p.2) := binaryComputable Bool.and

noncomputable def notComputable :
    TM2ComputableInPolyTime finEncodingBoolBool finEncodingBoolBool Bool.not :=
  unaryComputable Bool.not

example : step (binaryProgram Bool.and)
    (⟨some (), (false, false), constantStacks [.left false, .sep, .right false] []⟩ :
      Cfg (Alphabet PairBit Bool) Unit (Bool × Bool)) =
    some ⟨none, (false, false), constantStacks [] [false]⟩ :=
  binary_transition Bool.and false false

example : step (binaryProgram Bool.and)
    (⟨some (), (false, false), constantStacks [.left false, .sep, .right true] []⟩ :
      Cfg (Alphabet PairBit Bool) Unit (Bool × Bool)) =
    some ⟨none, (false, false), constantStacks [] [false]⟩ :=
  binary_transition Bool.and false true

example : step (binaryProgram Bool.and)
    (⟨some (), (false, false), constantStacks [.left true, .sep, .right false] []⟩ :
      Cfg (Alphabet PairBit Bool) Unit (Bool × Bool)) =
    some ⟨none, (false, false), constantStacks [] [false]⟩ :=
  binary_transition Bool.and true false

example : step (binaryProgram Bool.and)
    (⟨some (), (false, false), constantStacks [.left true, .sep, .right true] []⟩ :
      Cfg (Alphabet PairBit Bool) Unit (Bool × Bool)) =
    some ⟨none, (false, false), constantStacks [] [true]⟩ :=
  binary_transition Bool.and true true

end ProteinFolding.TM2Boolean
