import ProteinFolding.Common.TM2Embedding

/-! An explicit finite TM2 for constant functions. It erases its input stack
and writes a fixed output word, restoring the initial internal state. -/

namespace ProteinFolding.TM2Constants

open Computability Turing TM2

variable {A B : Type}

def Alphabet (A B : Type) : Bool → Type
  | false => A
  | true => B

def constantStacks (u : List A) (v : List B) : ∀ k, List (Alphabet A B k)
  | false => u
  | true => v

theorem update_input (u u' : List A) (v : List B) :
    Function.update (constantStacks u v) false u' = constantStacks u' v := by
  funext k
  cases k <;> simp [constantStacks, Function.update_of_ne]

theorem update_output (u : List A) (v v' : List B) :
    Function.update (constantStacks u v) true v' = constantStacks u v' := by
  funext k
  cases k <;> simp [constantStacks, Function.update_of_ne]

def writeWord : List B → Stmt (Alphabet A B) Bool Bool
  | [] => .load (fun _ => false) .halt
  | b :: bs => .push true (fun _ => b) (writeWord bs)

theorem writeWord_stepAux (w : List B) (flag : Bool) (u : List A) (v : List B) :
    stepAux (writeWord w) flag (constantStacks u v) =
      ⟨none, false, constantStacks u (w.reverse ++ v)⟩ := by
  induction w generalizing flag v with
  | nil => rfl
  | cons b bs ih =>
    simpa [writeWord, stepAux, constantStacks, update_output, List.reverse_cons,
      List.append_assoc] using ih flag (b :: v)

def program (output : List B) : Bool → Stmt (Alphabet A B) Bool Bool
  | false => .pop false (fun _ x => x.isSome)
      (.branch id (.goto (fun _ => false)) (.goto (fun _ => true)))
  | true => writeWord output.reverse

def cfg (label flag : Bool) (u : List A) (v : List B) : Cfg (Alphabet A B) Bool Bool :=
  ⟨some label, flag, constantStacks u v⟩

theorem clear_run (output : List B) (input : List A) (flag : Bool) (v : List B) :
    (fun x : Option (Cfg (Alphabet A B) Bool Bool) => x.bind (step (program output)))^[input.length + 1]
      (some (cfg false flag input v)) = some (cfg true false [] v) := by
  induction input generalizing flag with
  | nil =>
    simp [cfg, program, step, stepAux, constantStacks, update_input]
  | cons a input ih =>
    rw [List.length_cons, Nat.add_right_comm input.length 1 1, Function.iterate_succ_apply]
    simpa only [Option.bind_some, cfg, program, step, stepAux, constantStacks, update_input,
      List.head?_cons, List.tail_cons, Option.isSome_some, id_eq, cond_true] using ih true

theorem program_run (output : List B) (input : List A) :
    (fun x : Option (Cfg (Alphabet A B) Bool Bool) => x.bind (step (program output)))^[input.length + 2]
      (some (cfg false false input [])) = some ⟨none, false, constantStacks [] output⟩ := by
  rw [show input.length + 2 = (input.length + 1) + 1 by omega,
    Function.iterate_succ_apply', clear_run]
  simp only [Option.bind_some, cfg, step, program, writeWord_stepAux, List.reverse_reverse,
    List.append_nil]

def machine (Input : Type) [Fintype Input] (output : List B) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := Alphabet Input B
  Λ := Bool
  main := false
  σ := Bool
  initialState := false
  Γk₀Fin := inferInstanceAs (Fintype Input)
  m := program output

def machine_outputs (Input : Type) [Fintype Input] (output : List B) (input : List Input) :
    TM2OutputsInTime (machine Input output) input (some output) (input.length + 2) := by
  have hi : initList (machine Input output) input = cfg false false input [] := by
    apply congrArg (fun S : ∀ k, List (Alphabet Input B k) =>
      (⟨some false, false, S⟩ : Cfg (Alphabet Input B) Bool Bool))
    funext k
    cases k <;> rfl
  have ho : haltList (machine Input output) output =
      (⟨none, false, constantStacks [] output⟩ : Cfg (Alphabet Input B) Bool Bool) := by
    apply congrArg (fun S : ∀ k, List (Alphabet Input B k) =>
      (⟨none, false, S⟩ : Cfg (Alphabet Input B) Bool Bool))
    funext k
    cases k <;> rfl
  refine ⟨⟨input.length + 2, ?_⟩, le_rfl⟩
  change (fun x => x.bind (step (program output)))^[input.length + 2]
    (some (initList (machine Input output) input)) = some (haltList (machine Input output) output)
  rw [hi, ho]
  exact program_run output input

noncomputable def constantComputable {X Y : Type} (ex : FinEncoding X) (ey : FinEncoding Y)
    (y : Y) : TM2ComputableInPolyTime ex ey (fun _ => y) where
  tm := machine ex.Γ (ey.encode y)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + Polynomial.C 2
  outputsFun x := by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    change TM2OutputsInTime (machine ex.Γ (ey.encode y))
      (List.map id (ex.encode x)) (some (List.map id (ey.encode y))) ((ex.encode x).length + 2)
    simpa only [List.map_id] using machine_outputs ex.Γ (ey.encode y) (ex.encode x)

end ProteinFolding.TM2Constants
