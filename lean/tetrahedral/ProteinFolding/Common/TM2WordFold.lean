import ProteinFolding.Common.TM2CompositionPoly

/-! An actual TM2 for finite-state word predicates. One input letter updates
the finite control in one TM2 step; the final step emits a Boolean and restores
the initial state. No unbounded value is stored in the control state. -/

namespace ProteinFolding.TM2WordFold

open Computability Turing TM2

inductive Slot where
  | input | output
  deriving DecidableEq, Fintype

def Alphabet (I : Type) : Slot → Type
  | .input => I
  | .output => Bool

variable {I S : Type}

def contents (u : List I) (o : List Bool) : ∀ k, List (Alphabet I k)
  | .input => u
  | .output => o

def cfg (s : S) (u : List I) (o : List Bool) : Cfg (Alphabet I) Unit (S × Option I) :=
  ⟨some (), (s, none), contents u o⟩

def done (s₀ : S) (o : List Bool) : Cfg (Alphabet I) Unit (S × Option I) :=
  ⟨none, (s₀, none), contents [] o⟩

def program (f : S → I → S) (g : S → Bool) (s₀ : S) :
    Unit → Stmt (Alphabet I) Unit (S × Option I) := fun _ =>
  .pop .input (fun st head => (st.1, head))
    (.branch (fun st => st.2.isSome)
      (.load (fun st => (match st.2 with | none => st.1 | some a => f st.1 a, none))
        (.goto (fun _ => ())))
      (.push .output (fun st => g st.1) (.load (fun _ => (s₀, none)) .halt)))

theorem update_input (u u' : List I) (o : List Bool) :
    Function.update (contents u o) .input u' = contents u' o := by
  funext k
  cases k <;> simp [contents, Function.update_of_ne]

theorem update_output (u : List I) (o o' : List Bool) :
    Function.update (contents u o) .output o' = contents u o' := by
  funext k
  cases k <;> simp [contents, Function.update_of_ne]

theorem step_cons (f : S → I → S) (g : S → Bool) (s₀ s : S) (a : I) (u : List I) (o : List Bool) :
    step (program f g s₀) (cfg s (a :: u) o) = some (cfg (f s a) u o) := by
  simp [program, cfg, step, stepAux, contents, update_input]

theorem step_nil (f : S → I → S) (g : S → Bool) (s₀ s : S) (o : List Bool) :
    step (program f g s₀) (cfg s ([] : List I) o) = some (done s₀ (g s :: o)) := by
  simp [program, cfg, done, step, stepAux, contents, update_input, update_output]

theorem program_run (f : S → I → S) (g : S → Bool) (s₀ s : S) (u : List I) :
    (fun q : Option (Cfg (Alphabet I) Unit (S × Option I)) => q.bind (step (program f g s₀)))^[u.length + 1]
      (some (cfg s u [])) = some (done s₀ [g (u.foldl f s)]) := by
  induction u generalizing s with
  | nil => simpa using step_nil f g s₀ s []
  | cons a u ih =>
    rw [List.length_cons, Nat.add_right_comm u.length 1 1, Function.iterate_succ_apply]
    simp only [Option.bind_some, step_cons, List.foldl_cons]
    exact ih (f s a)

def machine (I S : Type) [Fintype I] [Fintype S] (f : S → I → S) (g : S → Bool) (s₀ : S) : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet I
  Λ := Unit
  main := ()
  σ := S × Option I
  initialState := (s₀, none)
  Γk₀Fin := inferInstanceAs (Fintype I)
  m := program f g s₀

def machine_outputs [Fintype I] [Fintype S] (f : S → I → S) (g : S → Bool) (s₀ : S) (u : List I) :
    TM2OutputsInTime (machine I S f g s₀) u (some [g (u.foldl f s₀)]) (u.length + 1) := by
  have hi : initList (machine I S f g s₀) u = cfg s₀ u [] := by
    apply congrArg (fun A => (⟨some (), (s₀, none), A⟩ : Cfg (Alphabet I) Unit (S × Option I)))
    funext k; cases k <;> rfl
  have ho : haltList (machine I S f g s₀) [g (u.foldl f s₀)] = done s₀ [g (u.foldl f s₀)] := by
    apply congrArg (fun A => (⟨none, (s₀, none), A⟩ : Cfg (Alphabet I) Unit (S × Option I)))
    funext k; cases k <;> rfl
  refine ⟨⟨u.length + 1, ?_⟩, le_rfl⟩
  change (fun q : Option (Cfg (Alphabet I) Unit (S × Option I)) => q.bind (step (program f g s₀)))^[_]
    (some (initList (machine I S f g s₀) u)) = some (haltList (machine I S f g s₀) _)
  rw [hi, ho]
  exact program_run f g s₀ s₀ u

/-- Every Boolean observation of a finite-state fold is computed in `X+1`. -/
noncomputable def computable (I S : Type) [Fintype I] [Fintype S]
    (f : S → I → S) (g : S → Bool) (s₀ : S) :
    TM2ComputableInPolyTime (wordEncoding I) finEncodingBoolBool (fun u => g (u.foldl f s₀)) where
  tm := machine I S f g s₀
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + Polynomial.C 1
  outputsFun u := by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    change TM2OutputsInTime (machine I S f g s₀) (List.map id u)
      (some (List.map id [g (u.foldl f s₀)])) (u.length + 1)
    simpa only [List.map_id] using machine_outputs f g s₀ u

end ProteinFolding.TM2WordFold
