import ProteinFolding.Common.TM2Transfer
import ProteinFolding.Common.TM2CompositionPoly

/-!
# Polynomial-time projections of delimiter-tagged pairs

A generic finite-alphabet filtering machine consumes every input symbol,
reverses retained symbols through a buffer, and clears both symbol registers.
It is specialised to the left/right tags in the frozen pair format.
-/

namespace ProteinFolding.TM2PairProjections

open Computability Turing TM2

inductive Slot where
  | input
  | buffer
  | output
  deriving DecidableEq, Fintype

inductive Phase where
  | scan
  | restore
  | finish
  deriving DecidableEq, Fintype

variable {I O : Type}

def Alphabet (I O : Type) : Slot → Type
  | .input => I
  | .buffer => O
  | .output => O

def stackContents (input : List I) (buffer output : List O) : ∀ k, List (Alphabet I O k)
  | .input => input
  | .buffer => buffer
  | .output => output

theorem update_input (u u' : List I) (v w : List O) :
    Function.update (stackContents u v w) .input u' = stackContents u' v w := by
  funext k; cases k <;> simp [stackContents, Function.update_of_ne]

theorem update_buffer (u : List I) (v v' w : List O) :
    Function.update (stackContents u v w) .buffer v' = stackContents u v' w := by
  funext k; cases k <;> simp [stackContents, Function.update_of_ne]

theorem update_output (u : List I) (v w w' : List O) :
    Function.update (stackContents u v w) .output w' = stackContents u v w' := by
  funext k; cases k <;> simp [stackContents, Function.update_of_ne]

def effectiveMap (convert : I → Option O) : Option O → I → Option O
  | none => fun _ => none
  | some _ => convert

def bump : Option O → List O → List O
  | none, v => v
  | some x, v => x :: v

def program (convert : I → Option O) (seed : Option O) :
    Phase → Stmt (Alphabet I O) Phase (Option I × Option O)
  | .scan => .pop .input (fun st x => (x, st.2))
      (.branch (fun st => st.1.isSome)
        (match seed with
        | none => .goto (fun _ => .scan)
        | some x => .branch (fun st => (st.1.bind convert).isSome)
            (.push .buffer (fun st => (st.1.bind convert).getD x) (.goto (fun _ => .scan)))
            (.goto (fun _ => .scan)))
        (.goto (fun _ => .restore)))
  | .restore => match seed with
    | none => .load (fun _ => (none, none)) (.goto (fun _ => .finish))
    | some x =>
      letI : Inhabited (Alphabet I O .buffer) := ⟨x⟩
      TM2Transfer.transferStmt (Γ := Alphabet I O) (Λ := Phase) (σ := Option I)
        .buffer .output id .restore .finish
  | .finish => .halt

def cfg (label : Phase) (reg : Option I × Option O) (u : List I) (v w : List O) :
    Cfg (Alphabet I O) Phase (Option I × Option O) :=
  ⟨some label, reg, stackContents u v w⟩

theorem scan_step_cons (convert : I → Option O) (seed : Option O)
    (reg : Option I × Option O) (a : I) (u : List I) (v w : List O) :
    step (program convert seed) (cfg .scan reg (a :: u) v w) =
      some (cfg .scan (some a, reg.2) u (bump (effectiveMap convert seed a) v) w) := by
  cases seed with
  | none => simp [cfg, program, step, stepAux, stackContents, update_input, effectiveMap, bump]
  | some x =>
    cases h : convert a <;>
      simp [cfg, program, step, stepAux, stackContents, update_input, update_buffer, effectiveMap, bump, h]

theorem scan_step_nil (convert : I → Option O) (seed : Option O)
    (reg : Option I × Option O) (v w : List O) :
    step (program convert seed) (cfg .scan reg [] v w) =
      some (cfg .restore (none, reg.2) [] v w) := by
  simp [cfg, program, step, stepAux, stackContents, update_input]

theorem scan_run (convert : I → Option O) (seed : Option O)
    (reg : Option I × Option O) (u : List I) (v w : List O) :
    (fun x : Option (Cfg (Alphabet I O) Phase (Option I × Option O)) =>
      x.bind (step (program convert seed)))^[u.length + 1] (some (cfg .scan reg u v w)) =
        some (cfg .restore (none, reg.2) [] ((u.filterMap (effectiveMap convert seed)).reverse ++ v) w) := by
  induction u generalizing reg v with
  | nil => simpa using scan_step_nil convert seed reg v w
  | cons a u ih =>
    rw [List.length_cons, Nat.add_right_comm u.length 1 1, Function.iterate_succ_apply]
    simp only [Option.bind_some, scan_step_cons]
    have h := ih (some a, reg.2) (bump (effectiveMap convert seed a) v)
    cases hf : effectiveMap convert seed a <;>
      simpa [List.filterMap_cons, hf, bump, List.reverse_cons, List.append_assoc] using h

theorem transferCfg_eq (label : Phase) (reg : Option I × Option O)
    (u : List I) (v w : List O) :
    TM2Transfer.transferCfg (Γ := Alphabet I O) (Λ := Phase) .buffer .output
      label reg.1 reg.2 (stackContents u [] []) v w = cfg label reg u v w := by
  unfold TM2Transfer.transferCfg cfg
  congr 1
  funext k
  cases k <;> simp [TM2Transfer.setStacks, stackContents, Function.update_of_ne]

theorem restore_run_some (convert : I → Option O) (x : O)
    (reg : Option I × Option O) (u : List I) (v w : List O) :
    (fun c : Option (Cfg (Alphabet I O) Phase (Option I × Option O)) =>
      c.bind (step (program convert (some x))))^[v.length + 1] (some (cfg .restore reg u v w)) =
        some (cfg .finish (reg.1, none) u [] (v.reverse ++ w)) := by
  letI : Inhabited (Alphabet I O .buffer) := ⟨x⟩
  have h := TM2Transfer.transfer_run (Γ := Alphabet I O) (Λ := Phase) (σ := Option I)
    .buffer .output (by decide) id .restore .finish (program convert (some x)) rfl
    reg.1 reg.2 (stackContents u [] []) v w
  simp only [List.map_id, transferCfg_eq] at h
  exact h.trans (congrArg some (transferCfg_eq .finish (reg.1, none) u [] (v.reverse ++ w)))

theorem program_run (convert : I → Option O) (seed : Option O) (u : List I) :
    (fun c : Option (Cfg (Alphabet I O) Phase (Option I × Option O)) =>
      c.bind (step (program convert seed)))^[u.length + (u.filterMap (effectiveMap convert seed)).length + 3]
      (some (cfg .scan (none, none) u [] [])) =
        some ⟨none, (none, none), stackContents [] [] (u.filterMap (effectiveMap convert seed))⟩ := by
  have hscan := scan_run convert seed (none, none) u [] []
  simp only [List.append_nil] at hscan
  rw [show u.length + (u.filterMap (effectiveMap convert seed)).length + 3 =
      ((u.filterMap (effectiveMap convert seed)).length + 2) + (u.length + 1) by omega,
    Function.iterate_add_apply, hscan]
  cases seed with
  | none =>
    have hf : u.filterMap (effectiveMap convert none) = [] := by
      induction u <;> simp [effectiveMap, *]
    simp only [hf]
    simp [cfg, program, step, stepAux]
  | some x =>
    rw [show (u.filterMap (effectiveMap convert (some x))).length + 2 =
        ((u.filterMap (effectiveMap convert (some x))).reverse.length + 1) + 1 by simp,
      Function.iterate_succ_apply', restore_run_some]
    simp [cfg, program, step, stepAux]

def machine (I O : Type) [Fintype I] [Fintype O] (convert : I → Option O) (seed : Option O) : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet I O
  Λ := Phase
  main := .scan
  σ := Option I × Option O
  initialState := (none, none)
  Γk₀Fin := inferInstanceAs (Fintype I)
  m := program convert seed

theorem effectiveMap_eq (convert : I → Option O) (seed : Option O)
    (hseed : seed = none → IsEmpty O) : effectiveMap convert seed = convert := by
  funext a
  cases seed with
  | some x => rfl
  | none =>
    cases h : convert a with
    | none => rfl
    | some x => exact False.elim ((hseed rfl).false x)

def machine_outputs (I O : Type) [Fintype I] [Fintype O]
    (convert : I → Option O) (seed : Option O) (hseed : seed = none → IsEmpty O) (u : List I) :
    TM2OutputsInTime (machine I O convert seed) u (some (u.filterMap convert)) (2 * u.length + 3) := by
  have hi : initList (machine I O convert seed) u = cfg .scan (none, none) u [] [] := by
    apply congrArg (fun S : ∀ k, List (Alphabet I O k) =>
      (⟨some .scan, (none, none), S⟩ : Cfg (Alphabet I O) Phase (Option I × Option O)))
    funext k
    cases k <;> rfl
  have ho : haltList (machine I O convert seed) (u.filterMap convert) =
      (⟨none, (none, none), stackContents [] [] (u.filterMap convert)⟩ :
        Cfg (Alphabet I O) Phase (Option I × Option O)) := by
    apply congrArg (fun S : ∀ k, List (Alphabet I O k) =>
      (⟨none, (none, none), S⟩ : Cfg (Alphabet I O) Phase (Option I × Option O)))
    funext k
    cases k <;> rfl
  refine
    { steps := u.length + (u.filterMap convert).length + 3
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · rw [hi]
    change _ = some (haltList (machine I O convert seed) (u.filterMap convert))
    rw [ho]
    simpa only [effectiveMap_eq convert seed hseed] using program_run convert seed u
  · have h := List.length_filterMap_le convert u
    omega

noncomputable def filterMapComputable (I O : Type) [Fintype I] [Fintype O]
    (convert : I → Option O) :
    TM2ComputableInPolyTime (wordEncoding I) (wordEncoding O) (List.filterMap convert) where
  tm := machine I O convert (TM2CompositionPoly.alphabetSeed O)
  inputAlphabet := Equiv.refl I
  outputAlphabet := Equiv.refl O
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun u := by
    have h := machine_outputs I O convert (TM2CompositionPoly.alphabetSeed O)
      (TM2CompositionPoly.alphabetSeed_none O) u
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime (machine I O convert (TM2CompositionPoly.alphabetSeed O))
      (List.map id u) (some (List.map id (u.filterMap convert))) (2 * u.length + 3)
    simpa only [List.map_id] using h

def takeLeft : PairSymbol I O → Option I
  | .left a => some a
  | _ => none

def takeRight : PairSymbol I O → Option O
  | .right b => some b
  | _ => none

theorem discard_all (u : List I) : u.filterMap (fun _ => (none : Option O)) = [] := by
  induction u <;> simp [*]

theorem takeLeft_join (u : List I) (v : List O) :
    (u.map PairSymbol.left ++ PairSymbol.sep :: v.map PairSymbol.right).filterMap takeLeft = u := by
  simp [List.filterMap_append, List.filterMap_map, Function.comp_def, takeLeft, discard_all]

theorem takeRight_join (u : List I) (v : List O) :
    (u.map PairSymbol.left ++ PairSymbol.sep :: v.map PairSymbol.right).filterMap takeRight = v := by
  simp [List.filterMap_append, List.filterMap_map, Function.comp_def, takeRight, discard_all]

noncomputable def fstComputable {A B : Type} (ea : FinEncoding A) (eb : FinEncoding B) :
    TM2ComputableInPolyTime (pairEncoding ea eb) ea Prod.fst := by
  letI := ea.ΓFin
  letI := eb.ΓFin
  let h := filterMapComputable (PairSymbol ea.Γ eb.Γ) ea.Γ takeLeft
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun ab => by
        have hout := h.outputsFun ((pairEncoding ea eb).encode ab)
        have hword : ((pairEncoding ea eb).encode ab).filterMap takeLeft = ea.encode ab.1 :=
          takeLeft_join (ea.encode ab.1) (eb.encode ab.2)
        change TM2OutputsInTime h.tm
          (((pairEncoding ea eb).encode ab).map h.inputAlphabet.symm)
          (some ((ea.encode ab.1).map h.outputAlphabet.symm))
          (h.time.eval ((pairEncoding ea eb).encode ab).length)
        simpa only [wordEncoding, hword] using hout }

noncomputable def sndComputable {A B : Type} (ea : FinEncoding A) (eb : FinEncoding B) :
    TM2ComputableInPolyTime (pairEncoding ea eb) eb Prod.snd := by
  letI := ea.ΓFin
  letI := eb.ΓFin
  let h := filterMapComputable (PairSymbol ea.Γ eb.Γ) eb.Γ takeRight
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun ab => by
        have hout := h.outputsFun ((pairEncoding ea eb).encode ab)
        have hword : ((pairEncoding ea eb).encode ab).filterMap takeRight = eb.encode ab.2 :=
          takeRight_join (ea.encode ab.1) (eb.encode ab.2)
        change TM2OutputsInTime h.tm
          (((pairEncoding ea eb).encode ab).map h.inputAlphabet.symm)
          (some ((eb.encode ab.2).map h.outputAlphabet.symm))
          (h.time.eval ((pairEncoding ea eb).encode ab).length)
        simpa only [wordEncoding, hword] using hout }

def takeEither {A : Type} : PairSymbol A A → Option A
  | .left a => some a
  | .right a => some a
  | .sep => none

theorem takeEither_join {A : Type} (u v : List A) :
    (u.map PairSymbol.left ++ PairSymbol.sep :: v.map PairSymbol.right).filterMap takeEither = u ++ v := by
  simp [List.filterMap_append, List.filterMap_map, Function.comp_def, takeEither]

/-- Concatenate two explicitly encoded words by retaining both sets of tags
and discarding the separator. Its scan consumes the entire tagged input. -/
noncomputable def concatComputable (A : Type) [Fintype A] :
    TM2ComputableInPolyTime (pairEncoding (wordEncoding A) (wordEncoding A))
      (wordEncoding A) (fun p => p.1 ++ p.2) := by
  let h := filterMapComputable (PairSymbol A A) A takeEither
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun uv => by
        have hout := h.outputsFun ((pairEncoding (wordEncoding A) (wordEncoding A)).encode uv)
        have hword :
            ((pairEncoding (wordEncoding A) (wordEncoding A)).encode uv).filterMap takeEither = uv.1 ++ uv.2 :=
          takeEither_join uv.1 uv.2
        change TM2OutputsInTime h.tm
          (((pairEncoding (wordEncoding A) (wordEncoding A)).encode uv).map h.inputAlphabet.symm)
          (some ((uv.1 ++ uv.2).map h.outputAlphabet.symm))
          (h.time.eval ((pairEncoding (wordEncoding A) (wordEncoding A)).encode uv).length)
        change TM2OutputsInTime h.tm
          (((pairEncoding (wordEncoding A) (wordEncoding A)).encode uv).map h.inputAlphabet.symm)
          (some ((((pairEncoding (wordEncoding A) (wordEncoding A)).encode uv).filterMap takeEither).map
            h.outputAlphabet.symm))
          (h.time.eval ((pairEncoding (wordEncoding A) (wordEncoding A)).encode uv).length) at hout
        rw [hword] at hout
        exact hout }

theorem concatComputable_time (A : Type) [Fintype A] :
    (concatComputable A).time = Polynomial.C 2 * Polynomial.X + Polynomial.C 3 := rfl

end ProteinFolding.TM2PairProjections
