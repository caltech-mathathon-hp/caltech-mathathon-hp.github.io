import ProteinFolding.Common.TM2Transfer
import ProteinFolding.Common.TM2WordMap

/-! An explicit input-duplication machine for the frozen tagged pair format.
The two tagged buffers are reversed during scanning, then drained in the order
needed to place the left word before the separator before the right word.
The separator provides a harmless total fallback symbol, including empty input
alphabets; no nonemptiness assumption is required. -/

namespace ProteinFolding.TM2Fanout

open Computability Turing TM2

inductive Slot where
  | input
  | left
  | right
  | output
  deriving DecidableEq, Fintype

inductive Phase where
  | scan
  | drainRight
  | separator
  | drainLeft
  | finish
  deriving DecidableEq, Fintype

variable {A : Type}

abbrev Out (A : Type) := PairSymbol A A

def Alphabet (A : Type) : Slot → Type
  | .input => A
  | _ => Out A

def stackContents (u : List A) (v r w : List (Out A)) : ∀ k, List (Alphabet A k)
  | .input => u
  | .left => v
  | .right => r
  | .output => w

theorem update_input (u u' : List A) (v r w : List (Out A)) :
    Function.update (stackContents u v r w) .input u' = stackContents u' v r w := by
  funext k; cases k <;> simp [stackContents, Function.update_of_ne]

theorem update_left (u : List A) (v v' r w : List (Out A)) :
    Function.update (stackContents u v r w) .left v' = stackContents u v' r w := by
  funext k; cases k <;> simp [stackContents, Function.update_of_ne]

theorem update_right (u : List A) (v r r' w : List (Out A)) :
    Function.update (stackContents u v r w) .right r' = stackContents u v r' w := by
  funext k; cases k <;> simp [stackContents, Function.update_of_ne]

theorem update_output (u : List A) (v r w w' : List (Out A)) :
    Function.update (stackContents u v r w) .output w' = stackContents u v r w' := by
  funext k; cases k <;> simp [stackContents, Function.update_of_ne]

def program (A : Type) : Phase → Stmt (Alphabet A) Phase (Option A × Option (Out A))
  | .scan => .pop .input (fun st x => (x, st.2))
      (.branch (fun st => st.1.isSome)
        (.push .left (fun st => st.1.elim PairSymbol.sep PairSymbol.left)
          (.push .right (fun st => st.1.elim PairSymbol.sep PairSymbol.right)
            (.goto (fun _ => .scan))))
        (.goto (fun _ => .drainRight)))
  | .drainRight =>
      letI : Inhabited (Alphabet A .right) := ⟨PairSymbol.sep⟩
      TM2Transfer.transferStmt (Γ := Alphabet A) (Λ := Phase) (σ := Option A)
        .right .output id .drainRight .separator
  | .separator => .push .output (fun _ => PairSymbol.sep) (.goto (fun _ => .drainLeft))
  | .drainLeft =>
      letI : Inhabited (Alphabet A .left) := ⟨PairSymbol.sep⟩
      TM2Transfer.transferStmt (Γ := Alphabet A) (Λ := Phase) (σ := Option A)
        .left .output id .drainLeft .finish
  | .finish => .halt

def cfg (label : Phase) (reg : Option A × Option (Out A))
    (u : List A) (v r w : List (Out A)) : Cfg (Alphabet A) Phase (Option A × Option (Out A)) :=
  ⟨some label, reg, stackContents u v r w⟩

theorem scan_step_cons (reg : Option A × Option (Out A))
    (a : A) (u : List A) (v r w : List (Out A)) :
    step (program A) (cfg .scan reg (a :: u) v r w) =
      some (cfg .scan (some a, reg.2) u (PairSymbol.left a :: v) (PairSymbol.right a :: r) w) := by
  simp [cfg, program, step, stepAux, stackContents, update_input, update_left, update_right]

theorem scan_step_nil (reg : Option A × Option (Out A)) (v r w : List (Out A)) :
    step (program A) (cfg .scan reg [] v r w) =
      some (cfg .drainRight (none, reg.2) [] v r w) := by
  simp [cfg, program, step, stepAux, stackContents, update_input]

theorem scan_run (reg : Option A × Option (Out A))
    (u : List A) (v r w : List (Out A)) :
    (fun c : Option (Cfg (Alphabet A) Phase (Option A × Option (Out A))) =>
      c.bind (step (program A)))^[u.length + 1] (some (cfg .scan reg u v r w)) =
        some (cfg .drainRight (none, reg.2) []
          ((u.map PairSymbol.left).reverse ++ v) ((u.map PairSymbol.right).reverse ++ r) w) := by
  induction u generalizing reg v r with
  | nil => simpa using scan_step_nil reg v r w
  | cons a u ih =>
    rw [List.length_cons, Nat.add_right_comm u.length 1 1, Function.iterate_succ_apply]
    simp only [Option.bind_some, scan_step_cons]
    simpa [List.map_cons, List.reverse_cons, List.append_assoc] using
      ih (some a, reg.2) (PairSymbol.left a :: v) (PairSymbol.right a :: r)

theorem transferRightCfg_eq (label : Phase) (reg : Option A × Option (Out A))
    (u : List A) (v r w : List (Out A)) :
    TM2Transfer.transferCfg (Γ := Alphabet A) (Λ := Phase) .right .output label
      reg.1 reg.2 (stackContents u v [] []) r w = cfg label reg u v r w := by
  unfold TM2Transfer.transferCfg cfg
  congr 1
  funext k
  cases k <;> simp [TM2Transfer.setStacks, stackContents, Function.update_of_ne]

theorem drainRight_run (reg : Option A × Option (Out A))
    (u : List A) (v r w : List (Out A)) :
    (fun c : Option (Cfg (Alphabet A) Phase (Option A × Option (Out A))) =>
      c.bind (step (program A)))^[r.length + 1] (some (cfg .drainRight reg u v r w)) =
        some (cfg .separator (reg.1, none) u v [] (r.reverse ++ w)) := by
  letI : Inhabited (Alphabet A .right) := ⟨PairSymbol.sep⟩
  have h := TM2Transfer.transfer_run (Γ := Alphabet A) (Λ := Phase) (σ := Option A)
    .right .output (by decide) id .drainRight .separator (program A) rfl
    reg.1 reg.2 (stackContents u v [] []) r w
  simp only [List.map_id, transferRightCfg_eq] at h
  exact h.trans (congrArg some (transferRightCfg_eq .separator (reg.1, none) u v [] (r.reverse ++ w)))

theorem transferLeftCfg_eq (label : Phase) (reg : Option A × Option (Out A))
    (u : List A) (v r w : List (Out A)) :
    TM2Transfer.transferCfg (Γ := Alphabet A) (Λ := Phase) .left .output label
      reg.1 reg.2 (stackContents u [] r []) v w = cfg label reg u v r w := by
  unfold TM2Transfer.transferCfg cfg
  congr 1
  funext k
  cases k <;> simp [TM2Transfer.setStacks, stackContents, Function.update_of_ne]

theorem drainLeft_run (reg : Option A × Option (Out A))
    (u : List A) (v r w : List (Out A)) :
    (fun c : Option (Cfg (Alphabet A) Phase (Option A × Option (Out A))) =>
      c.bind (step (program A)))^[v.length + 1] (some (cfg .drainLeft reg u v r w)) =
        some (cfg .finish (reg.1, none) u [] r (v.reverse ++ w)) := by
  letI : Inhabited (Alphabet A .left) := ⟨PairSymbol.sep⟩
  have h := TM2Transfer.transfer_run (Γ := Alphabet A) (Λ := Phase) (σ := Option A)
    .left .output (by decide) id .drainLeft .finish (program A) rfl
    reg.1 reg.2 (stackContents u [] r []) v w
  simp only [List.map_id, transferLeftCfg_eq] at h
  exact h.trans (congrArg some (transferLeftCfg_eq .finish (reg.1, none) u [] r (v.reverse ++ w)))

theorem separator_step (reg : Option A × Option (Out A))
    (u : List A) (v r w : List (Out A)) :
    step (program A) (cfg .separator reg u v r w) =
      some (cfg .drainLeft reg u v r (PairSymbol.sep :: w)) := by
  simp [cfg, program, step, stepAux, stackContents, update_output]

theorem program_run (u : List A) :
    (fun c : Option (Cfg (Alphabet A) Phase (Option A × Option (Out A))) =>
      c.bind (step (program A)))^[3 * u.length + 5] (some (cfg .scan (none, none) u [] [] [])) =
        some ⟨none, (none, none),
          stackContents [] [] [] (u.map PairSymbol.left ++ PairSymbol.sep :: u.map PairSymbol.right)⟩ := by
  have hs := scan_run (none, none) u [] [] []
  simp only [List.append_nil] at hs
  have hr := drainRight_run (none, none) ([] : List A)
    (u.map PairSymbol.left).reverse (u.map PairSymbol.right).reverse []
  simp only [List.length_reverse, List.length_map, List.reverse_reverse, List.append_nil] at hr
  have hl := drainLeft_run (none, none) ([] : List A)
    (u.map PairSymbol.left).reverse [] (PairSymbol.sep :: u.map PairSymbol.right)
  simp only [List.length_reverse, List.length_map, List.reverse_reverse] at hl
  rw [show 3 * u.length + 5 = ((u.length + 2) + 1) + (u.length + 1) + (u.length + 1) by omega,
    Function.iterate_add_apply, hs, Function.iterate_add_apply, hr,
    Function.iterate_succ_apply]
  simp only [Option.bind_some, separator_step]
  rw [show u.length + 2 = (u.length + 1) + 1 by omega,
    Function.iterate_succ_apply', hl]
  rfl

def machine (A : Type) [Fintype A] : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet A
  Λ := Phase
  main := .scan
  σ := Option A × Option (Out A)
  initialState := (none, none)
  Γk₀Fin := inferInstanceAs (Fintype A)
  m := program A

def machine_outputs (A : Type) [Fintype A] (u : List A) :
    TM2OutputsInTime (machine A) u
      (some (u.map PairSymbol.left ++ PairSymbol.sep :: u.map PairSymbol.right)) (3 * u.length + 5) := by
  have hi : initList (machine A) u = cfg .scan (none, none) u [] [] [] := by
    apply congrArg (fun S : ∀ k, List (Alphabet A k) =>
      (⟨some .scan, (none, none), S⟩ : Cfg (Alphabet A) Phase (Option A × Option (Out A))))
    funext k
    cases k <;> rfl
  have ho : haltList (machine A) (u.map PairSymbol.left ++ PairSymbol.sep :: u.map PairSymbol.right) =
      (⟨none, (none, none), stackContents [] [] []
        (u.map PairSymbol.left ++ PairSymbol.sep :: u.map PairSymbol.right)⟩ :
          Cfg (Alphabet A) Phase (Option A × Option (Out A))) := by
    apply congrArg (fun S : ∀ k, List (Alphabet A k) =>
      (⟨none, (none, none), S⟩ : Cfg (Alphabet A) Phase (Option A × Option (Out A))))
    funext k
    cases k <;> rfl
  refine { steps := 3 * u.length + 5, evals_in_steps := ?_, steps_le_m := le_rfl }
  rw [hi]
  change _ = some (haltList (machine A) _)
  rw [ho]
  exact program_run u

/-- Copy an encoded typed input into both fields of the existing tagged pair
encoding. Each residue or binary symbol is physically copied by the machine. -/
noncomputable def diagonalComputable {X : Type} (ea : FinEncoding X) :
    TM2ComputableInPolyTime ea (pairEncoding ea ea) (fun x => (x, x)) where
  tm := machine ea.Γ
  inputAlphabet := Equiv.refl ea.Γ
  outputAlphabet := Equiv.refl (PairSymbol ea.Γ ea.Γ)
  time := Polynomial.C 3 * Polynomial.X + Polynomial.C 5
  outputsFun x := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime (machine ea.Γ) (List.map id (ea.encode x))
      (some (List.map id ((ea.encode x).map PairSymbol.left ++ PairSymbol.sep :: (ea.encode x).map PairSymbol.right)))
      (3 * (ea.encode x).length + 5)
    simpa only [List.map_id] using machine_outputs ea.Γ (ea.encode x)

theorem diagonalComputable_time {X : Type} (ea : FinEncoding X) :
    (diagonalComputable ea).time = Polynomial.C 3 * Polynomial.X + Polynomial.C 5 := rfl

def coordinateTag {B C : Type} : PairSymbol (B × C) (B × C) → PairSymbol B C
  | .left x => .left x.1
  | .right x => .right x.2
  | .sep => .sep

noncomputable def splitCoordinatesComputable (B C : Type) [Fintype B] [Fintype C] :
    TM2ComputableInPolyTime
      (pairEncoding (wordEncoding (B × C)) (wordEncoding (B × C)))
      (pairEncoding (wordEncoding B) (wordEncoding C))
      (fun p => (p.1.map Prod.fst, p.2.map Prod.snd)) := by
  let source := pairEncoding (wordEncoding (B × C)) (wordEncoding (B × C))
  let target := pairEncoding (wordEncoding B) (wordEncoding C)
  let h := TM2WordMap.mapComputable (coordinateTag (B := B) (C := C))
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun p => by
        have hw : (source.encode p).map coordinateTag =
            target.encode (p.1.map Prod.fst, p.2.map Prod.snd) := by
          simp [source, target, pairEncoding, wordEncoding, List.map_append, List.map_map,
            coordinateTag, Function.comp_def]
        have hr := h.outputsFun (source.encode p)
        change TM2OutputsInTime h.tm ((source.encode p).map h.inputAlphabet.symm)
          (some ((target.encode (p.1.map Prod.fst, p.2.map Prod.snd)).map h.outputAlphabet.symm))
          (h.time.eval (source.encode p).length)
        change TM2OutputsInTime h.tm ((source.encode p).map h.inputAlphabet.symm)
          (some (((source.encode p).map coordinateTag).map h.outputAlphabet.symm))
          (h.time.eval (source.encode p).length) at hr
        rw [hw] at hr
        exact hr }

/-- Actual simultaneous symbolwise maps, obtained from the copying machine
and total finite-alphabet maps. This is not general pairing of arbitrary
polynomial-time algorithms. -/
noncomputable def wordFanoutComputable {I B C : Type} [Fintype I] [Fintype B] [Fintype C]
    (f : I → B) (g : I → C) :
    TM2ComputableInPolyTime (wordEncoding I)
      (pairEncoding (wordEncoding B) (wordEncoding C)) (fun u => (u.map f, u.map g)) := by
  let hmap := TM2WordMap.mapComputable (fun i => (f i, g i))
  let hdiag := diagonalComputable (wordEncoding (B × C))
  let hsplit := splitCoordinatesComputable B C
  let h := TM2CompositionPoly.compose (TM2CompositionPoly.compose hmap hdiag) hsplit
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := fun u => by
        simpa only [Function.comp_apply, List.map_map, Function.comp_def] using h.outputsFun u }

end ProteinFolding.TM2Fanout
