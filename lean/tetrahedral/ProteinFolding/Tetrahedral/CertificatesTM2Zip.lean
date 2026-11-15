import ProteinFolding.Tetrahedral.CertificatesTM2Records
import ProteinFolding.Common.TM2Transfer

/-! An explicit linear-time TM2 zipper for the frozen sequence/direction
certificate. The previous direction is a finite control register. Every
unmatched symbol emits an explicit malformed record. -/

namespace ProteinFolding.Tetrahedral.CertificatesTM2Zip

open Computability Turing TM2

abbrev Record := Residue × Fin 4
abbrev Letter := Option Record
abbrev Symbol := PairSymbol Residue (Fin 4)

def zipRecords : Fin 4 → Sequence → DirectionWord → List Letter
  | _, [], [] => []
  | p, r :: rs, d :: ds => some (r, p) :: zipRecords d rs ds
  | _, [], d :: ds => none :: zipRecords d [] ds
  | _, _ :: rs, [] => none :: zipRecords 0 rs []

def zipPrevious : Fin 4 → Sequence → DirectionWord → Fin 4
  | p, [], [] => p
  | _, _ :: rs, d :: ds => zipPrevious d rs ds
  | _, [], d :: ds => zipPrevious d [] ds
  | _, _ :: rs, [] => zipPrevious 0 rs []

theorem zipRecords_length (p : Fin 4) (rs : Sequence) (ds : DirectionWord) :
    (zipRecords p rs ds).length = max rs.length ds.length := by
  induction rs generalizing p ds with
  | nil =>
    induction ds generalizing p with
    | nil => simp [zipRecords]
    | cons d ds ih => simp [zipRecords, ih]
  | cons r rs ih =>
    cases ds with
    | nil => simp [zipRecords, ih]
    | cons d ds => simp [zipRecords, ih, Nat.succ_max_succ]

inductive Slot where
  | input | residueBuffer | residues | recordBuffer | output
  deriving DecidableEq, Fintype

inductive Phase where
  | read | restoreResidues | zip | restoreRecords | finish
  deriving DecidableEq, Fintype

def Alphabet : Slot → Type
  | .input => Symbol
  | .residueBuffer | .residues => Residue
  | .recordBuffer | .output => Letter

structure Reg where
  symbol : Option Symbol
  residue : Option Residue
  direction : Option (Fin 4)
  token : Option Letter
  previous : Fin 4
  deriving DecidableEq, Fintype

def reg (p : Fin 4) : Reg := ⟨none, none, none, none, p⟩

def contents (u : List Symbol) (b r : Sequence) (v w : List Letter) :
    ∀ k, List (Alphabet k)
  | .input => u
  | .residueBuffer => b
  | .residues => r
  | .recordBuffer => v
  | .output => w

def cfg (phase : Phase) (st : Reg) (u : List Symbol) (b r : Sequence) (v w : List Letter) :
    Cfg Alphabet Phase Reg := ⟨some phase, st, contents u b r v w⟩

theorem update_input (u u' : List Symbol) (b r : Sequence) (v w : List Letter) :
    Function.update (contents u b r v w) .input u' = contents u' b r v w := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_residueBuffer (u : List Symbol) (b b' r : Sequence) (v w : List Letter) :
    Function.update (contents u b r v w) .residueBuffer b' = contents u b' r v w := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_residues (u : List Symbol) (b r r' : Sequence) (v w : List Letter) :
    Function.update (contents u b r v w) .residues r' = contents u b r' v w := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_recordBuffer (u : List Symbol) (b r : Sequence) (v v' w : List Letter) :
    Function.update (contents u b r v w) .recordBuffer v' = contents u b r v' w := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_output (u : List Symbol) (b r : Sequence) (v w w' : List Letter) :
    Function.update (contents u b r v w) .output w' = contents u b r v w' := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

def readResidue : Option Symbol → Option Residue
  | some (.left r) => some r
  | _ => none

def readDirection : Option Symbol → Option (Fin 4)
  | some (.right d) => some d
  | _ => none

def emitLetter (st : Reg) : Letter :=
  match st.residue, st.direction with
  | some r, some _ => some (r, st.previous)
  | _, _ => none

def program : Phase → Stmt Alphabet Phase Reg
  | .read => .pop .input (fun st o => { st with symbol := o })
      (.branch (fun st => (readResidue st.symbol).isSome)
        (.push .residueBuffer (fun st => (readResidue st.symbol).getD Residue.H)
          (.load (fun st => reg st.previous) (.goto (fun _ => .read))))
        (.load (fun st => reg st.previous) (.goto (fun _ => .restoreResidues))))
  | .restoreResidues => .pop .residueBuffer (fun st o => { st with residue := o })
      (.branch (fun st => st.residue.isSome)
        (.push .residues (fun st => st.residue.getD Residue.H)
          (.load (fun st => reg st.previous) (.goto (fun _ => .restoreResidues))))
        (.load (fun st => reg st.previous) (.goto (fun _ => .zip))))
  | .zip => .pop .residues (fun st o => { st with residue := o })
      (.pop .input (fun st o => { st with direction := readDirection o })
        (.branch (fun st => st.residue.isSome || st.direction.isSome)
          (.push .recordBuffer emitLetter
            (.load (fun st => reg (st.direction.getD 0)) (.goto (fun _ => .zip))))
          (.load (fun st => reg st.previous) (.goto (fun _ => .restoreRecords)))))
  | .restoreRecords => .pop .recordBuffer (fun st o => { st with token := o })
      (.branch (fun st => st.token.isSome)
        (.push .output (fun st => st.token.getD none)
          (.load (fun st => reg st.previous) (.goto (fun _ => .restoreRecords))))
        (.load (fun st => reg st.previous) (.goto (fun _ => .finish))))
  | .finish => .load (fun _ => reg 0) .halt

def run (n : ℕ) (q : Cfg Alphabet Phase Reg) : Option (Cfg Alphabet Phase Reg) :=
  (fun x : Option (Cfg Alphabet Phase Reg) => x.bind (Turing.TM2.step program))^[n] (some q)

theorem run_step {q q' : Cfg Alphabet Phase Reg} (h : Turing.TM2.step program q = some q') (n : ℕ) :
    run (n + 1) q = run n q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]

theorem run_add {q q' : Cfg Alphabet Phase Reg} {n : ℕ} (h : run n q = some q') (m : ℕ) :
    run (n + m) q = run m q' := by
  unfold run at *
  rw [Nat.add_comm n m, Function.iterate_add_apply, h]

theorem read_step_cons (p : Fin 4) (r : Residue) (u : List Symbol) (b s : Sequence) (v w : List Letter) :
    Turing.TM2.step program (cfg .read (reg p) (.left r :: u) b s v w) =
      some (cfg .read (reg p) u (r :: b) s v w) := by
  simp [cfg, program, reg, Turing.TM2.step, stepAux, readResidue, contents,
    update_input, update_residueBuffer]

theorem read_step_sep (p : Fin 4) (u : List Symbol) (b s : Sequence) (v w : List Letter) :
    Turing.TM2.step program (cfg .read (reg p) (.sep :: u) b s v w) =
      some (cfg .restoreResidues (reg p) u b s v w) := by
  simp [cfg, program, reg, Turing.TM2.step, stepAux, readResidue, contents, update_input]

theorem read_run (p : Fin 4) (rs : Sequence) (u : List Symbol) (b s : Sequence) (v w : List Letter) :
    run (rs.length + 1) (cfg .read (reg p) (rs.map PairSymbol.left ++ .sep :: u) b s v w) =
      some (cfg .restoreResidues (reg p) u (rs.reverse ++ b) s v w) := by
  induction rs generalizing b with
  | nil => exact read_step_sep p u b s v w
  | cons r rs ih =>
    rw [List.length_cons, List.map_cons, List.cons_append, run_step (read_step_cons p r _ b s v w)]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (r :: b)

theorem residue_step_cons (p : Fin 4) (r : Residue) (u : List Symbol) (b s : Sequence) (v w : List Letter) :
    Turing.TM2.step program (cfg .restoreResidues (reg p) u (r :: b) s v w) =
      some (cfg .restoreResidues (reg p) u b (r :: s) v w) := by
  simp [cfg, program, reg, Turing.TM2.step, stepAux, contents,
    update_residueBuffer, update_residues]

theorem residue_step_nil (p : Fin 4) (u : List Symbol) (s : Sequence) (v w : List Letter) :
    Turing.TM2.step program (cfg .restoreResidues (reg p) u [] s v w) =
      some (cfg .zip (reg p) u [] s v w) := by
  simp [cfg, program, reg, Turing.TM2.step, stepAux, contents, update_residueBuffer]

theorem residue_run (p : Fin 4) (u : List Symbol) (b s : Sequence) (v w : List Letter) :
    run (b.length + 1) (cfg .restoreResidues (reg p) u b s v w) =
      some (cfg .zip (reg p) u [] (b.reverse ++ s) v w) := by
  induction b generalizing s with
  | nil => exact residue_step_nil p u s v w
  | cons r b ih =>
    rw [List.length_cons, run_step (residue_step_cons p r u b s v w)]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (r :: s)

theorem zip_step (p : Fin 4) (rs : Sequence) (ds : DirectionWord) (v w : List Letter)
    (h : rs ≠ [] ∨ ds ≠ []) :
    Turing.TM2.step program (cfg .zip (reg p) (ds.map PairSymbol.right) [] rs v w) =
      some (cfg .zip (reg (ds.head?.getD 0)) (ds.tail.map PairSymbol.right) [] rs.tail
        ((match rs.head?, ds.head? with
          | some r, some _ => some (r, p)
          | _, _ => none) :: v) w) := by
  cases rs <;> cases ds <;>
    simp_all [cfg, program, reg, Turing.TM2.step, stepAux, contents, readDirection,
      emitLetter, update_input, update_residues, update_recordBuffer]

theorem zip_step_nil (p : Fin 4) (v w : List Letter) :
    Turing.TM2.step program (cfg .zip (reg p) [] [] [] v w) =
      some (cfg .restoreRecords (reg p) [] [] [] v w) := by
  simp [cfg, program, reg, Turing.TM2.step, stepAux, contents, readDirection,
    update_input, update_residues]

theorem zip_run (p : Fin 4) (rs : Sequence) (ds : DirectionWord) (v w : List Letter) :
    run (max rs.length ds.length + 1) (cfg .zip (reg p) (ds.map PairSymbol.right) [] rs v w) =
      some (cfg .restoreRecords (reg (zipPrevious p rs ds)) [] [] []
        ((zipRecords p rs ds).reverse ++ v) w) := by
  induction rs generalizing p ds v with
  | nil =>
    induction ds generalizing p v with
    | nil => simpa [run, zipPrevious, zipRecords] using zip_step_nil p v w
    | cons d ds ih =>
      simp only [List.length_nil, List.length_cons, Nat.zero_max]
      rw [run_step (zip_step p [] (d :: ds) v w (Or.inr (by simp)))]
      simpa only [List.head?_cons, List.head?_nil, Option.getD_some, List.tail_cons,
        List.tail_nil, List.length_nil, Nat.zero_max, zipPrevious, zipRecords,
        List.reverse_cons, List.append_assoc, List.singleton_append] using ih d (none :: v)
  | cons r rs ih =>
    cases ds with
    | nil =>
      simp only [List.length_nil, List.length_cons, Nat.max_zero]
      rw [run_step (zip_step p (r :: rs) [] v w (Or.inl (by simp)))]
      simpa only [List.head?_nil, List.head?_cons, Option.getD_none, List.tail_nil,
        List.tail_cons, List.length_nil, Nat.max_zero, zipPrevious, zipRecords,
        List.reverse_cons, List.append_assoc, List.singleton_append, List.map_nil] using ih 0 [] (none :: v)
    | cons d ds =>
      simp only [List.length_cons, Nat.succ_max_succ]
      rw [run_step (zip_step p (r :: rs) (d :: ds) v w (Or.inl (by simp)))]
      simpa only [List.head?_cons, Option.getD_some, List.tail_cons, zipPrevious, zipRecords,
        List.reverse_cons, List.append_assoc, List.singleton_append] using ih d ds (some (r, p) :: v)

theorem record_step_cons (p : Fin 4) (a : Letter) (u : List Symbol) (b s : Sequence) (v w : List Letter) :
    Turing.TM2.step program (cfg .restoreRecords (reg p) u b s (a :: v) w) =
      some (cfg .restoreRecords (reg p) u b s v (a :: w)) := by
  simp [cfg, program, reg, Turing.TM2.step, stepAux, contents, update_recordBuffer, update_output]

theorem record_step_nil (p : Fin 4) (u : List Symbol) (b s : Sequence) (w : List Letter) :
    Turing.TM2.step program (cfg .restoreRecords (reg p) u b s [] w) =
      some (cfg .finish (reg p) u b s [] w) := by
  simp [cfg, program, reg, Turing.TM2.step, stepAux, contents, update_recordBuffer]

theorem record_run (p : Fin 4) (u : List Symbol) (b s : Sequence) (v w : List Letter) :
    run (v.length + 1) (cfg .restoreRecords (reg p) u b s v w) =
      some (cfg .finish (reg p) u b s [] (v.reverse ++ w)) := by
  induction v generalizing w with
  | nil => exact record_step_nil p u b s w
  | cons a v ih =>
    rw [List.length_cons, run_step (record_step_cons p a u b s v w)]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (a :: w)

theorem program_run (rs : Sequence) (ds : DirectionWord) :
    run (2 * rs.length + 2 * max rs.length ds.length + 5)
      (cfg .read (reg 0) (rs.map PairSymbol.left ++ .sep :: ds.map PairSymbol.right) [] [] [] []) =
      some ⟨none, reg 0, contents [] [] [] [] (zipRecords 0 rs ds)⟩ := by
  rw [show 2 * rs.length + 2 * max rs.length ds.length + 5 =
      (rs.length + 1) + ((rs.reverse.length + 1) +
        ((max rs.length ds.length + 1) + ((zipRecords 0 rs ds).reverse.length + 1 + 1))) by
        simp only [List.length_reverse, zipRecords_length]; omega]
  rw [run_add (read_run 0 rs _ [] [] [] [])]
  simp only [List.append_nil]
  rw [run_add (residue_run 0 _ rs.reverse [] [] [])]
  simp only [List.reverse_reverse, List.append_nil]
  rw [run_add (zip_run 0 rs ds [] [])]
  simp only [List.append_nil]
  rw [run_add (record_run _ [] [] [] (zipRecords 0 rs ds).reverse [])]
  simp only [List.reverse_reverse, List.append_nil]
  rfl

def machine : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Phase
  main := .read
  σ := Reg
  initialState := reg 0
  Γk₀Fin := inferInstanceAs (Fintype Symbol)
  m := program

theorem initList_eq (u : List Symbol) : initList machine u = cfg .read (reg 0) u [] [] [] [] := by
  apply congrArg (fun S => (⟨some .read, reg 0, S⟩ : Cfg Alphabet Phase Reg))
  funext k; cases k <;> rfl

theorem haltList_eq (w : List Letter) :
    haltList machine w = (⟨none, reg 0, contents [] [] [] [] w⟩ : Cfg Alphabet Phase Reg) := by
  apply congrArg (fun S => (⟨none, reg 0, S⟩ : Cfg Alphabet Phase Reg))
  funext k; cases k <;> rfl

def machine_outputs (rs : Sequence) (ds : DirectionWord) : TM2OutputsInTime machine
    ((pairEncoding sequenceEncoding directionEncoding).encode (rs, ds))
    (some (zipRecords 0 rs ds))
    (4 * ((pairEncoding sequenceEncoding directionEncoding).encode (rs, ds)).length + 5) := by
  refine { steps := 2 * rs.length + 2 * max rs.length ds.length + 5
           evals_in_steps := ?_
           steps_le_m := ?_ }
  · change run _ (initList machine _) = some (haltList machine _)
    rw [initList_eq, haltList_eq]
    simpa [pairEncoding, sequenceEncoding, directionEncoding, wordEncoding] using program_run rs ds
  · simp only [pairEncoding, sequenceEncoding, directionEncoding, wordEncoding, id_eq,
      List.length_append, List.length_map, List.length_cons]
    omega

noncomputable def zipComputable : TM2ComputableInPolyTime
    (pairEncoding sequenceEncoding directionEncoding) (wordEncoding Letter)
    (fun x => zipRecords 0 x.1 x.2) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 4 * Polynomial.X + Polynomial.C 5
  outputsFun x := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime machine (List.map id _) (some (List.map id _)) _
    simpa only [List.map_id] using machine_outputs x.1 x.2

end ProteinFolding.Tetrahedral.CertificatesTM2Zip
