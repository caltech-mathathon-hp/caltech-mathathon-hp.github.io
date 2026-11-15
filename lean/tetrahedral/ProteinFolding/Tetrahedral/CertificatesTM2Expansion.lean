import ProteinFolding.Tetrahedral.CertificatesTM2Directions

/-!
# An actual linear-time finite TM2 expanding tetrahedral directions

The control stores only the A/B parity and two finite symbol caches. Each
input direction emits exactly three signed unit moves, then toggles parity.
A final transfer restores the output order and empties the buffer.
-/

namespace ProteinFolding.Tetrahedral.CertificatesTM2Expansion

open Computability Turing TM2
open CertificatesTM2Directions

def expandFrom : Bool → List (Fin 4) → List (Fin 6)
  | _, [] => []
  | a, d :: ds => unitDirections a d ++ expandFrom (!a) ds

def endColour : Bool → List (Fin 4) → Bool
  | a, [] => a
  | a, _ :: ds => endColour (!a) ds

theorem expandFrom_length (a : Bool) (ds : List (Fin 4)) :
    (expandFrom a ds).length = 3 * ds.length := by
  induction ds generalizing a with
  | nil => rfl
  | cons d ds ih =>
    simp [expandFrom, List.length_append, unitDirections_length, ih, Nat.mul_succ]
    omega

theorem unitDirections_triple (a : Bool) (d : Fin 4) : unitDirections a d =
    [(unitDirections a d)[0]?.getD 0, (unitDirections a d)[1]?.getD 0,
      (unitDirections a d)[2]?.getD 0] := by revert a d; decide

inductive Slot where
  | input | buffer | output
  deriving DecidableEq, Fintype

inductive Phase where
  | scan | restore | finish
  deriving DecidableEq, Fintype

def Alphabet : Slot → Type
  | .input => Fin 4
  | .buffer => Fin 6
  | .output => Fin 6

abbrev Reg := (Bool × Option (Fin 4)) × Option (Fin 6)

def contents (u : List (Fin 4)) (v w : List (Fin 6)) : ∀ k, List (Alphabet k)
  | .input => u
  | .buffer => v
  | .output => w

def cfg (phase : Phase) (reg : Reg) (u : List (Fin 4)) (v w : List (Fin 6)) :
    Cfg Alphabet Phase Reg := ⟨some phase, reg, contents u v w⟩

theorem update_input (u u' : List (Fin 4)) (v w : List (Fin 6)) :
    Function.update (contents u v w) .input u' = contents u' v w := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_buffer (u : List (Fin 4)) (v v' w : List (Fin 6)) :
    Function.update (contents u v w) .buffer v' = contents u v' w := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

def token (reg : Reg) (i : ℕ) : Fin 6 :=
  (unitDirections reg.1.1 (reg.1.2.getD 0))[i]?.getD 0

def scanBody : Stmt Alphabet Phase Reg :=
  .push .buffer (fun st => token st 0)
    (.push .buffer (fun st => token st 1)
      (.push .buffer (fun st => token st 2)
        (.load (fun st => ((!st.1.1, none), none)) (.goto (fun _ => .scan)))))

def program : Phase → Stmt Alphabet Phase Reg
  | .scan => .pop .input (fun st d => ((st.1.1, d), st.2))
      (.branch (fun st => st.1.2.isSome) scanBody
        (.load (fun st => ((st.1.1, none), none)) (.goto (fun _ => .restore))))
  | .restore =>
      letI : Inhabited (Alphabet .buffer) := inferInstanceAs (Inhabited (Fin 6))
      TM2Transfer.transferStmt (Γ := Alphabet) (Λ := Phase) (σ := Bool × Option (Fin 4))
        .buffer .output id .restore .finish
  | .finish => .load (fun _ => ((true, none), none)) .halt

theorem scan_step_cons (a : Bool) (cache : Option (Fin 4)) (outCache : Option (Fin 6))
    (d : Fin 4) (u : List (Fin 4)) (v w : List (Fin 6)) :
    Turing.TM2.step program (cfg .scan ((a, cache), outCache) (d :: u) v w) =
      some (cfg .scan ((!a, none), none) u ((unitDirections a d).reverse ++ v) w) := by
  have htriple := unitDirections_triple a d
  conv_rhs => rw [htriple]
  simp [program, cfg, Turing.TM2.step, stepAux, scanBody, token, contents,
    update_input, update_buffer]

theorem scan_step_nil (a : Bool) (cache : Option (Fin 4)) (outCache : Option (Fin 6))
    (v w : List (Fin 6)) :
    Turing.TM2.step program (cfg .scan ((a, cache), outCache) [] v w) =
      some (cfg .restore ((a, none), none) [] v w) := by
  simp [program, cfg, Turing.TM2.step, stepAux, contents, update_input]

theorem scan_run (a : Bool) (cache : Option (Fin 4)) (outCache : Option (Fin 6))
    (u : List (Fin 4)) (v w : List (Fin 6)) :
    (fun x : Option (Cfg Alphabet Phase Reg) => x.bind (Turing.TM2.step program))^[u.length + 1]
      (some (cfg .scan ((a, cache), outCache) u v w)) =
        some (cfg .restore ((endColour a u, none), none) []
          ((expandFrom a u).reverse ++ v) w) := by
  induction u generalizing a cache outCache v with
  | nil => simpa [expandFrom, endColour] using scan_step_nil a cache outCache v w
  | cons d u ih =>
    rw [List.length_cons, Nat.add_right_comm u.length 1 1, Function.iterate_succ_apply]
    simp only [Option.bind_some, scan_step_cons]
    simpa only [expandFrom, endColour, List.reverse_append, List.append_assoc] using
      ih (!a) none none ((unitDirections a d).reverse ++ v)

theorem transferCfg_eq (phase : Phase) (reg : Reg) (u : List (Fin 4)) (v w : List (Fin 6)) :
    TM2Transfer.transferCfg (Γ := Alphabet) (Λ := Phase) (σ := Bool × Option (Fin 4))
      .buffer .output phase reg.1 reg.2 (contents u [] []) v w =
      cfg phase reg u v w := by
  apply congrArg (fun S => (⟨some phase, reg, S⟩ : Cfg Alphabet Phase Reg))
  funext k
  cases k <;> simp [TM2Transfer.setStacks, contents]

theorem restore_run (reg : Reg) (u : List (Fin 4)) (v w : List (Fin 6)) :
    (fun x : Option (Cfg Alphabet Phase Reg) => x.bind (Turing.TM2.step program))^[v.length + 1]
      (some (cfg .restore reg u v w)) =
        some (cfg .finish (reg.1, none) u [] (v.reverse ++ w)) := by
  letI : Inhabited (Alphabet .buffer) := inferInstanceAs (Inhabited (Fin 6))
  have h := TM2Transfer.transfer_run (Γ := Alphabet) (Λ := Phase) (σ := Bool × Option (Fin 4))
    .buffer .output (by decide) id .restore .finish program rfl
    reg.1 reg.2 (contents u [] []) v w
  simp only [List.map_id, transferCfg_eq] at h
  exact h.trans (congrArg some (transferCfg_eq .finish (reg.1, none) u [] (v.reverse ++ w)))

theorem program_run (u : List (Fin 4)) :
    (fun x : Option (Cfg Alphabet Phase Reg) => x.bind (Turing.TM2.step program))^[4 * u.length + 3]
      (some (cfg .scan ((true, none), none) u [] [])) =
        some ⟨none, ((true, none), none), contents [] [] (expandFrom true u)⟩ := by
  have hscan := scan_run true none none u [] []
  simp only [List.append_nil] at hscan
  rw [show 4 * u.length + 3 = ((expandFrom true u).reverse.length + 1 + 1) + (u.length + 1) by
    rw [List.length_reverse, expandFrom_length]; omega, Function.iterate_add_apply, hscan]
  rw [Function.iterate_succ_apply', restore_run]
  simp [cfg, program, Turing.TM2.step, stepAux]

def machine : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Phase
  main := .scan
  σ := Reg
  initialState := ((true, none), none)
  Γk₀Fin := inferInstanceAs (Fintype (Fin 4))
  m := program

def machine_outputs (u : List (Fin 4)) :
    TM2OutputsInTime machine u (some (expandFrom true u)) (4 * u.length + 3) := by
  have hi : initList machine u = cfg .scan ((true, none), none) u [] [] := by
    apply congrArg (fun S => (⟨some .scan, ((true, none), none), S⟩ : Cfg Alphabet Phase Reg))
    funext k; cases k <;> rfl
  have ho : haltList machine (expandFrom true u) =
      (⟨none, ((true, none), none), contents [] [] (expandFrom true u)⟩ : Cfg Alphabet Phase Reg) := by
    apply congrArg (fun S => (⟨none, ((true, none), none), S⟩ : Cfg Alphabet Phase Reg))
    funext k; cases k <;> rfl
  refine ⟨⟨4 * u.length + 3, ?_⟩, le_rfl⟩
  change (fun x : Option (Cfg Alphabet Phase Reg) => x.bind (Turing.TM2.step program))^[_]
    (some (initList machine u)) = some (haltList machine (expandFrom true u))
  rw [hi, ho]
  exact program_run u

noncomputable def expansionComputable :
    TM2ComputableInPolyTime (wordEncoding (Fin 4)) (wordEncoding (Fin 6)) (expandFrom true) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 4 * Polynomial.X + Polynomial.C 3
  outputsFun u := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime machine (List.map id u) (some (List.map id (expandFrom true u))) _
    simpa only [List.map_id] using machine_outputs u

end ProteinFolding.Tetrahedral.CertificatesTM2Expansion
