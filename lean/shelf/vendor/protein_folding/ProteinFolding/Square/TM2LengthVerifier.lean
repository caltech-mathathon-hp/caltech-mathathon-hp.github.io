import ProteinFolding.Square.Certificates

/-!
A genuine finite-alphabet TM2 for the length-checking stage of the direction
verifier. Input symbols are consumed from the actual nested pair encoding.
The unary counter records residues, and one counter symbol is removed per
direction. The counter is cleared before halting. This stage does not check
self-avoidance or losses, and does not establish `LossVerifierPolyTime`.
-/

namespace ProteinFolding.Square

open Computability Turing

abbrev DirectionInputAlphabet := (pairEncoding lossEncoding directionEncoding).Γ

inductive LengthStack where
  | input | counter | output
  deriving DecidableEq, Fintype

def lengthAlphabet : LengthStack → Type
  | .input => DirectionInputAlphabet
  | .counter => Unit
  | .output => Bool

instance lengthAlphabetFintype (k : LengthStack) : Fintype (lengthAlphabet k) := by
  cases k <;> dsimp [lengthAlphabet] <;> infer_instance

inductive LengthLabel where
  | scan | compare | drain
  deriving DecidableEq, Fintype

abbrev LengthState := Option DirectionInputAlphabet × Bool

def lengthInitialState : LengthState := (none, true)

def lengthProgram : LengthLabel → TM2.Stmt lengthAlphabet LengthLabel LengthState
  | .scan =>
    .pop .input (fun s a => (a, s.2))
      (.branch (fun s => match s.1 with | some (.left (.left _)) => true | _ => false)
        (.push .counter (fun _ => ())
          (.load (fun s => (none, s.2)) (.goto (fun _ => .scan))))
        (.branch (fun s => match s.1 with | some .sep => true | _ => false)
          (.load (fun s => (none, s.2)) (.goto (fun _ => .compare)))
          (.branch (fun s => s.1.isSome)
            (.load (fun s => (none, s.2)) (.goto (fun _ => .scan)))
            (.load (fun _ => (none, false)) (.goto (fun _ => .drain))))))
  | .compare =>
    .pop .input (fun s a => (a, s.2))
      (.branch (fun s => s.1.isSome)
        (.pop .counter (fun s a => (none, s.2 && a.isSome)) (.goto (fun _ => .compare)))
        (.peek .counter (fun s a => (none, s.2 && a.isNone)) (.goto (fun _ => .drain))))
  | .drain =>
    .pop .counter (fun s a => (if a.isSome then some .sep else none, s.2))
      (.branch (fun s => s.1.isSome)
        (.load (fun s => (none, s.2)) (.goto (fun _ => .drain)))
        (.push .output Prod.snd (.load (fun _ => lengthInitialState) .halt)))

def lengthMachine : FinTM2 where
  K := LengthStack
  k₀ := .input
  k₁ := .output
  Γ := lengthAlphabet
  Λ := LengthLabel
  main := .scan
  σ := LengthState
  initialState := lengthInitialState
  Γk₀Fin := inferInstanceAs (Fintype DirectionInputAlphabet)
  m := lengthProgram

def lengthStacks (w : List DirectionInputAlphabet) (c : List Unit) (o : List Bool) :
    (k : LengthStack) → List (lengthAlphabet k)
  | .input => w
  | .counter => c
  | .output => o

def lengthConfig (l : LengthLabel) (w : List DirectionInputAlphabet) (n : ℕ) (b : Bool) :
    lengthMachine.Cfg :=
  ⟨some l, (none, b), lengthStacks w (List.replicate n ()) []⟩

theorem lengthStacks_update_input (w w' : List DirectionInputAlphabet) (c : List Unit) (o : List Bool) :
    Function.update (lengthStacks w c o) .input w' = lengthStacks w' c o := by
  funext k
  cases k <;> simp [lengthStacks]

theorem lengthStacks_update_counter (w : List DirectionInputAlphabet) (c c' : List Unit) (o : List Bool) :
    Function.update (lengthStacks w c o) .counter c' = lengthStacks w c' o := by
  funext k
  cases k <;> simp [lengthStacks]

theorem lengthStacks_update_output (w : List DirectionInputAlphabet) (c : List Unit) (o o' : List Bool) :
    Function.update (lengthStacks w c o) .output o' = lengthStacks w c o' := by
  funext k
  cases k <;> simp [lengthStacks]

def lengthRun (t : ℕ) (c : lengthMachine.Cfg) : Option lengthMachine.Cfg :=
  (fun q : Option lengthMachine.Cfg => q.bind lengthMachine.step)^[t] (some c)

theorem lengthRun_zero (c : lengthMachine.Cfg) : lengthRun 0 c = some c := rfl

theorem lengthRun_step {c c' : lengthMachine.Cfg} (h : lengthMachine.step c = some c') (t : ℕ) :
    lengthRun (t + 1) c = lengthRun t c' := by
  unfold lengthRun
  rw [Function.iterate_succ_apply, Option.bind_some, h]

theorem lengthRun_add {c c' : lengthMachine.Cfg} {t : ℕ}
    (h : lengthRun t c = some c') (u : ℕ) : lengthRun (t + u) c = lengthRun u c' := by
  unfold lengthRun at *
  rw [Nat.add_comm t u, Function.iterate_add_apply, h]

theorem length_step_residue (r : Residue) (w : List DirectionInputAlphabet) (n : ℕ) :
    lengthMachine.step (lengthConfig .scan (.left (.left r) :: w) n true) =
      some (lengthConfig .scan w (n + 1) true) := by
  simp [lengthMachine, FinTM2.step, TM2.step, lengthProgram, lengthConfig,
    TM2.stepAux, lengthStacks, lengthStacks_update_input, lengthStacks_update_counter,
    List.replicate_succ]

theorem length_step_skip (x : lossEncoding.Γ) (hx : ∀ r, x ≠ .left r)
    (w : List DirectionInputAlphabet) (n : ℕ) :
    lengthMachine.step (lengthConfig .scan (.left x :: w) n true) =
      some (lengthConfig .scan w n true) := by
  cases x with
  | left r => exact False.elim (hx r rfl)
  | sep | right b =>
    simp [lengthMachine, FinTM2.step, TM2.step, lengthProgram, lengthConfig,
      TM2.stepAux, lengthStacks, lengthStacks_update_input]

theorem length_step_separator (w : List DirectionInputAlphabet) (n : ℕ) :
    lengthMachine.step (lengthConfig .scan (.sep :: w) n true) =
      some (lengthConfig .compare w n true) := by
  simp [lengthMachine, FinTM2.step, TM2.step, lengthProgram, lengthConfig,
    TM2.stepAux, lengthStacks, lengthStacks_update_input]

theorem length_step_direction_zero (x : DirectionInputAlphabet) (w : List DirectionInputAlphabet) (b : Bool) :
    lengthMachine.step (lengthConfig .compare (x :: w) 0 b) =
      some (lengthConfig .compare w 0 false) := by
  simp [lengthMachine, FinTM2.step, TM2.step, lengthProgram, lengthConfig,
    TM2.stepAux, lengthStacks, lengthStacks_update_input, lengthStacks_update_counter]

theorem length_step_direction_succ (x : DirectionInputAlphabet) (w : List DirectionInputAlphabet)
    (n : ℕ) (b : Bool) :
    lengthMachine.step (lengthConfig .compare (x :: w) (n + 1) b) =
      some (lengthConfig .compare w n b) := by
  simp [lengthMachine, FinTM2.step, TM2.step, lengthProgram, lengthConfig,
    TM2.stepAux, lengthStacks, lengthStacks_update_input, lengthStacks_update_counter,
    List.replicate_succ]

theorem length_step_end (n : ℕ) (b : Bool) :
    lengthMachine.step (lengthConfig .compare [] n b) =
      some (lengthConfig .drain [] n (b && decide (n = 0))) := by
  cases n <;>
    simp [lengthMachine, FinTM2.step, TM2.step, lengthProgram, lengthConfig,
      TM2.stepAux, lengthStacks, lengthStacks_update_input, List.replicate_succ]

theorem length_step_drain (n : ℕ) (b : Bool) :
    lengthMachine.step (lengthConfig .drain [] (n + 1) b) =
      some (lengthConfig .drain [] n b) := by
  simp [lengthMachine, FinTM2.step, TM2.step, lengthProgram, lengthConfig,
    TM2.stepAux, lengthStacks, lengthStacks_update_counter, List.replicate_succ]

theorem length_step_halt (b : Bool) :
    lengthMachine.step (lengthConfig .drain [] 0 b) = some (haltList lengthMachine [b]) := by
  simp [lengthMachine, FinTM2.step, TM2.step, lengthProgram, lengthConfig,
    TM2.stepAux, lengthStacks, lengthStacks_update_counter, lengthStacks_update_output,
    lengthInitialState, haltList]
  funext k
  cases k <;> rfl

theorem length_drain_run (n : ℕ) (b : Bool) :
    lengthRun (n + 1) (lengthConfig .drain [] n b) = some (haltList lengthMachine [b]) := by
  induction n with
  | zero => rw [lengthRun_step (length_step_halt b), lengthRun_zero]
  | succ n ih => rw [lengthRun_step (length_step_drain n b), ih]

theorem length_compare_run (w : List DirectionInputAlphabet) (n : ℕ) (b : Bool) :
    lengthRun (w.length + 2 + (n - w.length)) (lengthConfig .compare w n b) =
      some (haltList lengthMachine [b && decide (w.length = n)]) := by
  induction w generalizing n b with
  | nil =>
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, eq_comm] using
      (lengthRun_step (length_step_end n b) (n + 1)).trans
        (length_drain_run n (b && decide (n = 0)))
  | cons x w ih =>
    cases n with
    | zero =>
      simp only [List.length_cons, Nat.zero_sub, Nat.add_zero]
      rw [show w.length + 1 + 2 = (w.length + 2) + 1 by omega,
        lengthRun_step (length_step_direction_zero x w b)]
      simpa using ih 0 false
    | succ n =>
      have ht : (x :: w).length + 2 + (n + 1 - (x :: w).length) =
          (w.length + 2 + (n - w.length)) + 1 := by simp; omega
      rw [ht, lengthRun_step (length_step_direction_succ x w n b), ih]
      simp

theorem length_scan_residues (S : Sequence) (w : List DirectionInputAlphabet) (n : ℕ) :
    lengthRun S.length
      (lengthConfig .scan (S.map (fun r => .left (.left r)) ++ w) n true) =
      some (lengthConfig .scan w (n + S.length) true) := by
  induction S generalizing n with
  | nil => simp [lengthRun_zero]
  | cons r S ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [lengthRun_step (length_step_residue r _ n)]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (n + 1)

theorem length_scan_bits (bs : List Bool) (w : List DirectionInputAlphabet) (n : ℕ) :
    lengthRun bs.length
      (lengthConfig .scan (bs.map (fun b => .left (.right b)) ++ w) n true) =
      some (lengthConfig .scan w n true) := by
  induction bs with
  | nil => exact lengthRun_zero _
  | cons b bs ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [lengthRun_step (length_step_skip (.right b) (by intro r; simp) _ n), ih]

theorem directionInput_encode (I : LossInstance) (ds : DirectionWord) :
    (pairEncoding lossEncoding directionEncoding).encode (I, ds) =
      I.sequence.map (fun r => .left (.left r)) ++ .left .sep ::
        ((encodeSigned I.maxLosses).map (fun b => .left (.right b)) ++ .sep :: ds.map .right) := by
  simp [pairEncoding, lossEncoding, directionEncoding, sequenceEncoding, signedEncoding,
    wordEncoding, List.map_append, List.map_map, List.append_assoc, Function.comp_def]

theorem length_init (w : List DirectionInputAlphabet) :
    initList lengthMachine w = lengthConfig .scan w 0 true := by
  simp [initList, lengthMachine, lengthConfig, lengthInitialState]
  congr 1
  funext k
  cases k <;> rfl

theorem length_canonical_run (I : LossInstance) (ds : DirectionWord) :
    lengthRun (I.sequence.length + 1 + (encodeSigned I.maxLosses).length + 1 +
      (ds.length + 2 + (I.sequence.length - ds.length)))
      (initList lengthMachine ((pairEncoding lossEncoding directionEncoding).encode (I, ds))) =
      some (haltList lengthMachine [decide (ds.length = I.sequence.length)]) := by
  rw [length_init, directionInput_encode]
  rw [show I.sequence.length + 1 + (encodeSigned I.maxLosses).length + 1 +
      (ds.length + 2 + (I.sequence.length - ds.length)) = I.sequence.length +
        (1 + ((encodeSigned I.maxLosses).length + (1 +
          (ds.length + 2 + (I.sequence.length - ds.length))))) by omega]
  rw [lengthRun_add (length_scan_residues I.sequence _ 0)]
  simp only [Nat.zero_add]
  rw [Nat.add_comm 1, lengthRun_step (length_step_skip .sep (by intro r; simp) _ _)]
  rw [lengthRun_add (length_scan_bits _ _ _)]
  rw [Nat.add_comm 1, lengthRun_step (length_step_separator _ _)]
  simpa using length_compare_run (ds.map PairSymbol.right) I.sequence.length true

def certificateLengthVerifier (input : LossInstance × DirectionWord) : Bool :=
  decide (input.2.length = input.1.sequence.length)

theorem certificateLengthVerifier_spec (input : LossInstance × DirectionWord) :
    certificateLengthVerifier input = true ↔ input.2.length = input.1.sequence.length := by
  simp [certificateLengthVerifier]

theorem directionAccepts_length (input : LossInstance × DirectionWord)
    (h : DirectionAccepts input) : input.2.length = input.1.sequence.length := by
  by_contra hn
  have hv : ¬ ValidDirectionWord input.1.sequence input.2 := fun hv => hn hv.1
  simp [DirectionAccepts, certificateFold, hv] at h

theorem directionVerifier_false_of_length_mismatch (input : LossInstance × DirectionWord)
    (h : input.2.length ≠ input.1.sequence.length) : directionVerifier input = false := by
  cases hb : directionVerifier input with
  | false => rfl
  | true => exact False.elim (h (directionAccepts_length input ((directionVerifier_spec input).mp hb)))

/-- The guard is semantically a necessary first stage of the complete verifier. -/
theorem directionVerifier_length_guard (input : LossInstance × DirectionWord) :
    (certificateLengthVerifier input && directionVerifier input) = directionVerifier input := by
  by_cases h : input.2.length = input.1.sequence.length
  · rw [(certificateLengthVerifier_spec input).mpr h]
    rfl
  · rw [directionVerifier_false_of_length_mismatch input h]
    simp

/-- The machine itself is executable. Only its polynomial-valued proof bundle
is marked noncomputable, as required by mathlib's polynomial representation. -/
noncomputable def certificateLengthComputable :
    TM2ComputableInPolyTime (pairEncoding lossEncoding directionEncoding)
      finEncodingBoolBool certificateLengthVerifier where
  tm := lengthMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun input :=
    { steps := input.1.sequence.length + 1 + (encodeSigned input.1.maxLosses).length + 1 +
        (input.2.length + 2 + (input.1.sequence.length - input.2.length))
      evals_in_steps := by
        change lengthRun _
          (initList lengthMachine (List.map id ((pairEncoding lossEncoding directionEncoding).encode input))) =
          some (haltList lengthMachine [certificateLengthVerifier input])
        rw [List.map_id]
        exact length_canonical_run input.1 input.2
      steps_le_m := by
        simp [pairEncoding, lossEncoding, directionEncoding, sequenceEncoding,
          wordEncoding, signedEncoding]
        omega }

theorem certificateLength_polyTimeDecidable :
    PolyTimeDecidable (pairEncoding lossEncoding directionEncoding)
      (fun input : LossInstance × DirectionWord => input.2.length = input.1.sequence.length) :=
  ⟨certificateLengthVerifier, ⟨certificateLengthComputable⟩, certificateLengthVerifier_spec⟩

end ProteinFolding.Square
