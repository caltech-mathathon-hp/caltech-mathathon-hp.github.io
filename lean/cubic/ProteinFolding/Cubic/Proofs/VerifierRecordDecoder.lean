import ProteinFolding.Cubic.Proofs.VerifierRecords
import ProteinFolding.Common.TM2Transfer

/-! A finite-state four-bit record decoder. Every complete block emits either
a record or an explicit failure token; an incomplete final block also emits a
failure token. Thus malformed words cannot disappear through filtering. -/

namespace ProteinFolding.CubicRecordDecoder

open Computability Turing TM2 CubicVerifier CubicCertificates

def decodeBlock (label a b c : Bool) : Option Record :=
  if h : bitsValue a b c < 6 then
    some ((if label then Residue.H else Residue.P), ⟨bitsValue a b c, h⟩)
  else none

def stream : List Bool → List (Option Record)
  | [] => []
  | label :: a :: b :: c :: rest => decodeBlock label a b c :: stream rest
  | _ => [none]

theorem stream_cons_record (r : Record) (w : List Bool) :
    stream (encodeRecord r ++ w) = some r :: stream w := by
  obtain ⟨r, d⟩ := r
  cases r <;> match d with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl

theorem stream_encodeRecords (rs : List Record) :
    stream (encodeRecords rs) = rs.map some := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simpa only [encodeRecords, List.flatMap_cons, stream_cons_record, List.map_cons] using
      congrArg (some r :: ·) ih

theorem stream_length_le (w : List Bool) : (stream w).length ≤ w.length := by
  cases w with
  | nil => simp [stream]
  | cons a w =>
    cases w with
    | nil => simp [stream]
    | cons b w =>
      cases w with
      | nil => simp [stream]
      | cons c w =>
        cases w with
        | nil => simp [stream]
        | cons d rest =>
          have ih := stream_length_le rest
          simp only [stream, List.length_cons]
          omega
termination_by w.length

inductive Partial where
  | empty
  | one : Bool → Partial
  | two : Bool → Bool → Partial
  | three : Bool → Bool → Bool → Partial
  deriving DecidableEq, Fintype

def advance : Partial → Bool → Partial
  | .empty, a => .one a
  | .one a, b => .two a b
  | .two a b, c => .three a b c
  | .three _ _ _, _ => .empty

def emit : Partial → Bool → Option (Option Record)
  | .three a b c, d => some (decodeBlock a b c d)
  | _, _ => none

inductive Stack where
  | input | buffer | output
  deriving DecidableEq, Fintype

inductive Label where
  | scan | drain | finish
  deriving DecidableEq, Fintype

def Alphabet : Stack → Type
  | .input => Bool
  | .buffer | .output => Option Record

abbrev State := (Partial × Option Bool) × Option (Option Record)

def initialState : State := ((.empty, none), none)

def dataStacks (w : List Bool) (b o : List (Option Record)) : ∀ k, List (Alphabet k)
  | .input => w
  | .buffer => b
  | .output => o

theorem update_input (w w' : List Bool) (b o : List (Option Record)) :
    Function.update (dataStacks w b o) .input w' = dataStacks w' b o := by
  funext k; cases k <;> simp [dataStacks, Function.update_of_ne]

theorem update_buffer (w : List Bool) (b b' o : List (Option Record)) :
    Function.update (dataStacks w b o) .buffer b' = dataStacks w b' o := by
  funext k; cases k <;> simp [dataStacks, Function.update_of_ne]

def program : Label → Stmt Alphabet Label State
  | .scan => .pop .input (fun st x => ((st.1.1, x), st.2))
      (.branch (fun st => st.1.2.isSome)
        (.branch (fun st => (emit st.1.1 (st.1.2.getD false)).isSome)
          (.push .buffer (fun st => (emit st.1.1 (st.1.2.getD false)).getD none)
            (.load (fun st => ((advance st.1.1 (st.1.2.getD false), none), none))
              (.goto (fun _ => .scan))))
          (.load (fun st => ((advance st.1.1 (st.1.2.getD false), none), none))
            (.goto (fun _ => .scan))))
        (.branch (fun st => decide (st.1.1 = .empty))
          (.load (fun _ => initialState) (.goto (fun _ => .drain)))
          (.push .buffer (fun _ => none)
            (.load (fun _ => initialState) (.goto (fun _ => .drain))))))
  | .drain =>
      letI : Inhabited (Alphabet .buffer) := ⟨none⟩
      TM2Transfer.transferStmt (Γ := Alphabet) (σ := Partial × Option Bool)
        .buffer .output id .drain .finish
  | .finish => .halt

def cfg (label : Label) (p : Partial) (w : List Bool) (b o : List (Option Record)) :
    Cfg Alphabet Label State := ⟨some label, ((p, none), none), dataStacks w b o⟩

def run (n : ℕ) (c : Cfg Alphabet Label State) : Option (Cfg Alphabet Label State) :=
  (fun x : Option (Cfg Alphabet Label State) => x.bind (TM2.step program))^[n] (some c)

theorem run_step {c d : Cfg Alphabet Label State} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  unfold run
  rw [Function.iterate_succ_apply, Option.bind_some, h]

theorem run_add {c d : Cfg Alphabet Label State} {n : ℕ}
    (h : run n c = some d) (m : ℕ) : run (n + m) c = run m d := by
  unfold run at *
  rw [Nat.add_comm n m, Function.iterate_add_apply, h]

theorem step_empty_bit (a : Bool) (w : List Bool) (b o : List (Option Record)) :
    TM2.step program (cfg .scan .empty (a :: w) b o) = some (cfg .scan (.one a) w b o) := by
  simp [cfg, program, TM2.step, stepAux, dataStacks, update_input, emit, advance]

theorem step_one_bit (a c : Bool) (w : List Bool) (b o : List (Option Record)) :
    TM2.step program (cfg .scan (.one a) (c :: w) b o) = some (cfg .scan (.two a c) w b o) := by
  simp [cfg, program, TM2.step, stepAux, dataStacks, update_input, emit, advance]

theorem step_two_bit (a c d : Bool) (w : List Bool) (b o : List (Option Record)) :
    TM2.step program (cfg .scan (.two a c) (d :: w) b o) = some (cfg .scan (.three a c d) w b o) := by
  simp [cfg, program, TM2.step, stepAux, dataStacks, update_input, emit, advance]

theorem step_three_bit (a c d e : Bool) (w : List Bool) (b o : List (Option Record)) :
    TM2.step program (cfg .scan (.three a c d) (e :: w) b o) =
      some (cfg .scan .empty w (decodeBlock a c d e :: b) o) := by
  simp [cfg, program, TM2.step, stepAux, dataStacks, update_input, update_buffer, emit, advance]

theorem step_nil_empty (b o : List (Option Record)) :
    TM2.step program (cfg .scan .empty [] b o) = some (cfg .drain .empty [] b o) := by
  simp [cfg, program, TM2.step, stepAux, dataStacks, update_input, initialState]

theorem step_nil_partial (p : Partial) (hp : p ≠ .empty) (b o : List (Option Record)) :
    TM2.step program (cfg .scan p [] b o) = some (cfg .drain .empty [] (none :: b) o) := by
  simp [cfg, program, TM2.step, stepAux, dataStacks, update_input, update_buffer, hp, initialState]

theorem run_one {c d : Cfg Alphabet Label State} (h : TM2.step program c = some d) :
    run 1 c = some d := by
  simpa only [run, Function.iterate_one, Option.bind_some] using h

theorem block_run (a b c d : Bool) (w : List Bool) (buf o : List (Option Record)) :
    run 4 (cfg .scan .empty (a :: b :: c :: d :: w) buf o) =
      some (cfg .scan .empty w (decodeBlock a b c d :: buf) o) := by
  rw [show 4 = 3 + 1 by decide, run_step (step_empty_bit a (b :: c :: d :: w) buf o),
    show 3 = 2 + 1 by decide, run_step (step_one_bit a b (c :: d :: w) buf o),
    show 2 = 1 + 1 by decide, run_step (step_two_bit a b c (d :: w) buf o)]
  exact run_one (step_three_bit a b c d w buf o)

/-- Every bit is consumed. Final incomplete blocks emit a failure token rather
than being silently discarded. The partial state and registers are reset. -/
theorem scan_run (w : List Bool) (buf o : List (Option Record)) :
    run (w.length + 1) (cfg .scan .empty w buf o) =
      some (cfg .drain .empty [] ((stream w).reverse ++ buf) o) := by
  cases w with
  | nil => simpa [stream] using run_one (step_nil_empty buf o)
  | cons a w =>
    cases w with
    | nil =>
      rw [show [a].length + 1 = 1 + 1 by rfl, run_step (step_empty_bit a [] buf o)]
      simpa [stream] using run_one (step_nil_partial (.one a) (by intro h; cases h) buf o)
    | cons b w =>
      cases w with
      | nil =>
        rw [show [a, b].length + 1 = 2 + 1 by rfl,
          run_step (step_empty_bit a [b] buf o), show 2 = 1 + 1 by decide,
          run_step (step_one_bit a b [] buf o)]
        simpa [stream] using run_one (step_nil_partial (.two a b) (by intro h; cases h) buf o)
      | cons c w =>
        cases w with
        | nil =>
          rw [show [a, b, c].length + 1 = 3 + 1 by rfl,
            run_step (step_empty_bit a [b, c] buf o), show 3 = 2 + 1 by decide,
            run_step (step_one_bit a b [c] buf o), show 2 = 1 + 1 by decide,
            run_step (step_two_bit a b c [] buf o)]
          simpa [stream] using run_one (step_nil_partial (.three a b c) (by intro h; cases h) buf o)
        | cons d rest =>
          have ih := scan_run rest (decodeBlock a b c d :: buf) o
          rw [show (a :: b :: c :: d :: rest).length + 1 = 4 + (rest.length + 1) by simp; omega,
            run_add (block_run a b c d rest buf o)]
          simpa [stream, List.reverse_cons, List.append_assoc] using ih
termination_by w.length

theorem transferCfg_eq (label : Label) (w : List Bool) (buf o : List (Option Record)) :
    TM2Transfer.transferCfg (Γ := Alphabet) (Λ := Label) .buffer .output
      label (.empty, none) none (dataStacks w [] []) buf o = cfg label .empty w buf o := by
  unfold TM2Transfer.transferCfg cfg
  congr 1
  funext k
  cases k <;> simp [TM2Transfer.setStacks, dataStacks, Function.update_of_ne]

theorem drain_run (w : List Bool) (buf o : List (Option Record)) :
    run (buf.length + 1) (cfg .drain .empty w buf o) =
      some (cfg .finish .empty w [] (buf.reverse ++ o)) := by
  letI : Inhabited (Alphabet .buffer) := ⟨none⟩
  have h := TM2Transfer.transfer_run (Γ := Alphabet) (Λ := Label) (σ := Partial × Option Bool)
    .buffer .output (by decide) id .drain .finish program rfl
    (.empty, none) none (dataStacks w [] []) buf o
  simp only [List.map_id, transferCfg_eq] at h
  exact h

theorem program_run (w : List Bool) :
    run (w.length + (stream w).length + 3) (cfg .scan .empty w [] []) =
      some (Cfg.mk none initialState (dataStacks [] [] (stream w))) := by
  have hs := scan_run w [] []
  simp only [List.append_nil] at hs
  have hd := drain_run [] (stream w).reverse []
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hd
  rw [show w.length + (stream w).length + 3 =
      (w.length + 1) + (((stream w).length + 1) + 1) by omega,
    run_add hs, run_add hd]
  rfl

def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := initialState
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program

def machine_outputs (w : List Bool) :
    TM2OutputsInTime machine w (some (stream w)) (2 * w.length + 3) := by
  have hi : initList machine w = cfg .scan .empty w [] [] := by
    apply congrArg (fun S : ∀ k, List (Alphabet k) =>
      (Cfg.mk (Γ := Alphabet) (Λ := Label) (σ := State) (some .scan) initialState S))
    funext k
    cases k <;> rfl
  have ho : haltList machine (stream w) = Cfg.mk none initialState (dataStacks [] [] (stream w)) := by
    apply congrArg (Cfg.mk (Γ := Alphabet) (Λ := Label) (σ := State) none initialState)
    funext k
    cases k <;> rfl
  refine { steps := w.length + (stream w).length + 3, evals_in_steps := ?_, steps_le_m := ?_ }
  · change run (w.length + (stream w).length + 3) (initList machine w) = some (haltList machine (stream w))
    rw [hi, ho]
    exact program_run w
  · have h := stream_length_le w
    omega

noncomputable def decoderComputable :
    TM2ComputableInPolyTime (wordEncoding Bool) (wordEncoding (Option Record)) stream where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl (Option Record)
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun w := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime machine (List.map id w) (some (List.map id (stream w))) (2 * w.length + 3)
    simpa only [List.map_id] using machine_outputs w

theorem decoderComputable_time :
    decoderComputable.time = Polynomial.C 2 * Polynomial.X + Polynomial.C 3 := rfl

end ProteinFolding.CubicRecordDecoder
