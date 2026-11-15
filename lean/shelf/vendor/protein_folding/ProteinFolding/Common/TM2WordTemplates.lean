import ProteinFolding.Common.TM2Constants
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Substitution of two input words into an input Boolean word by an actual
finite TM2. Templates and control bits are reversed while parsing; each control
bit copies its selected template to output and a restoration buffer. Processing
the reversed control word produces the original concatenation order. -/

namespace ProteinFolding.TM2WordTemplates

open Computability Turing TM2

variable {A : Type}

abbrev Sym (A : Type) := PairSymbol (PairSymbol A A) Bool
abbrev State (A : Type) := (Option (Sym A) × Option Bool) × Option A

inductive Slot where
  | input | template : Bool → Slot
  | controls | buffer | output
  deriving DecidableEq, Fintype

inductive Phase where
  | scan | outer | inner : Bool → Phase
  | restore : Bool → Phase
  | clear : Bool → Phase
  | finish
  deriving DecidableEq, Fintype

def Alphabet (A : Type) : Slot → Type
  | .input => Sym A
  | .controls => Bool
  | _ => A

def initial (A : Type) : State A := ((none, none), none)

def words (u v : List A) (b : Bool) : List A := if b then u else v

def substitute (p : (List A × List A) × List Bool) : List A :=
  p.2.flatMap (fun b => words p.1.1 p.1.2 b)

def contents (raw : List (Sym A)) (W : Bool → List A) (bs : List Bool) (buf out : List A) :
    ∀ k, List (Alphabet A k)
  | .input => raw
  | .template b => W b
  | .controls => bs
  | .buffer => buf
  | .output => out

def cfg (p : Phase) (reg : State A) (raw : List (Sym A)) (W : Bool → List A)
    (bs : List Bool) (buf out : List A) : Cfg (Alphabet A) Phase (State A) :=
  ⟨some p, reg, contents raw W bs buf out⟩

def readTemplate (b : Bool) : Sym A → Option A
  | .left (.left a) => if b then some a else none
  | .left (.right a) => if b then none else some a
  | _ => none

def readControl : Sym A → Option Bool
  | .right b => some b
  | _ => none

def tag (b : Bool) (a : A) : Sym A := if b then .left (.left a) else .left (.right a)

def nextClear (b : Bool) : Phase := if b then .clear false else .finish

def program (A : Type) [Inhabited A] : Phase → Stmt (Alphabet A) Phase (State A)
  | .scan => .pop .input (fun st head => ((head, st.1.2), st.2))
      (.branch (fun st => st.1.1.isSome)
        (.branch (fun st => (st.1.1.bind (readTemplate true)).isSome)
          (.push (.template true) (fun st => (st.1.1.bind (readTemplate true)).getD default)
            (.goto (fun _ => .scan)))
          (.branch (fun st => (st.1.1.bind (readTemplate false)).isSome)
            (.push (.template false) (fun st => (st.1.1.bind (readTemplate false)).getD default)
              (.goto (fun _ => .scan)))
            (.branch (fun st => (st.1.1.bind readControl).isSome)
              (.push .controls (fun st => (st.1.1.bind readControl).getD false) (.goto (fun _ => .scan)))
              (.goto (fun _ => .scan)))))
        (.load (fun _ => initial A) (.goto (fun _ => .outer))))
  | .outer => .pop .controls (fun _ head => ((none, head), none))
      (.branch (fun st => st.1.2.isSome)
        (.goto (fun st => .inner (st.1.2.getD false)))
        (.goto (fun _ => .clear true)))
  | .inner b => .pop (.template b) (fun st head => (st.1, head))
      (.branch (fun st => st.2.isSome)
        (.push .buffer (fun st => st.2.getD default)
          (.push .output (fun st => st.2.getD default) (.goto (fun _ => .inner b))))
        (.goto (fun _ => .restore b)))
  | .restore b => .pop .buffer (fun st head => (st.1, head))
      (.branch (fun st => st.2.isSome)
        (.push (.template b) (fun st => st.2.getD default) (.goto (fun _ => .restore b)))
        (.load (fun _ => initial A) (.goto (fun _ => .outer))))
  | .clear b => .pop (.template b) (fun st head => (st.1, head))
      (.branch (fun st => st.2.isSome) (.goto (fun _ => .clear b))
        (.load (fun _ => initial A) (.goto (fun _ => nextClear b))))
  | .finish => .halt

theorem update_input (raw raw' : List (Sym A)) (W : Bool → List A) (bs : List Bool) (buf out : List A) :
    Function.update (contents raw W bs buf out) .input raw' = contents raw' W bs buf out := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_template (raw : List (Sym A)) (W : Bool → List A) (b : Bool)
    (u : List A) (bs : List Bool) (buf out : List A) :
    Function.update (contents raw W bs buf out) (.template b) u =
      contents raw (Function.update W b u) bs buf out := by
  funext k
  cases k with
  | template c =>
    by_cases hc : c = b
    · subst c; simp [contents, Function.update]
    · simp [contents, Function.update, hc]
  | input => simp [contents, Function.update]
  | controls => simp [contents, Function.update]
  | buffer => simp [contents, Function.update]
  | output => simp [contents, Function.update]

theorem update_controls (raw : List (Sym A)) (W : Bool → List A) (bs bs' : List Bool) (buf out : List A) :
    Function.update (contents raw W bs buf out) .controls bs' = contents raw W bs' buf out := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_buffer (raw : List (Sym A)) (W : Bool → List A) (bs : List Bool) (buf buf' out : List A) :
    Function.update (contents raw W bs buf out) .buffer buf' = contents raw W bs buf' out := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_output (raw : List (Sym A)) (W : Bool → List A) (bs : List Bool) (buf out out' : List A) :
    Function.update (contents raw W bs buf out) .output out' = contents raw W bs buf out' := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

def run (A : Type) [Inhabited A] (n : ℕ) (q : Cfg (Alphabet A) Phase (State A)) :
    Option (Cfg (Alphabet A) Phase (State A)) :=
  (fun x : Option (Cfg (Alphabet A) Phase (State A)) => x.bind (step (program A)))^[n] (some q)

theorem run_step [Inhabited A] {q q' : Cfg (Alphabet A) Phase (State A)}
    (h : step (program A) q = some q') (n : ℕ) : run A (n + 1) q = run A n q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]

theorem run_add [Inhabited A] {q q' : Cfg (Alphabet A) Phase (State A)} {n : ℕ}
    (h : run A n q = some q') (m : ℕ) : run A (n + m) q = run A m q' := by
  rw [Nat.add_comm n m]
  simp only [run, Function.iterate_add_apply, show
    (fun x : Option (Cfg (Alphabet A) Phase (State A)) => x.bind (step (program A)))^[n]
      (some q) = some q' from h]

section Inhabited
variable [Inhabited A]

theorem inner_cons_step (b : Bool) (reg : State A) (raw : List (Sym A)) (W : Bool → List A)
    (a : A) (u : List A) (bs : List Bool) (buf out : List A) :
    step (program A) (cfg (.inner b) reg raw (Function.update W b (a :: u)) bs buf out) =
      some (cfg (.inner b) (reg.1, some a) raw (Function.update W b u) bs (a :: buf) (a :: out)) := by
  simp [cfg, program, step, stepAux, contents, update_template, update_buffer, update_output]

theorem inner_nil_step (b : Bool) (reg : State A) (raw : List (Sym A)) (W : Bool → List A)
    (bs : List Bool) (buf out : List A) :
    step (program A) (cfg (.inner b) reg raw (Function.update W b []) bs buf out) =
      some (cfg (.restore b) (reg.1, none) raw (Function.update W b []) bs buf out) := by
  simp [cfg, program, step, stepAux, contents]

theorem inner_run (b : Bool) (reg : State A) (raw : List (Sym A)) (W : Bool → List A)
    (u : List A) (bs : List Bool) (buf out : List A) :
    run A (u.length + 1) (cfg (.inner b) reg raw (Function.update W b u) bs buf out) =
      some (cfg (.restore b) (reg.1, none) raw (Function.update W b []) bs
        (u.reverse ++ buf) (u.reverse ++ out)) := by
  induction u generalizing reg buf out with
  | nil => simpa [run] using inner_nil_step b reg raw W bs buf out
  | cons a u ih =>
    rw [List.length_cons, run_step (inner_cons_step b reg raw W a u bs buf out)]
    simpa [List.reverse_cons, List.append_assoc] using ih (reg.1, some a) (a :: buf) (a :: out)

theorem restore_cons_step (b : Bool) (reg : State A) (raw : List (Sym A)) (W : Bool → List A)
    (u : List A) (bs : List Bool) (a : A) (buf out : List A) :
    step (program A) (cfg (.restore b) reg raw (Function.update W b u) bs (a :: buf) out) =
      some (cfg (.restore b) (reg.1, some a) raw (Function.update W b (a :: u)) bs buf out) := by
  simp [cfg, program, step, stepAux, contents, update_buffer, update_template]

theorem restore_nil_step (b : Bool) (reg : State A) (raw : List (Sym A)) (W : Bool → List A)
    (u : List A) (bs : List Bool) (out : List A) :
    step (program A) (cfg (.restore b) reg raw (Function.update W b u) bs [] out) =
      some (cfg .outer (initial A) raw (Function.update W b u) bs [] out) := by
  simp [cfg, program, step, stepAux, contents]

theorem restore_run (b : Bool) (reg : State A) (raw : List (Sym A)) (W : Bool → List A)
    (u : List A) (bs : List Bool) (buf out : List A) :
    run A (buf.length + 1) (cfg (.restore b) reg raw (Function.update W b u) bs buf out) =
      some (cfg .outer (initial A) raw (Function.update W b (buf.reverse ++ u)) bs [] out) := by
  induction buf generalizing reg u with
  | nil => simpa [run] using restore_nil_step b reg raw W u bs out
  | cons a buf ih =>
    rw [List.length_cons, run_step (restore_cons_step b reg raw W u bs a buf out)]
    simpa [List.reverse_cons, List.append_assoc] using ih (reg.1, some a) (a :: u)

theorem outer_cons_step (W : Bool → List A) (b : Bool) (bs : List Bool) (out : List A) :
    step (program A) (cfg .outer (initial A) [] W (b :: bs) [] out) =
      some (cfg (.inner b) ((none, some b), none) [] W bs [] out) := by
  simp [cfg, program, step, stepAux, contents, update_controls]

theorem outer_nil_step (W : Bool → List A) (out : List A) :
    step (program A) (cfg .outer (initial A) [] W [] [] out) =
      some (cfg (.clear true) (initial A) [] W [] [] out) := by
  simp [cfg, program, step, stepAux, contents, initial]

theorem clear_cons_step (b : Bool) (reg : State A) (raw : List (Sym A)) (W : Bool → List A)
    (a : A) (u : List A) (bs : List Bool) (buf out : List A) :
    step (program A) (cfg (.clear b) reg raw (Function.update W b (a :: u)) bs buf out) =
      some (cfg (.clear b) (reg.1, some a) raw (Function.update W b u) bs buf out) := by
  simp [cfg, program, step, stepAux, contents, update_template]

theorem clear_nil_step (b : Bool) (reg : State A) (raw : List (Sym A)) (W : Bool → List A)
    (bs : List Bool) (buf out : List A) :
    step (program A) (cfg (.clear b) reg raw (Function.update W b []) bs buf out) =
      some (cfg (nextClear b) (initial A) raw (Function.update W b []) bs buf out) := by
  simp [cfg, program, step, stepAux, contents]

theorem clear_run (b : Bool) (reg : State A) (raw : List (Sym A)) (W : Bool → List A)
    (u : List A) (bs : List Bool) (buf out : List A) :
    run A (u.length + 1) (cfg (.clear b) reg raw (Function.update W b u) bs buf out) =
      some (cfg (nextClear b) (initial A) raw (Function.update W b []) bs buf out) := by
  induction u generalizing reg with
  | nil => simpa [run] using clear_nil_step b reg raw W bs buf out
  | cons a u ih =>
    rw [List.length_cons, run_step (clear_cons_step b reg raw W a u bs buf out)]
    exact ih (reg.1, some a)

def outerTime (W : Bool → List A) : List Bool → ℕ
  | [] => (W true).length + (W false).length + 3
  | b :: bs => 2 * (W b).length + 3 + outerTime W bs

theorem outer_run (W : Bool → List A) (bs : List Bool) (out : List A) :
    run A (outerTime W bs) (cfg .outer (initial A) [] W bs [] out) =
      some (cfg .finish (initial A) [] (fun _ => []) [] []
        (bs.reverse.flatMap (fun b => (W b).reverse) ++ out)) := by
  induction bs generalizing out with
  | nil =>
    rw [outerTime, show (W true).length + (W false).length + 3 =
      ((W true).length + 1 + ((W false).length + 1)) + 1 by omega,
      run_step (outer_nil_step W out)]
    have ht := clear_run true (initial A) [] W (W true) [] [] out
    simp only [Function.update_eq_self, nextClear] at ht
    rw [run_add ht]
    have hf := clear_run false (initial A) [] (Function.update W true []) (W false) [] [] out
    have hi : Function.update (Function.update W true []) false (W false) = Function.update W true [] := by
      funext b; cases b <;> simp
    have hz : Function.update (Function.update W true []) false [] = (fun _ => []) := by
      funext b; cases b <;> simp
    simpa only [hi, hz, nextClear, Bool.false_eq_true, ↓reduceIte,
      List.reverse_nil, List.flatMap_nil, List.nil_append] using hf
  | cons b bs ih =>
    rw [outerTime, show 2 * (W b).length + 3 + outerTime W bs =
      (((W b).length + 1) + (((W b).length + 1) + outerTime W bs)) + 1 by omega,
      run_step (outer_cons_step W b bs out)]
    have hi := inner_run b ((none, some b), none) [] W (W b) bs [] out
    simp only [Function.update_eq_self, List.append_nil] at hi
    rw [run_add hi]
    have hr := restore_run b ((none, some b), none) [] W [] bs (W b).reverse ((W b).reverse ++ out)
    simp only [List.length_reverse, List.reverse_reverse, List.append_nil,
      Function.update_eq_self] at hr
    rw [run_add hr, ih]
    simp [List.reverse_cons, List.flatMap_append, List.append_assoc]

omit [Inhabited A] in
theorem outerTime_bound (W : Bool → List A) (bs : List Bool) :
    outerTime W bs ≤ bs.length * (2 * ((W true).length + (W false).length) + 3) +
      (W true).length + (W false).length + 3 := by
  induction bs with
  | nil => simp [outerTime]
  | cons b bs ih =>
    have hb : (W b).length ≤ (W true).length + (W false).length := by cases b <;> omega
    simp only [outerTime, List.length_cons]
    nlinarith

theorem scan_template_step (reg : State A) (b : Bool) (a : A) (raw : List (Sym A))
    (W : Bool → List A) (bs : List Bool) (buf out : List A) :
    step (program A) (cfg .scan reg (tag b a :: raw) W bs buf out) =
      some (cfg .scan ((some (tag b a), reg.1.2), reg.2) raw
        (Function.update W b (a :: W b)) bs buf out) := by
  cases b <;> simp [cfg, program, step, stepAux, contents, tag,
    readTemplate, readControl, update_input, update_template]

theorem scan_control_step (reg : State A) (b : Bool) (raw : List (Sym A))
    (W : Bool → List A) (bs : List Bool) (buf out : List A) :
    step (program A) (cfg .scan reg (.right b :: raw) W bs buf out) =
      some (cfg .scan ((some (.right b), reg.1.2), reg.2) raw W (b :: bs) buf out) := by
  simp [cfg, program, step, stepAux, contents, readTemplate, readControl, update_input, update_controls]

theorem scan_separator_step (reg : State A) (raw : List (Sym A))
    (W : Bool → List A) (bs : List Bool) (buf out : List A) :
    step (program A) (cfg .scan reg (.sep :: raw) W bs buf out) =
      some (cfg .scan ((some .sep, reg.1.2), reg.2) raw W bs buf out) := by
  simp [cfg, program, step, stepAux, contents, readTemplate, readControl, update_input]

theorem scan_innerSeparator_step (reg : State A) (raw : List (Sym A))
    (W : Bool → List A) (bs : List Bool) (buf out : List A) :
    step (program A) (cfg .scan reg (.left .sep :: raw) W bs buf out) =
      some (cfg .scan ((some (.left .sep), reg.1.2), reg.2) raw W bs buf out) := by
  simp [cfg, program, step, stepAux, contents, readTemplate, readControl, update_input]

theorem scan_nil_step (reg : State A) (W : Bool → List A) (bs : List Bool) (buf out : List A) :
    step (program A) (cfg .scan reg [] W bs buf out) =
      some (cfg .outer (initial A) [] W bs buf out) := by
  simp [cfg, program, step, stepAux, contents, update_input]

theorem scan_template_run (reg : State A) (b : Bool) (as : List A) (raw : List (Sym A))
    (W : Bool → List A) (bs : List Bool) (buf out : List A) :
    ∃ reg', run A as.length (cfg .scan reg (as.map (tag b) ++ raw) W bs buf out) =
      some (cfg .scan reg' raw (Function.update W b (as.reverse ++ W b)) bs buf out) := by
  induction as generalizing reg W with
  | nil => simpa only [List.length_nil, List.map_nil, List.nil_append, List.reverse_nil,
      Function.update_eq_self] using (show ∃ reg', run A 0 (cfg .scan reg raw W bs buf out) =
        some (cfg .scan reg' raw W bs buf out) from ⟨reg, rfl⟩)
  | cons a as ih =>
    obtain ⟨reg', hr⟩ := ih ((some (tag b a), reg.1.2), reg.2)
      (Function.update W b (a :: W b))
    refine ⟨reg', ?_⟩
    rw [List.length_cons]
    simp only [List.map_cons, List.cons_append]
    rw [run_step (scan_template_step reg b a _ W bs buf out)]
    simpa [List.reverse_cons, List.append_assoc] using hr

theorem scan_controls_run (reg : State A) (cs : List Bool)
    (W : Bool → List A) (bs : List Bool) (buf out : List A) :
    run A (cs.length + 1) (cfg .scan reg (cs.map .right) W bs buf out) =
      some (cfg .outer (initial A) [] W (cs.reverse ++ bs) buf out) := by
  induction cs generalizing reg bs with
  | nil => simpa [run] using scan_nil_step reg W bs buf out
  | cons b cs ih =>
    rw [List.length_cons]
    simp only [List.map_cons]
    rw [run_step (scan_control_step reg b _ W bs buf out)]
    simpa [List.reverse_cons, List.append_assoc] using
      ih ((some (.right b), reg.1.2), reg.2) (b :: bs)

def inputWord (u v : List A) (bs : List Bool) : List (Sym A) :=
  u.map (tag true) ++ .left .sep :: (v.map (tag false) ++ .sep :: bs.map .right)

omit [Inhabited A] in
theorem inputWord_length (u v : List A) (bs : List Bool) :
    (inputWord u v bs).length = u.length + v.length + bs.length + 2 := by
  simp [inputWord]
  omega

theorem scan_input_run (u v : List A) (bs : List Bool) :
    run A ((inputWord u v bs).length + 1)
      (cfg .scan (initial A) (inputWord u v bs) (fun _ => []) [] [] []) =
      some (cfg .outer (initial A) [] (words u.reverse v.reverse) bs.reverse [] []) := by
  obtain ⟨ru, hu⟩ := scan_template_run (initial A) true u
    (.left .sep :: (v.map (tag false) ++ .sep :: bs.map .right)) (fun _ => []) [] [] []
  simp only [List.append_nil] at hu
  rw [inputWord_length, show u.length + v.length + bs.length + 2 + 1 =
    u.length + ((v.length + ((bs.length + 1) + 1)) + 1) by omega]
  rw [inputWord, run_add hu, run_step (scan_innerSeparator_step ru _ _ [] [] [])]
  obtain ⟨rv, hv⟩ := scan_template_run ((some (.left .sep), ru.1.2), ru.2) false v
    (.sep :: bs.map .right) (Function.update (fun _ => []) true u.reverse) [] [] []
  rw [run_add hv, run_step (scan_separator_step rv _ _ [] [] [])]
  have he0 : Function.update (fun _ => ([] : List A)) true u.reverse false = [] := by simp
  rw [he0, List.append_nil]
  have hc := scan_controls_run ((some .sep, rv.1.2), rv.2) bs
    (Function.update (Function.update (fun _ => []) true u.reverse) false v.reverse) [] [] []
  have he : Function.update (Function.update (fun _ => []) true u.reverse) false v.reverse =
      words u.reverse v.reverse := by
    funext b; cases b <;> simp [words]
  simpa only [he, List.append_nil] using hc

def halted (out : List A) : Cfg (Alphabet A) Phase (State A) :=
  ⟨none, initial A, contents [] (fun _ => []) [] [] out⟩

theorem finish_step (out : List A) :
    step (program A) (cfg .finish (initial A) [] (fun _ => []) [] [] out) = some (halted out) := rfl

theorem program_run (u v : List A) (bs : List Bool) :
    run A ((inputWord u v bs).length + outerTime (words u.reverse v.reverse) bs.reverse + 2)
      (cfg .scan (initial A) (inputWord u v bs) (fun _ => []) [] [] []) =
      some (halted (substitute ((u, v), bs))) := by
  rw [show (inputWord u v bs).length + outerTime (words u.reverse v.reverse) bs.reverse + 2 =
    ((inputWord u v bs).length + 1) + (outerTime (words u.reverse v.reverse) bs.reverse + 1) by omega,
    run_add (scan_input_run u v bs)]
  have ho := outer_run (words u.reverse v.reverse) bs.reverse []
  have he : (fun b => (words u.reverse v.reverse b).reverse) = words u v := by
    funext b; cases b <;> simp [words]
  simp only [List.reverse_reverse, he, List.append_nil] at ho
  rw [run_add ho]
  simpa only [run] using finish_step (substitute ((u, v), bs))

def machine (A : Type) [Fintype A] [Inhabited A] : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet A
  Λ := Phase
  main := .scan
  σ := State A
  initialState := initial A
  Γk₀Fin := inferInstanceAs (Fintype (Sym A))
  m := program A

def machine_outputs [Fintype A] (u v : List A) (bs : List Bool) :
    TM2OutputsInTime (machine A) (inputWord u v bs) (some (substitute ((u, v), bs)))
      (2 * (inputWord u v bs).length ^ 2 + 5 * (inputWord u v bs).length + 5) := by
  have hi : initList (machine A) (inputWord u v bs) =
      cfg .scan (initial A) (inputWord u v bs) (fun _ => []) [] [] [] := by
    apply congrArg (fun S => (⟨some .scan, initial A, S⟩ : Cfg (Alphabet A) Phase (State A)))
    funext k; cases k <;> rfl
  have ho : haltList (machine A) (substitute ((u, v), bs)) = halted (substitute ((u, v), bs)) := by
    apply congrArg (fun S => (⟨none, initial A, S⟩ : Cfg (Alphabet A) Phase (State A)))
    funext k; cases k <;> rfl
  refine
    { steps := (inputWord u v bs).length + outerTime (words u.reverse v.reverse) bs.reverse + 2
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change run A _ (initList (machine A) _) = some (haltList (machine A) _)
    rw [hi, ho]
    exact program_run u v bs
  · have ht := outerTime_bound (words u.reverse v.reverse) bs.reverse
    simp only [words, ↓reduceIte, Bool.false_eq_true, List.length_reverse] at ht
    rw [inputWord_length]
    nlinarith

def encoding (A : Type) [Fintype A] : FinEncoding ((List A × List A) × List Bool) :=
  pairEncoding (pairEncoding (wordEncoding A) (wordEncoding A)) (wordEncoding Bool)

omit [Inhabited A] in
theorem encoding_word [Fintype A] (u v : List A) (bs : List Bool) :
    (encoding A).encode ((u, v), bs) = inputWord u v bs := by
  simp [encoding, pairEncoding, wordEncoding, inputWord, List.map_append,
    List.map_map, Function.comp_def]
  rfl

noncomputable def inhabitedComputable (A : Type) [Fintype A] [Inhabited A] :
    TM2ComputableInPolyTime (encoding A) (wordEncoding A) substitute where
  tm := machine A
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 5 * Polynomial.X + Polynomial.C 5
  outputsFun p := by
    obtain ⟨⟨u, v⟩, bs⟩ := p
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, encoding_word]
    change TM2OutputsInTime (machine A) (List.map id (inputWord u v bs))
      (some (List.map id (substitute ((u, v), bs))))
      (2 * (inputWord u v bs).length ^ 2 + 5 * (inputWord u v bs).length + 5)
    simpa only [List.map_id] using machine_outputs u v bs

end Inhabited

/-- Two input templates may have arbitrary lengths. The complete copying,
restoration and cleanup program has quadratic runtime in their joint encoding.
The empty alphabet is handled by an actual constant-output machine. -/
noncomputable def computable (A : Type) [Fintype A] :
    TM2ComputableInPolyTime
      (pairEncoding (pairEncoding (wordEncoding A) (wordEncoding A)) (wordEncoding Bool))
      (wordEncoding A) substitute := by
  classical
  by_cases h : Nonempty A
  · letI : Inhabited A := ⟨Classical.choice h⟩
    exact inhabitedComputable A
  · have he (u : List A) : u = [] := by
      cases u with
      | nil => rfl
      | cons a u => exact False.elim (h ⟨a⟩)
    have hf : (substitute : ((List A × List A) × List Bool) → List A) = fun _ => [] := by
      funext p
      simp only [substitute, he p.1.1, he p.1.2, words]
      induction p.2 <;> simp [*]
    rw [hf]
    exact TM2Constants.constantComputable _ (wordEncoding A) []

end ProteinFolding.TM2WordTemplates
