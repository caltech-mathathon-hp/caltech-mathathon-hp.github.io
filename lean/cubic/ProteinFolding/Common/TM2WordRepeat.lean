import ProteinFolding.Common.TM2PairProjections
import ProteinFolding.Common.TM2Constants
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Repeating a finite word a unary number of times by an actual finite TM2.
The reusable construction scans the input once, consumes one unary token per
outer iteration, copies the reversed word to output and a restoration buffer,
then restores the word. Cleanup empties every auxiliary stack and resets the
finite registers. No iteration is hidden in a single TM2 statement. -/

namespace ProteinFolding.TM2WordRepeat

open Computability Turing TM2

variable {A : Type}

def wordRepeat (u : List A) : ℕ → List A
  | 0 => []
  | n + 1 => wordRepeat u n ++ u

theorem repeat_succ_prepend (u : List A) (n : ℕ) : wordRepeat u (n + 1) = u ++ wordRepeat u n := by
  induction n with
  | zero => simp [wordRepeat]
  | succ n ih => simpa only [wordRepeat, List.append_assoc] using congrArg (· ++ u) ih

theorem repeat_length (u : List A) (n : ℕ) : (wordRepeat u n).length = n * u.length := by
  induction n with
  | zero => simp [wordRepeat]
  | succ n ih => simp [wordRepeat, ih, Nat.succ_mul]

inductive Slot where
  | input | word | count | buffer | output
  deriving DecidableEq, Fintype

inductive Phase where
  | scan | outer | inner | restore | clear | finish
  deriving DecidableEq, Fintype

abbrev Sym (A : Type) := PairSymbol A Bool
abbrev Registers (A : Type) := (Option (Sym A) × Option A) × Bool

def Alphabet (A : Type) : Slot → Type
  | .input => Sym A
  | .count => Bool
  | _ => A

def initialState (A : Type) : Registers A := ((none, none), false)

def contents (w : List (Sym A)) (u : List A) (n : ℕ) (v o : List A) :
    ∀ k, List (Alphabet A k)
  | .input => w
  | .word => u
  | .count => unaryEncodeNat n
  | .buffer => v
  | .output => o

theorem update_input (w w' : List (Sym A)) (u : List A) (n : ℕ) (v o : List A) :
    Function.update (contents w u n v o) .input w' = contents w' u n v o := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_word (w : List (Sym A)) (u u' : List A) (n : ℕ) (v o : List A) :
    Function.update (contents w u n v o) .word u' = contents w u' n v o := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_count (w : List (Sym A)) (u : List A) (n n' : ℕ) (v o : List A) :
    Function.update (contents w u n v o) .count (unaryEncodeNat n') = contents w u n' v o := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_count_push (w : List (Sym A)) (u : List A) (n : ℕ) (v o : List A) :
    Function.update (contents w u n v o) .count (true :: unaryEncodeNat n) =
      contents w u (n + 1) v o := update_count w u n (n + 1) v o

theorem update_buffer (w : List (Sym A)) (u : List A) (n : ℕ) (v v' o : List A) :
    Function.update (contents w u n v o) .buffer v' = contents w u n v' o := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

theorem update_output (w : List (Sym A)) (u : List A) (n : ℕ) (v o o' : List A) :
    Function.update (contents w u n v o) .output o' = contents w u n v o' := by
  funext k; cases k <;> simp [contents, Function.update_of_ne]

def isLeft : Sym A → Bool
  | .left _ => true
  | _ => false

def isRight : Sym A → Bool
  | .right _ => true
  | _ => false

def readLeft [Inhabited A] : Option (Sym A) → A
  | some (.left a) => a
  | _ => default

def program (A : Type) [Inhabited A] : Phase → Stmt (Alphabet A) Phase (Registers A)
  | .scan => .pop .input (fun st head => ((head, st.1.2), st.2))
      (.branch (fun st => st.1.1.isSome)
        (.branch (fun st => (st.1.1.map isLeft).getD false)
          (.push .word (fun st => readLeft (A := A) st.1.1) (.goto (fun _ => .scan)))
          (.branch (fun st => (st.1.1.map isRight).getD false)
            (.push .count (fun _ => true) (.goto (fun _ => .scan)))
            (.goto (fun _ => .scan))))
        (.load (fun _ => initialState A) (.goto (fun _ => .outer))))
  | .outer => .pop .count (fun st head => (st.1, head.isSome))
      (.branch Prod.snd (.goto (fun _ => .inner)) (.goto (fun _ => .clear)))
  | .inner => .pop .word (fun st head => ((st.1.1, head), head.isSome))
      (.branch Prod.snd
        (.push .buffer (fun st => st.1.2.getD default)
          (.push .output (fun st => st.1.2.getD default) (.goto (fun _ => .inner))))
        (.goto (fun _ => .restore)))
  | .restore => .pop .buffer (fun st head => ((st.1.1, head), head.isSome))
      (.branch Prod.snd
        (.push .word (fun st => st.1.2.getD default) (.goto (fun _ => .restore)))
        (.load (fun _ => initialState A) (.goto (fun _ => .outer))))
  | .clear => .pop .word (fun st head => (st.1, head.isSome))
      (.branch Prod.snd (.goto (fun _ => .clear))
        (.load (fun _ => initialState A) (.goto (fun _ => .finish))))
  | .finish => .halt

def cfg (phase : Phase) (reg : Registers A) (w : List (Sym A)) (u : List A)
    (n : ℕ) (v o : List A) : Cfg (Alphabet A) Phase (Registers A) :=
  ⟨some phase, reg, contents w u n v o⟩

def run (A : Type) [Inhabited A] (n : ℕ) (q : Cfg (Alphabet A) Phase (Registers A)) :
    Option (Cfg (Alphabet A) Phase (Registers A)) :=
  (fun x : Option (Cfg (Alphabet A) Phase (Registers A)) => x.bind (step (program A)))^[n] (some q)

theorem run_step [Inhabited A] {q q' : Cfg (Alphabet A) Phase (Registers A)}
    (h : step (program A) q = some q') (n : ℕ) : run A (n + 1) q = run A n q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]

theorem run_add [Inhabited A] {q q' : Cfg (Alphabet A) Phase (Registers A)} {n : ℕ}
    (h : run A n q = some q') (m : ℕ) : run A (n + m) q = run A m q' := by
  rw [Nat.add_comm n m]
  simp only [run, Function.iterate_add_apply, show
    (fun x : Option (Cfg (Alphabet A) Phase (Registers A)) => x.bind (step (program A)))^[n] (some q) =
      some q' from h]

section Inhabited
variable [Inhabited A]

theorem scan_step_left (reg : Registers A) (a : A) (w : List (Sym A))
    (u : List A) (n : ℕ) (v o : List A) :
    step (program A) (cfg .scan reg (.left a :: w) u n v o) =
      some (cfg .scan ((some (.left a), reg.1.2), reg.2) w (a :: u) n v o) := by
  simp [cfg, program, step, stepAux, contents, isLeft, readLeft, update_input, update_word]

theorem scan_step_right (reg : Registers A) (b : Bool) (w : List (Sym A))
    (u : List A) (n : ℕ) (v o : List A) :
    step (program A) (cfg .scan reg (.right b :: w) u n v o) =
      some (cfg .scan ((some (.right b), reg.1.2), reg.2) w u (n + 1) v o) := by
  simp [cfg, program, step, stepAux, contents, isLeft, isRight, update_count_push, update_input]

theorem scan_step_sep (reg : Registers A) (w : List (Sym A))
    (u : List A) (n : ℕ) (v o : List A) :
    step (program A) (cfg .scan reg (.sep :: w) u n v o) =
      some (cfg .scan ((some .sep, reg.1.2), reg.2) w u n v o) := by
  simp [cfg, program, step, stepAux, contents, isLeft, isRight, update_input]

theorem scan_step_nil (reg : Registers A) (u : List A) (n : ℕ) (v o : List A) :
    step (program A) (cfg .scan reg [] u n v o) =
      some (cfg .outer (initialState A) [] u n v o) := by
  simp [cfg, program, step, stepAux, contents, update_input]

theorem scan_left_run (reg : Registers A) (as : List A) (w : List (Sym A))
    (u : List A) (n : ℕ) (v o : List A) :
    ∃ reg', run A as.length (cfg .scan reg (as.map .left ++ w) u n v o) =
      some (cfg .scan reg' w (as.reverse ++ u) n v o) := by
  induction as generalizing reg u with
  | nil => exact ⟨reg, rfl⟩
  | cons a as ih =>
    obtain ⟨reg', hr⟩ := ih ((some (.left a), reg.1.2), reg.2) (a :: u)
    refine ⟨reg', ?_⟩
    rw [List.length_cons]
    simp only [List.map_cons, List.cons_append]
    rw [run_step (scan_step_left reg a _ u n v o)]
    simpa [List.reverse_cons, List.append_assoc] using hr

theorem scan_right_run (reg : Registers A) (n : ℕ) (u : List A) (k : ℕ) (v o : List A) :
    run A (n + 1) (cfg .scan reg ((unaryEncodeNat n).map .right) u k v o) =
      some (cfg .outer (initialState A) [] u (k + n) v o) := by
  induction n generalizing reg k with
  | zero => simpa [run, unaryEncodeNat] using scan_step_nil reg u k v o
  | succ n ih =>
    simp only [unaryEncodeNat, List.map_cons]
    rw [run_step (scan_step_right reg true _ u k v o)]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih ((some (.right true), reg.1.2), reg.2) (k + 1)

theorem outer_step_succ (u : List A) (n : ℕ) (o : List A) :
    step (program A) (cfg .outer (initialState A) [] u (n + 1) [] o) =
      some (cfg .inner ((none, none), true) [] u n [] o) := by
  simp [cfg, program, step, stepAux, contents, initialState, unaryEncodeNat, update_count]

theorem outer_step_zero (u o : List A) :
    step (program A) (cfg .outer (initialState A) [] u 0 [] o) =
      some (cfg .clear ((none, none), false) [] u 0 [] o) := by
  simp [cfg, program, step, stepAux, contents, initialState, unaryEncodeNat]

theorem inner_step_cons (reg : Registers A) (w : List (Sym A)) (a : A)
    (u : List A) (n : ℕ) (v o : List A) :
    step (program A) (cfg .inner reg w (a :: u) n v o) =
      some (cfg .inner ((reg.1.1, some a), true) w u n (a :: v) (a :: o)) := by
  simp [cfg, program, step, stepAux, contents, update_word, update_buffer, update_output]

theorem inner_step_nil (reg : Registers A) (w : List (Sym A)) (n : ℕ) (v o : List A) :
    step (program A) (cfg .inner reg w [] n v o) =
      some (cfg .restore ((reg.1.1, none), false) w [] n v o) := by
  simp [cfg, program, step, stepAux, contents]

theorem inner_run (reg : Registers A) (w : List (Sym A)) (u : List A)
    (n : ℕ) (v o : List A) :
    run A (u.length + 1) (cfg .inner reg w u n v o) =
      some (cfg .restore ((reg.1.1, none), false) w [] n (u.reverse ++ v) (u.reverse ++ o)) := by
  induction u generalizing reg v o with
  | nil => simpa [run] using inner_step_nil reg w n v o
  | cons a u ih =>
    rw [List.length_cons, run_step (inner_step_cons reg w a u n v o)]
    simpa [List.reverse_cons, List.append_assoc] using
      ih ((reg.1.1, some a), true) (a :: v) (a :: o)

theorem restore_step_cons (reg : Registers A) (w : List (Sym A)) (a : A)
    (u : List A) (n : ℕ) (v o : List A) :
    step (program A) (cfg .restore reg w u n (a :: v) o) =
      some (cfg .restore ((reg.1.1, some a), true) w (a :: u) n v o) := by
  simp [cfg, program, step, stepAux, contents, update_word, update_buffer]

theorem restore_step_nil (reg : Registers A) (w : List (Sym A))
    (u : List A) (n : ℕ) (o : List A) :
    step (program A) (cfg .restore reg w u n [] o) =
      some (cfg .outer (initialState A) w u n [] o) := by
  simp [cfg, program, step, stepAux, contents]

theorem restore_run (reg : Registers A) (w : List (Sym A)) (u : List A)
    (n : ℕ) (v o : List A) :
    run A (v.length + 1) (cfg .restore reg w u n v o) =
      some (cfg .outer (initialState A) w (v.reverse ++ u) n [] o) := by
  induction v generalizing reg u with
  | nil => simpa [run] using restore_step_nil reg w u n o
  | cons a v ih =>
    rw [List.length_cons, run_step (restore_step_cons reg w a u n v o)]
    simpa [List.reverse_cons, List.append_assoc] using ih ((reg.1.1, some a), true) (a :: u)

theorem clear_step_cons (reg : Registers A) (w : List (Sym A))
    (a : A) (u : List A) (n : ℕ) (v o : List A) :
    step (program A) (cfg .clear reg w (a :: u) n v o) =
      some (cfg .clear (reg.1, true) w u n v o) := by
  simp [cfg, program, step, stepAux, contents, update_word]

theorem clear_step_nil (reg : Registers A) (w : List (Sym A)) (n : ℕ) (v o : List A) :
    step (program A) (cfg .clear reg w [] n v o) =
      some (cfg .finish (initialState A) w [] n v o) := by
  simp [cfg, program, step, stepAux, contents]

theorem clear_run (reg : Registers A) (w : List (Sym A))
    (u : List A) (n : ℕ) (v o : List A) :
    run A (u.length + 1) (cfg .clear reg w u n v o) =
      some (cfg .finish (initialState A) w [] n v o) := by
  induction u generalizing reg with
  | nil => simpa [run] using clear_step_nil reg w n v o
  | cons a u ih =>
    rw [List.length_cons, run_step (clear_step_cons reg w a u n v o)]
    exact ih (reg.1, true)

theorem outer_run (u : List A) (n : ℕ) (o : List A) :
    run A (n * (2 * u.length + 3) + u.length + 2)
      (cfg .outer (initialState A) [] u n [] o) =
      some (cfg .finish (initialState A) [] [] 0 [] (wordRepeat u.reverse n ++ o)) := by
  induction n generalizing o with
  | zero =>
    rw [show 0 * (2 * u.length + 3) + u.length + 2 = (u.length + 1) + 1 by omega,
      run_step (outer_step_zero u o)]
    simpa [initialState, wordRepeat] using clear_run ((none, none), false) [] u 0 [] o
  | succ n ih =>
    rw [show (n + 1) * (2 * u.length + 3) + u.length + 2 =
      ((u.length + 1) + ((u.length + 1) +
        (n * (2 * u.length + 3) + u.length + 2))) + 1 by ring,
      run_step (outer_step_succ u n o)]
    rw [run_add (inner_run ((none, none), true) [] u n [] o)]
    simp only [List.append_nil]
    have hr := restore_run ((none, none), false) [] [] n u.reverse (u.reverse ++ o)
    simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
    rw [run_add hr, ih]
    simp only [wordRepeat, List.append_assoc]

def inputWord (u : List A) (n : ℕ) : List (Sym A) :=
  u.map .left ++ .sep :: (unaryEncodeNat n).map .right

theorem unary_length (n : ℕ) : (unaryEncodeNat n).length = n := by
  induction n <;> simp [unaryEncodeNat, *]

omit [Inhabited A] in
theorem inputWord_length (u : List A) (n : ℕ) : (inputWord u n).length = u.length + n + 1 := by
  simp [inputWord, unary_length, Nat.add_assoc]

theorem scan_input_run (u : List A) (n : ℕ) :
    run A ((inputWord u n).length + 1)
      (cfg .scan (initialState A) (inputWord u n) [] 0 [] []) =
      some (cfg .outer (initialState A) [] u.reverse n [] []) := by
  obtain ⟨reg, hl⟩ := scan_left_run (initialState A) u
    (.sep :: (unaryEncodeNat n).map .right) [] 0 [] []
  simp only [List.append_nil] at hl
  rw [inputWord_length, show u.length + n + 1 + 1 = u.length + ((n + 1) + 1) by omega]
  rw [inputWord]
  rw [run_add hl, run_step (scan_step_sep reg _ u.reverse 0 [] [])]
  simpa only [Nat.zero_add] using scan_right_run ((some .sep, reg.1.2), reg.2) n u.reverse 0 [] []

def halted (o : List A) : Cfg (Alphabet A) Phase (Registers A) :=
  ⟨none, initialState A, contents [] [] 0 [] o⟩

theorem finish_step (o : List A) :
    step (program A) (cfg .finish (initialState A) [] [] 0 [] o) = some (halted o) := rfl

theorem program_run (u : List A) (n : ℕ) :
    run A (n * (2 * u.length + 3) + (inputWord u n).length + u.length + 4)
      (cfg .scan (initialState A) (inputWord u n) [] 0 [] []) =
      some (halted (wordRepeat u n)) := by
  rw [show n * (2 * u.length + 3) + (inputWord u n).length + u.length + 4 =
    ((inputWord u n).length + 1) +
      ((n * (2 * u.length + 3) + u.length + 2) + 1) by omega,
    run_add (scan_input_run u n)]
  have ho := outer_run u.reverse n []
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at ho
  rw [run_add ho]
  simpa [run] using finish_step (wordRepeat u n)

def machine (A : Type) [Fintype A] [Inhabited A] : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet A
  Λ := Phase
  main := .scan
  σ := Registers A
  initialState := initialState A
  Γk₀Fin := inferInstanceAs (Fintype (Sym A))
  m := program A

def machine_outputs [Fintype A] (u : List A) (n : ℕ) :
    TM2OutputsInTime (machine A) (inputWord u n) (some (wordRepeat u n))
      (2 * (inputWord u n).length ^ 2 + 4 * (inputWord u n).length + 5) := by
  have hi : initList (machine A) (inputWord u n) =
      cfg .scan (initialState A) (inputWord u n) [] 0 [] [] := by
    apply congrArg (fun S =>
      (⟨some .scan, initialState A, S⟩ : Cfg (Alphabet A) Phase (Registers A)))
    funext k; cases k <;> rfl
  have ho : haltList (machine A) (wordRepeat u n) = halted (wordRepeat u n) := by
    apply congrArg (fun S =>
      (⟨none, initialState A, S⟩ : Cfg (Alphabet A) Phase (Registers A)))
    funext k; cases k <;> rfl
  refine
    { steps := n * (2 * u.length + 3) + (inputWord u n).length + u.length + 4
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change run A _ (initList (machine A) _) = some (haltList (machine A) _)
    rw [hi, ho]
    exact program_run u n
  · rw [inputWord_length]
    nlinarith

noncomputable def inhabitedComputable (A : Type) [Fintype A] [Inhabited A] :
    TM2ComputableInPolyTime (pairEncoding (wordEncoding A) unaryFinEncodingNat)
      (wordEncoding A) (fun un => wordRepeat un.1 un.2) where
  tm := machine A
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 4 * Polynomial.X + Polynomial.C 5
  outputsFun un := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime (machine A) (List.map id (inputWord un.1 un.2))
      (some (List.map id (wordRepeat un.1 un.2)))
      (2 * (inputWord un.1 un.2).length ^ 2 + 4 * (inputWord un.1 un.2).length + 5)
    simpa only [List.map_id] using machine_outputs un.1 un.2

end Inhabited

/-- Repetition over every finite alphabet, including the empty alphabet. The
empty case uses an actual constant-output machine and needs no chosen symbol. -/
noncomputable def computable (A : Type) [Fintype A] :
    TM2ComputableInPolyTime (pairEncoding (wordEncoding A) unaryFinEncodingNat)
      (wordEncoding A) (fun un => wordRepeat un.1 un.2) := by
  classical
  by_cases h : Nonempty A
  · letI : Inhabited A := ⟨Classical.choice h⟩
    exact inhabitedComputable A
  · have he (u : List A) : u = [] := by
      cases u with
      | nil => rfl
      | cons a u => exact False.elim (h ⟨a⟩)
    have hf : (fun un : List A × ℕ => wordRepeat un.1 un.2) = fun _ => [] := by
      funext un
      rw [he un.1]
      induction un.2 <;> simp [wordRepeat, *]
    rw [hf]
    exact TM2Constants.constantComputable _ (wordEncoding A) []

end ProteinFolding.TM2WordRepeat
