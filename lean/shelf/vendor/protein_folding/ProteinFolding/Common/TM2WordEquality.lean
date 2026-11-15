import ProteinFolding.Common.TM2Transfer

/-! A concrete polynomial-time equality test on two encoded finite words.
The first word is buffered and reversed, then compared against the second word.
Any unconsumed comparison suffix is drained before the Boolean result is emitted.
All auxiliary stacks are empty and the internal state is reset on halting. -/

namespace ProteinFolding.TM2WordEquality

open Computability Turing TM2

inductive Stack where
  | input | buffer | compare | output
  deriving DecidableEq, Fintype

inductive Label where
  | scan | reverse | compare | drain
  deriving DecidableEq, Fintype

abbrev Sym (A : Type) := PairSymbol A A

def Alphabet (A : Type) : Stack → Type
  | .input | .buffer | .compare => Sym A
  | .output => Bool

abbrev State (A : Type) := Bool × Option (Sym A)

def initialState (A : Type) : State A := (true, none)

def dataStacks {A : Type} (w l c : List (Sym A)) (o : List Bool) : ∀ k, List (Alphabet A k)
  | .input => w
  | .buffer => l
  | .compare => c
  | .output => o

theorem update_input {A : Type} (w w' l c : List (Sym A)) (o : List Bool) :
    Function.update (dataStacks w l c o) .input w' = dataStacks w' l c o := by
  funext k; cases k <;> simp [dataStacks, Function.update_of_ne]

theorem update_buffer {A : Type} (w l l' c : List (Sym A)) (o : List Bool) :
    Function.update (dataStacks w l c o) .buffer l' = dataStacks w l' c o := by
  funext k; cases k <;> simp [dataStacks, Function.update_of_ne]

theorem update_compare {A : Type} (w l c c' : List (Sym A)) (o : List Bool) :
    Function.update (dataStacks w l c o) .compare c' = dataStacks w l c' o := by
  funext k; cases k <;> simp [dataStacks, Function.update_of_ne]

theorem update_output {A : Type} (w l c : List (Sym A)) (o o' : List Bool) :
    Function.update (dataStacks w l c o) .output o' = dataStacks w l c o' := by
  funext k; cases k <;> simp [dataStacks, Function.update_of_ne]

def pairMatches {A : Type} [DecidableEq A] : Option (Sym A) → Option (Sym A) → Bool
  | some (.right a), some (.left b) => decide (b = a)
  | _, _ => false

def program (A : Type) [DecidableEq A] : Label → Stmt (Alphabet A) Label (State A)
  | .scan => .pop .input (fun st x => (st.1, x))
      (.branch (fun st => match st.2 with | some (.left _) => true | _ => false)
        (.push .buffer (fun st => st.2.getD .sep)
          (.load (fun st => (st.1, none)) (.goto (fun _ => .scan))))
        (.load (fun st => (st.1, none)) (.goto (fun _ => .reverse))))
  | .reverse =>
      letI : Inhabited (Alphabet A .buffer) := ⟨.sep⟩
      TM2Transfer.transferStmt (Γ := Alphabet A) (σ := Bool)
        .buffer .compare id .reverse .compare
  | .compare => .pop .input (fun st x => (st.1, x))
      (.branch (fun st => st.2.isSome)
        (.pop .compare (fun st x => (st.1 && pairMatches st.2 x, none)) (.goto (fun _ => .compare)))
        (.peek .compare (fun st x => (st.1 && x.isNone, none)) (.goto (fun _ => .drain))))
  | .drain => .pop .compare (fun st x => (st.1, x))
      (.branch (fun st => st.2.isSome)
        (.load (fun st => (st.1, none)) (.goto (fun _ => .drain)))
        (.push .output Prod.fst (.load (fun _ => initialState A) .halt)))

def cfg {A : Type} (l : Label) (b : Bool) (w u v : List (Sym A)) :
    Cfg (Alphabet A) Label (State A) := ⟨some l, (b, none), dataStacks w u v []⟩

def done {A : Type} (b : Bool) : Cfg (Alphabet A) Label (State A) :=
  ⟨none, initialState A, dataStacks [] [] [] [b]⟩

def run (A : Type) [DecidableEq A] (n : ℕ) (c : Cfg (Alphabet A) Label (State A)) :
    Option (Cfg (Alphabet A) Label (State A)) :=
  (fun x : Option (Cfg (Alphabet A) Label (State A)) => x.bind (step (program A)))^[n] (some c)

theorem run_step {A : Type} [DecidableEq A] {c d : Cfg (Alphabet A) Label (State A)}
    (h : step (program A) c = some d) (n : ℕ) : run A (n + 1) c = run A n d := by
  unfold run
  rw [Function.iterate_succ_apply, Option.bind_some, h]

theorem run_add {A : Type} [DecidableEq A] {c d : Cfg (Alphabet A) Label (State A)}
    {n : ℕ} (h : run A n c = some d) (m : ℕ) : run A (n + m) c = run A m d := by
  unfold run at *
  rw [Nat.add_comm n m, Function.iterate_add_apply, h]

theorem scan_left_step {A : Type} [DecidableEq A]
    (a : A) (w u v : List (Sym A)) (b : Bool) :
    step (program A) (cfg .scan b (.left a :: w) u v) =
      some (cfg .scan b w (.left a :: u) v) := by
  simp [cfg, program, step, stepAux, dataStacks, update_input, update_buffer]

theorem scan_separator_step {A : Type} [DecidableEq A]
    (w u v : List (Sym A)) (b : Bool) :
    step (program A) (cfg .scan b (.sep :: w) u v) =
      some (cfg .reverse b w u v) := by
  simp [cfg, program, step, stepAux, dataStacks, update_input]

theorem scan_run {A : Type} [DecidableEq A]
    (u : List A) (tail l c : List (Sym A)) (b : Bool) :
    run A (u.length + 1) (cfg .scan b (u.map PairSymbol.left ++ .sep :: tail) l c) =
      some (cfg .reverse b tail ((u.map PairSymbol.left).reverse ++ l) c) := by
  induction u generalizing l with
  | nil => simpa [run] using scan_separator_step tail l c b
  | cons a u ih =>
    simp only [List.map_cons, List.cons_append]
    rw [List.length_cons, show u.length + 1 + 1 = (u.length + 1) + 1 by omega]
    rw [run_step (scan_left_step a _ l c b)]
    simpa [List.map_cons, List.reverse_cons, List.append_assoc] using ih (.left a :: l)

theorem transfer_data {A : Type} (w l c : List (Sym A)) :
    TM2Transfer.setStacks (Γ := Alphabet A) Stack.buffer Stack.compare
      (dataStacks w [] [] []) l c = dataStacks w l c [] := by
  funext k
  cases k <;> simp [TM2Transfer.setStacks, dataStacks, Function.update_of_ne]

theorem reverse_run {A : Type} [DecidableEq A] (w u : List (Sym A)) (b : Bool) :
    run A (u.length + 1) (cfg .reverse b w u []) = some (cfg .compare b w [] u.reverse) := by
  letI : Inhabited (Alphabet A .buffer) := ⟨.sep⟩
  have h := TM2Transfer.transfer_run (Γ := Alphabet A) (σ := Bool)
    .buffer .compare (by decide) id .reverse .compare (program A) rfl b none
    (dataStacks w [] [] []) u []
  simpa only [TM2Transfer.transferCfg, transfer_data, List.map_id, List.append_nil, cfg, run] using h

theorem drain_nil_step {A : Type} [DecidableEq A] (b : Bool) :
    step (program A) (cfg .drain b [] [] []) = some (done b) := by
  simp [cfg, done, program, step, stepAux, dataStacks, update_compare, update_output]

theorem drain_cons_step {A : Type} [DecidableEq A] (b : Bool) (a : Sym A) (u : List (Sym A)) :
    step (program A) (cfg .drain b [] [] (a :: u)) = some (cfg .drain b [] [] u) := by
  simp [cfg, program, step, stepAux, dataStacks, update_compare]

theorem drain_run {A : Type} [DecidableEq A] (u : List (Sym A)) (b : Bool) :
    run A (u.length + 1) (cfg .drain b [] [] u) = some (done b) := by
  induction u with
  | nil => simpa [run] using drain_nil_step b
  | cons a u ih =>
    rw [List.length_cons, run_step (drain_cons_step b a u)]
    exact ih

theorem compare_nil_step {A : Type} [DecidableEq A] (u : List A) (b : Bool) :
    step (program A) (cfg .compare b [] [] (u.map PairSymbol.left)) =
      some (cfg .drain (b && decide (u = [])) [] [] (u.map PairSymbol.left)) := by
  cases u <;>
    simp [cfg, program, step, stepAux, dataStacks, update_input]

theorem compare_cons_nil_step {A : Type} [DecidableEq A] (a : A) (v : List A) (b : Bool) :
    step (program A) (cfg .compare b (PairSymbol.right a :: v.map PairSymbol.right) [] []) =
      some (cfg .compare false (v.map PairSymbol.right) [] []) := by
  simp [cfg, program, step, stepAux, dataStacks, update_input, update_compare, pairMatches]

theorem compare_cons_step {A : Type} [DecidableEq A] (a c : A) (u v : List A) (b : Bool) :
    step (program A) (cfg .compare b (PairSymbol.right c :: v.map PairSymbol.right) []
      (PairSymbol.left a :: u.map PairSymbol.left)) =
      some (cfg .compare (b && decide (a = c)) (v.map PairSymbol.right) [] (u.map PairSymbol.left)) := by
  simp [cfg, program, step, stepAux, dataStacks, update_input, update_compare, pairMatches]

theorem compare_run {A : Type} [DecidableEq A] (u v : List A) (b : Bool) :
    run A (v.length + (u.length - v.length) + 2)
      (cfg .compare b (v.map PairSymbol.right) [] (u.map PairSymbol.left)) =
        some (done (b && decide (u = v))) := by
  induction v generalizing u b with
  | nil =>
    have h := run_step (compare_nil_step u b) ((u.map (PairSymbol.left (B := A))).length + 1)
    rw [drain_run] at h
    simpa [Nat.add_assoc] using h
  | cons c v ih =>
    cases u with
    | nil =>
      rw [show (c :: v).length + ([].length - (c :: v).length) + 2 = (v.length + 2) + 1 by
        simp]
      simp only [List.map_cons, List.map_nil]
      rw [run_step (compare_cons_nil_step c v b)]
      simpa using ih [] false
    | cons a u =>
      rw [show (c :: v).length + ((a :: u).length - (c :: v).length) + 2 =
          (v.length + (u.length - v.length) + 2) + 1 by simp; omega]
      simp only [List.map_cons]
      rw [run_step (compare_cons_step a c u v b)]
      simpa [List.cons.injEq, Bool.and_assoc] using ih u (b && decide (a = c))

theorem canonical_run {A : Type} [DecidableEq A] (u v : List A) :
    run A (2 * u.length + v.length + (u.length - v.length) + 4)
      (cfg .scan true (u.map PairSymbol.left ++ PairSymbol.sep :: v.map PairSymbol.right) [] []) =
        some (done (decide (u = v))) := by
  have hscan := scan_run u (v.map PairSymbol.right) [] [] true
  simp only [List.append_nil] at hscan
  have hreverse := reverse_run (v.map PairSymbol.right) (u.map PairSymbol.left).reverse true
  simp only [List.length_reverse, List.length_map, List.reverse_reverse] at hreverse
  rw [show 2 * u.length + v.length + (u.length - v.length) + 4 =
      (u.length + 1) + ((u.length + 1) + (v.length + (u.length - v.length) + 2)) by omega,
    run_add hscan, run_add hreverse]
  simpa using compare_run u v true

def machine (A : Type) [Fintype A] [DecidableEq A] : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet A
  Λ := Label
  main := .scan
  σ := State A
  initialState := initialState A
  Γk₀Fin := inferInstanceAs (Fintype (Sym A))
  m := program A

def machine_outputs {A : Type} [Fintype A] [DecidableEq A] (u v : List A) :
    TM2OutputsInTime (machine A)
      (u.map PairSymbol.left ++ PairSymbol.sep :: v.map PairSymbol.right)
      (some [decide (u = v)])
      (4 * ((pairEncoding (wordEncoding A) (wordEncoding A)).encode (u, v)).length + 4) := by
  have hi : initList (machine A)
      (u.map PairSymbol.left ++ PairSymbol.sep :: v.map PairSymbol.right) =
      cfg .scan true (u.map PairSymbol.left ++ PairSymbol.sep :: v.map PairSymbol.right) [] [] := by
    apply congrArg (fun S : ∀ k, List (Alphabet A k) =>
      (⟨some .scan, initialState A, S⟩ : Cfg (Alphabet A) Label (State A)))
    funext k
    cases k <;> rfl
  have ho : haltList (machine A) [decide (u = v)] = done (decide (u = v)) := by
    apply congrArg (fun S : ∀ k, List (Alphabet A k) =>
      (⟨none, initialState A, S⟩ : Cfg (Alphabet A) Label (State A)))
    funext k
    cases k <;> rfl
  refine
    { steps := 2 * u.length + v.length + (u.length - v.length) + 4
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change run A _ (initList (machine A) _) = some (haltList (machine A) _)
    rw [hi, ho]
    exact canonical_run u v
  · simp only [pairEncoding, wordEncoding, List.length_append, List.length_map, List.length_cons]
    dsimp only [id]
    omega

noncomputable def wordEqualityComputable (A : Type) [Fintype A] [DecidableEq A] :
    TM2ComputableInPolyTime (pairEncoding (wordEncoding A) (wordEncoding A))
      finEncodingBoolBool (fun uv => decide (uv.1 = uv.2)) where
  tm := machine A
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 4 * Polynomial.X + Polynomial.C 4
  outputsFun uv := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime (machine A)
      (List.map id ((pairEncoding (wordEncoding A) (wordEncoding A)).encode uv))
      (some (List.map id [decide (uv.1 = uv.2)]))
      (4 * ((pairEncoding (wordEncoding A) (wordEncoding A)).encode uv).length + 4)
    simpa only [List.map_id] using machine_outputs uv.1 uv.2

theorem wordEquality_polyTimeDecidable (A : Type) [Fintype A] [DecidableEq A] :
    PolyTimeDecidable (pairEncoding (wordEncoding A) (wordEncoding A))
      (fun uv => uv.1 = uv.2) :=
  ⟨fun uv => decide (uv.1 = uv.2), ⟨wordEqualityComputable A⟩, fun _ => by simp⟩

end ProteinFolding.TM2WordEquality
