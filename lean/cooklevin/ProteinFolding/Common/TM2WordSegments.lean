import ProteinFolding.Common.TM2WordDrop

/-! A unary-indexed finite TM2 split after the n-th delimiter occurrence.
The delimiter belongs to the prefix. An out-of-range request returns the whole
word as prefix and an empty suffix. Counting, scanning, unused-counter cleanup
and serialization are all explicit machine stages. -/

namespace ProteinFolding.TM2WordSegments

open Computability Turing TM2

def splitMarkers {A : Type} (p : A → Bool) : List A → ℕ → List A × List A
  | [], _ => ([], [])
  | a :: w, 0 => ([], a :: w)
  | a :: w, n + 1 =>
    let r := splitMarkers p w (if p a then n else n + 1)
    (a :: r.1, r.2)

theorem splitMarkers_append {A : Type} (p : A → Bool) (w : List A) (n : ℕ) :
    (splitMarkers p w n).1 ++ (splitMarkers p w n).2 = w := by
  induction w generalizing n with
  | nil => rfl
  | cons a w ih =>
    cases n with
    | zero => rfl
    | succ n => simpa only [splitMarkers, List.cons_append] using
        congrArg (a :: ·) (ih (if p a then n else n + 1))

theorem splitMarkers_lengths {A : Type} (p : A → Bool) (w : List A) (n : ℕ) :
    (splitMarkers p w n).1.length + (splitMarkers p w n).2.length = w.length := by
  simpa only [List.length_append] using congrArg List.length (splitMarkers_append p w n)

def prefixTime {A : Type} (p : A → Bool) : List A → ℕ → ℕ
  | _, 0 => 1
  | [], n + 1 => n + 3
  | a :: w, n + 1 => 1 + prefixTime p w (if p a then n else n + 1)

theorem prefixTime_bound {A : Type} (p : A → Bool) (w : List A) (n : ℕ) :
    prefixTime p w n ≤ n + w.length + 2 := by
  induction w generalizing n with
  | nil => cases n <;> simp [prefixTime]
  | cons a w ih =>
    cases n with
    | zero => simp [prefixTime]
    | succ n =>
      have hn := ih (if p a then n else n + 1)
      cases hp : p a <;> simp [hp] at hn <;>
        simp only [prefixTime, hp, Bool.false_eq_true, if_false, if_true, List.length_cons] <;> omega

inductive Slot where
  | input | prefix | suffix | counter | output
  deriving DecidableEq, Fintype

inductive Phase where
  | count | prefix | drain | suffix | emitSuffix | separator | emitPrefix | finish
  deriving DecidableEq, Fintype

def Alphabet (A : Type) : Slot → Type
  | .input => PairSymbol Bool A
  | .prefix | .suffix => A
  | .counter => Unit
  | .output => PairSymbol A A

abbrev State (A : Type) := Bool × Option A
def initialState {A : Type} : State A := (false, none)

def contents {A : Type} (u : List (PairSymbol Bool A)) (v w : List A) (c : ℕ)
    (o : List (PairSymbol A A)) : ∀ k, List (Alphabet A k)
  | .input => u
  | .prefix => v
  | .suffix => w
  | .counter => List.replicate c ()
  | .output => o

def cfg {A : Type} (phase : Phase) (u : List (PairSymbol Bool A)) (v w : List A) (c : ℕ)
    (o : List (PairSymbol A A)) : Cfg (Alphabet A) Phase (State A) :=
  ⟨some phase, initialState, contents u v w c o⟩

instance {A : Type} [Inhabited A] : Inhabited (Alphabet A .prefix) := inferInstanceAs (Inhabited A)
instance {A : Type} [Inhabited A] : Inhabited (Alphabet A .suffix) := inferInstanceAs (Inhabited A)

def program {A : Type} [Inhabited A] (p : A → Bool) : Phase → Stmt (Alphabet A) Phase (State A)
  | .count => .pop .input (fun _ h => (TM2WordDrop.countHead h, none))
    (.branch Prod.fst
      (.push .counter (fun _ => ()) (.load (fun _ => initialState) (.goto (fun _ => .count))))
      (.load (fun _ => initialState) (.goto (fun _ => .prefix))))
  | .prefix => .peek .counter (fun _ h => (h.isSome, none))
    (.branch Prod.fst
      (.pop .input (fun _ h => (false, h.bind TM2WordDrop.readRight))
        (.branch (fun st => st.2.isSome)
          (.push .prefix (fun st => st.2.getD default)
            (.branch (fun st => p (st.2.getD default))
              (.pop .counter (fun _ _ => initialState) (.goto (fun _ => .prefix)))
              (.load (fun _ => initialState) (.goto (fun _ => .prefix)))))
          (.load (fun _ => initialState) (.goto (fun _ => .drain)))))
      (.load (fun _ => initialState) (.goto (fun _ => .suffix))))
  | .drain => .pop .counter (fun _ h => (h.isSome, none))
    (.branch Prod.fst
      (.load (fun _ => initialState) (.goto (fun _ => .drain)))
      (.load (fun _ => initialState) (.goto (fun _ => .suffix))))
  | .suffix => .pop .input (fun _ h => (false, h.bind TM2WordDrop.readRight))
    (.branch (fun st => st.2.isSome)
      (.push .suffix (fun st => st.2.getD default)
        (.load (fun _ => initialState) (.goto (fun _ => .suffix))))
      (.load (fun _ => initialState) (.goto (fun _ => .emitSuffix))))
  | .emitSuffix => TM2Transfer.transferStmt (Γ := Alphabet A) (σ := Bool)
    Slot.suffix Slot.output PairSymbol.right Phase.emitSuffix Phase.separator
  | .separator => .push .output (fun _ => .sep) (.goto (fun _ => .emitPrefix))
  | .emitPrefix => TM2Transfer.transferStmt (Γ := Alphabet A) (σ := Bool)
    Slot.prefix Slot.output PairSymbol.left Phase.emitPrefix Phase.finish
  | .finish => .load (fun _ => initialState) .halt

def run {A : Type} [Inhabited A] (p : A → Bool) (n : ℕ)
    (q : Cfg (Alphabet A) Phase (State A)) : Option (Cfg (Alphabet A) Phase (State A)) :=
  (fun x : Option (Cfg (Alphabet A) Phase (State A)) => x.bind (step (program p)))^[n] (some q)

theorem run_step {A : Type} [Inhabited A] (p : A → Bool)
    {q q' : Cfg (Alphabet A) Phase (State A)} (h : step (program p) q = some q') (n : ℕ) :
    run p (n + 1) q = run p n q' := by
  simp only [run, Function.iterate_succ_apply, Option.bind_some, h]

theorem run_add {A : Type} [Inhabited A] (p : A → Bool)
    {q q' : Cfg (Alphabet A) Phase (State A)} {n : ℕ} (h : run p n q = some q') (m : ℕ) :
    run p (n + m) q = run p m q' := by
  rw [Nat.add_comm n m]
  simp only [run, Function.iterate_add_apply, show
    (fun x : Option (Cfg (Alphabet A) Phase (State A)) => x.bind (step (program p)))^[n]
      (some q) = some q' from h]

theorem update_input {A : Type} (u u' : List (PairSymbol Bool A)) (v w : List A) (c : ℕ)
    (o : List (PairSymbol A A)) :
    Function.update (contents u v w c o) .input u' = contents u' v w c o := by
  funext k; cases k <;> simp [contents]

theorem update_prefix {A : Type} (u : List (PairSymbol Bool A)) (v v' w : List A) (c : ℕ)
    (o : List (PairSymbol A A)) :
    Function.update (contents u v w c o) .prefix v' = contents u v' w c o := by
  funext k; cases k <;> simp [contents]

theorem update_suffix {A : Type} (u : List (PairSymbol Bool A)) (v w w' : List A) (c : ℕ)
    (o : List (PairSymbol A A)) :
    Function.update (contents u v w c o) .suffix w' = contents u v w' c o := by
  funext k; cases k <;> simp [contents]

theorem update_counter {A : Type} (u : List (PairSymbol Bool A)) (v w : List A) (c c' : ℕ)
    (o : List (PairSymbol A A)) :
    Function.update (contents u v w c o) .counter (List.replicate c' ()) = contents u v w c' o := by
  funext k; cases k <;> simp [contents]

theorem update_output {A : Type} (u : List (PairSymbol Bool A)) (v w : List A) (c : ℕ)
    (o o' : List (PairSymbol A A)) :
    Function.update (contents u v w c o) .output o' = contents u v w c o' := by
  funext k; cases k <;> simp [contents]

theorem count_cons {A : Type} [Inhabited A] (p : A → Bool) (u : List (PairSymbol Bool A))
    (v w : List A) (c : ℕ) (o : List (PairSymbol A A)) :
    step (program p) (cfg .count (.left true :: u) v w c o) =
      some (cfg .count u v w (c + 1) o) := by
  simp [cfg, program, step, stepAux, contents, TM2WordDrop.countHead]
  change Function.update (Function.update (contents (.left true :: u) v w c o) .input u)
    .counter (List.replicate (c + 1) ()) = contents u v w (c + 1) o
  rw [update_input, update_counter]

theorem count_sep {A : Type} [Inhabited A] (p : A → Bool) (u : List (PairSymbol Bool A))
    (v w : List A) (c : ℕ) (o : List (PairSymbol A A)) :
    step (program p) (cfg .count (.sep :: u) v w c o) = some (cfg .prefix u v w c o) := by
  simp [cfg, program, step, stepAux, contents, TM2WordDrop.countHead]
  exact update_input _ _ _ _ _ _

theorem count_run {A : Type} [Inhabited A] (p : A → Bool) (n : ℕ)
    (u : List (PairSymbol Bool A)) (v w : List A) (c : ℕ) (o : List (PairSymbol A A)) :
    run p (n + 1) (cfg .count ((unaryEncodeNat n).map .left ++ .sep :: u) v w c o) =
      some (cfg .prefix u v w (c + n) o) := by
  induction n generalizing c with
  | zero => simpa only [run, unaryEncodeNat, List.map_nil, List.nil_append, Nat.add_zero,
      Nat.zero_add, Function.iterate_one, Option.bind_some] using count_sep p u v w c o
  | succ n ih =>
    simp only [unaryEncodeNat, List.map_cons, List.cons_append]
    rw [run_step p (count_cons p _ _ _ _ _)]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (c + 1)

theorem prefix_zero {A : Type} [Inhabited A] (p : A → Bool) (u : List (PairSymbol Bool A))
    (v w : List A) (o : List (PairSymbol A A)) :
    step (program p) (cfg .prefix u v w 0 o) = some (cfg .suffix u v w 0 o) := by
  simp [cfg, program, step, stepAux, contents]

theorem prefix_nil {A : Type} [Inhabited A] (p : A → Bool) (v w : List A) (n : ℕ)
    (o : List (PairSymbol A A)) :
    step (program p) (cfg .prefix [] v w (n + 1) o) = some (cfg .drain [] v w (n + 1) o) := by
  simp [cfg, program, step, stepAux, contents, List.replicate_succ]

theorem prefix_cons {A : Type} [Inhabited A] (p : A → Bool) (a : A)
    (u : List (PairSymbol Bool A)) (v w : List A) (n : ℕ) (o : List (PairSymbol A A)) :
    step (program p) (cfg .prefix (.right a :: u) v w (n + 1) o) =
      some (cfg .prefix u (a :: v) w (if p a then n else n + 1) o) := by
  cases hp : p a <;> simp [cfg, program, step, stepAux, contents, List.replicate_succ,
    TM2WordDrop.readRight, hp]
  · change Function.update (Function.update (contents (.right a :: u) v w (n + 1) o) .input u)
      .prefix (a :: v) = contents u (a :: v) w (n + 1) o
    rw [update_input, update_prefix]
  · change Function.update
      (Function.update (Function.update (contents (.right a :: u) v w (n + 1) o) .input u)
        .prefix (a :: v)) .counter (List.replicate n ()) = contents u (a :: v) w n o
    rw [update_input, update_prefix, update_counter]

theorem drain_cons {A : Type} [Inhabited A] (p : A → Bool) (u : List (PairSymbol Bool A))
    (v w : List A) (n : ℕ) (o : List (PairSymbol A A)) :
    step (program p) (cfg .drain u v w (n + 1) o) = some (cfg .drain u v w n o) := by
  simp [cfg, program, step, stepAux, contents, List.replicate_succ]
  exact update_counter _ _ _ _ _ _

theorem drain_zero {A : Type} [Inhabited A] (p : A → Bool) (u : List (PairSymbol Bool A))
    (v w : List A) (o : List (PairSymbol A A)) :
    step (program p) (cfg .drain u v w 0 o) = some (cfg .suffix u v w 0 o) := by
  simp [cfg, program, step, stepAux, contents]

theorem drain_run {A : Type} [Inhabited A] (p : A → Bool) (u : List (PairSymbol Bool A))
    (v w : List A) (n : ℕ) (o : List (PairSymbol A A)) :
    run p (n + 1) (cfg .drain u v w n o) = some (cfg .suffix u v w 0 o) := by
  induction n with
  | zero => simpa only [run, Function.iterate_one, Option.bind_some] using drain_zero p u v w o
  | succ n ih => rw [run_step p (drain_cons p u v w n o), ih]

theorem prefix_run {A : Type} [Inhabited A] (p : A → Bool) (u v w : List A) (n : ℕ)
    (o : List (PairSymbol A A)) :
    run p (prefixTime p u n) (cfg .prefix (u.map .right) v w n o) =
      some (cfg .suffix ((splitMarkers p u n).2.map .right)
        ((splitMarkers p u n).1.reverse ++ v) w 0 o) := by
  induction u generalizing n v with
  | nil =>
    cases n with
    | zero => simpa only [prefixTime, splitMarkers, List.map_nil, List.reverse_nil, List.nil_append,
        run, Function.iterate_one, Option.bind_some] using prefix_zero p [] v w o
    | succ n =>
      change run p (n + 3) (cfg .prefix [] v w (n + 1) o) = some (cfg .suffix [] v w 0 o)
      rw [show n + 3 = (n + 2) + 1 by omega, run_step p (prefix_nil p v w n o)]
      exact drain_run p [] v w (n + 1) o
  | cons a u ih =>
    cases n with
    | zero => simpa only [prefixTime, splitMarkers, List.reverse_nil, List.nil_append,
        run, Function.iterate_one, Option.bind_some] using prefix_zero p ((a :: u).map .right) v w o
    | succ n =>
      simp only [prefixTime, List.map_cons]
      rw [show 1 + prefixTime p u (if p a then n else n + 1) =
          prefixTime p u (if p a then n else n + 1) + 1 by omega,
        run_step p (prefix_cons p a _ v w n o), ih]
      simp [splitMarkers, List.reverse_cons, List.append_assoc]

theorem suffix_cons {A : Type} [Inhabited A] (p : A → Bool) (a : A)
    (u : List (PairSymbol Bool A)) (v w : List A) (c : ℕ) (o : List (PairSymbol A A)) :
    step (program p) (cfg .suffix (.right a :: u) v w c o) =
      some (cfg .suffix u v (a :: w) c o) := by
  simp [cfg, program, step, stepAux, contents, TM2WordDrop.readRight]
  change Function.update (Function.update (contents (.right a :: u) v w c o) .input u)
    .suffix (a :: w) = contents u v (a :: w) c o
  rw [update_input, update_suffix]

theorem suffix_nil {A : Type} [Inhabited A] (p : A → Bool) (v w : List A) (c : ℕ)
    (o : List (PairSymbol A A)) :
    step (program p) (cfg .suffix [] v w c o) = some (cfg .emitSuffix [] v w c o) := by
  simp [cfg, program, step, stepAux, contents]

theorem suffix_run {A : Type} [Inhabited A] (p : A → Bool) (u v w : List A) (c : ℕ)
    (o : List (PairSymbol A A)) :
    run p (u.length + 1) (cfg .suffix (u.map .right) v w c o) =
      some (cfg .emitSuffix [] v (u.reverse ++ w) c o) := by
  induction u generalizing w with
  | nil => simpa only [run, List.map_nil, List.length_nil, Nat.zero_add, Function.iterate_one,
      Option.bind_some, List.reverse_nil, List.nil_append] using suffix_nil p v w c o
  | cons a u ih =>
    simp only [List.map_cons, List.length_cons]
    rw [run_step p (suffix_cons p a _ v w c o), ih]
    simp

theorem emitSuffix_contents {A : Type} (u : List (PairSymbol Bool A)) (v w : List A) (c : ℕ)
    (o : List (PairSymbol A A)) :
    TM2Transfer.setStacks Slot.suffix Slot.output (contents u v [] c []) w o = contents u v w c o := by
  funext k; cases k <;> simp [TM2Transfer.setStacks, contents]

theorem emitSuffix_run {A : Type} [Inhabited A] (p : A → Bool)
    (u : List (PairSymbol Bool A)) (v w : List A) (c : ℕ) (o : List (PairSymbol A A)) :
    run p (w.length + 1) (cfg .emitSuffix u v w c o) =
      some (cfg .separator u v [] c ((w.map .right).reverse ++ o)) := by
  have h := TM2Transfer.transfer_run (Γ := Alphabet A) Slot.suffix Slot.output (by decide)
    PairSymbol.right Phase.emitSuffix Phase.separator (program p) rfl false none
    (contents u v [] c []) w o
  simpa only [run, cfg, initialState, TM2Transfer.transferCfg, emitSuffix_contents] using h

theorem separator_step {A : Type} [Inhabited A] (p : A → Bool)
    (u : List (PairSymbol Bool A)) (v w : List A) (c : ℕ) (o : List (PairSymbol A A)) :
    step (program p) (cfg .separator u v w c o) =
      some (cfg .emitPrefix u v w c (.sep :: o)) := by
  simp [cfg, program, step, stepAux, contents]
  exact update_output _ _ _ _ _ _

theorem emitPrefix_contents {A : Type} (u : List (PairSymbol Bool A)) (v w : List A) (c : ℕ)
    (o : List (PairSymbol A A)) :
    TM2Transfer.setStacks Slot.prefix Slot.output (contents u [] w c []) v o = contents u v w c o := by
  funext k; cases k <;> simp [TM2Transfer.setStacks, contents]

theorem emitPrefix_run {A : Type} [Inhabited A] (p : A → Bool)
    (u : List (PairSymbol Bool A)) (v w : List A) (c : ℕ) (o : List (PairSymbol A A)) :
    run p (v.length + 1) (cfg .emitPrefix u v w c o) =
      some (cfg .finish u [] w c ((v.map .left).reverse ++ o)) := by
  have h := TM2Transfer.transfer_run (Γ := Alphabet A) Slot.prefix Slot.output (by decide)
    PairSymbol.left Phase.emitPrefix Phase.finish (program p) rfl false none
    (contents u [] w c []) v o
  simpa only [run, cfg, initialState, TM2Transfer.transferCfg, emitPrefix_contents] using h

def halted {A : Type} (o : List (PairSymbol A A)) : Cfg (Alphabet A) Phase (State A) :=
  ⟨none, initialState, contents [] [] [] 0 o⟩

theorem finish_step {A : Type} [Inhabited A] (p : A → Bool) (o : List (PairSymbol A A)) :
    step (program p) (cfg .finish [] [] [] 0 o) = some (halted o) := rfl

theorem suffix_finish_run {A : Type} [Inhabited A] (p : A → Bool) (v w : List A) :
    run p (2 * w.length + v.length + 5) (cfg .suffix (w.map .right) v.reverse [] 0 []) =
      some (halted (v.map .left ++ .sep :: w.map .right)) := by
  rw [show 2 * w.length + v.length + 5 =
      (w.length + 1) + ((w.reverse.length + 1) + ((v.reverse.length + 2) + 1)) by simp; omega]
  rw [run_add p (suffix_run p w v.reverse [] 0 [])]
  simp only [List.append_nil]
  rw [run_add p (emitSuffix_run p [] v.reverse w.reverse 0 [])]
  simp only [List.map_reverse, List.reverse_reverse, List.append_nil]
  rw [run_step p (separator_step p [] v.reverse [] 0 (w.map .right))]
  rw [show v.reverse.length + 2 = (v.reverse.length + 1) + 1 by omega,
    run_add p (emitPrefix_run p [] v.reverse [] 0 (.sep :: w.map .right))]
  simp only [List.map_reverse, List.reverse_reverse]
  exact finish_step p _

theorem program_run {A : Type} [Inhabited A] (p : A → Bool) (n : ℕ) (w : List A) :
    run p (n + prefixTime p w n + 2 * (splitMarkers p w n).2.length +
      (splitMarkers p w n).1.length + 6)
      (cfg .count ((unaryEncodeNat n).map .left ++ .sep :: w.map .right) [] [] 0 []) =
      some (halted ((splitMarkers p w n).1.map .left ++ .sep :: (splitMarkers p w n).2.map .right)) := by
  rw [show n + prefixTime p w n + 2 * (splitMarkers p w n).2.length +
      (splitMarkers p w n).1.length + 6 = (n + 1) + (prefixTime p w n +
        (2 * (splitMarkers p w n).2.length + (splitMarkers p w n).1.length + 5)) by omega]
  rw [run_add p (count_run p n (w.map .right) [] [] 0 [])]
  simp only [Nat.zero_add]
  rw [run_add p (prefix_run p w [] [] n [])]
  simp only [List.append_nil]
  exact suffix_finish_run p (splitMarkers p w n).1 (splitMarkers p w n).2

def machine (A : Type) [Fintype A] [Inhabited A] (p : A → Bool) : FinTM2 where
  K := Slot
  k₀ := .input
  k₁ := .output
  Γ := Alphabet A
  Λ := Phase
  main := .count
  σ := State A
  initialState := initialState
  Γk₀Fin := inferInstanceAs (Fintype (PairSymbol Bool A))
  m := program p

def machine_outputs {A : Type} [Fintype A] [Inhabited A] (p : A → Bool) (n : ℕ) (w : List A) :
    TM2OutputsInTime (machine A p)
      ((unaryEncodeNat n).map .left ++ .sep :: w.map .right)
      (some ((pairEncoding (wordEncoding A) (wordEncoding A)).encode (splitMarkers p w n)))
      (3 * ((pairEncoding unaryFinEncodingNat (wordEncoding A)).encode (n, w)).length + 8) := by
  have hi : initList (machine A p) ((unaryEncodeNat n).map .left ++ .sep :: w.map .right) =
      cfg .count ((unaryEncodeNat n).map .left ++ .sep :: w.map .right) [] [] 0 [] := by
    apply congrArg (fun S => (⟨some .count, initialState, S⟩ : Cfg (Alphabet A) Phase (State A)))
    funext k; cases k <;> rfl
  have ho : haltList (machine A p)
      ((pairEncoding (wordEncoding A) (wordEncoding A)).encode (splitMarkers p w n)) =
      halted ((splitMarkers p w n).1.map .left ++ .sep :: (splitMarkers p w n).2.map .right) := by
    apply congrArg (fun S => (⟨none, initialState, S⟩ : Cfg (Alphabet A) Phase (State A)))
    funext k; cases k <;> rfl
  refine
    { steps := n + prefixTime p w n + 2 * (splitMarkers p w n).2.length +
        (splitMarkers p w n).1.length + 6
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change run p _ (initList (machine A p) _) = some (haltList (machine A p) _)
    rw [hi, ho]
    exact program_run p n w
  · have ht := prefixTime_bound p w n
    have hl := splitMarkers_lengths p w n
    simp only [pairEncoding, unaryFinEncodingNat, wordEncoding, List.length_append,
      List.length_map, List.length_cons, TM2WordDrop.unary_length]
    dsimp only [id]
    omega

noncomputable def prefixSplitComputable (A : Type) [Fintype A] [Inhabited A] (p : A → Bool) :
    TM2ComputableInPolyTime (pairEncoding unaryFinEncodingNat (wordEncoding A))
      (pairEncoding (wordEncoding A) (wordEncoding A)) (fun x => splitMarkers p x.2 x.1) where
  tm := machine A p
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 3 * Polynomial.X + Polynomial.C 8
  outputsFun x := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    change TM2OutputsInTime (machine A p)
      (List.map id ((pairEncoding unaryFinEncodingNat (wordEncoding A)).encode x))
      (some (List.map id ((pairEncoding (wordEncoding A) (wordEncoding A)).encode (splitMarkers p x.2 x.1))))
      (3 * ((pairEncoding unaryFinEncodingNat (wordEncoding A)).encode x).length + 8)
    simpa only [List.map_id] using machine_outputs p x.1 x.2

/-- Split a word immediately after its n-th marker occurrence, using an
ordinary unary-indexed pair input and an actual polynomial-time machine. -/
noncomputable def splitComputable (A : Type) [Fintype A] [Inhabited A] (p : A → Bool) :
    TM2ComputableInPolyTime (pairEncoding (wordEncoding A) unaryFinEncodingNat)
      (pairEncoding (wordEncoding A) (wordEncoding A)) (fun x => splitMarkers p x.1 x.2) :=
  TM2CompositionPoly.compose
    (TM2PairSwap.swapComputable (wordEncoding A) unaryFinEncodingNat) (prefixSplitComputable A p)

end ProteinFolding.TM2WordSegments
