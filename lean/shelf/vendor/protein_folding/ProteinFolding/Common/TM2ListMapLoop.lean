import ProteinFolding.Common.TM2ListMapTransfers

/-! Complete child calls and record iteration for the parameterized mapper. -/

namespace ProteinFolding.TM2ListMap

open Computability Turing TM2

variable {P A B : Type} {ep : FinEncoding P} {ea : FinEncoding A}
  {f : P × A → List B} [Fintype B]
  (h : TM2ComputableInPolyTime (pairEncoding ep ea) (wordEncoding B) f)

def emptyChild : ∀ k, List (h.tm.Γ k) := fun _ => []

theorem empty_update (k : h.tm.K) : Function.update (emptyChild h) k [] = emptyChild h :=
  Function.update_eq_self k (emptyChild h)

def parameterWord (p : P) : List (InLetter h) := (leftCode h (ep.encode p)).reverse

def childInput (p : P) (a : A) : List (InLetter h) :=
  leftCode h (ep.encode p) ++ separator h :: rightCode h (ea.encode a)

def childOutput (p : P) (a : A) : List (OutLetter h) :=
  (f (p, a)).map (fun b : B => h.outputAlphabet.symm b)

noncomputable def childSteps (p : P) (a : A) : ℕ := (h.outputsFun (p, a)).steps

theorem childInput_code (p : P) (a : A) : childInput h p a =
    ((pairEncoding ep ea).encode (p, a)).map h.inputAlphabet.symm := by
  simp [childInput, pairEncoding, leftCode, rightCode, separator,
    List.map_append, List.map_map, Function.comp_def]

theorem initList_stacks (w : List (InLetter h)) :
    (initList h.tm w).stk = Function.update (emptyChild h) h.tm.k₀ w := by
  funext k
  by_cases hk : k = h.tm.k₀
  · subst k; simp [initList, Function.update]
  · simp [initList, Function.update, hk, emptyChild]

theorem haltList_stacks (w : List (OutLetter h)) :
    (haltList h.tm w).stk = Function.update (emptyChild h) h.tm.k₁ w := by
  funext k
  by_cases hk : k = h.tm.k₁
  · subst k; simp [haltList, Function.update]
  · simp [haltList, Function.update, hk, emptyChild]

theorem childOutput_length (p : P) (a : A) : (childOutput h p a).length = (f (p, a)).length := by
  simp [childOutput]

theorem childOutput_decode (p : P) (a : A) : (childOutput h p a).map (outputSymbol h) = f (p, a) := by
  simp [childOutput, outputSymbol, List.map_map, Function.comp_def]

def rawRecords (xs : List A) : List (RawSymbol (ep := ep) (ea := ea)) :=
  (encodeFields ea xs).map .right

theorem rawRecords_cons (a : A) (xs : List A) : rawRecords (ep := ep) (ea := ea) (a :: xs) =
    (ea.encode a).map (fun c => .right (some c)) ++ .right none :: rawRecords (ep := ep) (ea := ea) xs := by
  simp [rawRecords, encodeFields, List.map_append, List.map_map, Function.comp_def]

section Inhabited
variable [Inhabited B]

theorem child_run (p : P) (a : A) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (acc : List (OutLetter h)) (out : List B) :
    run h (childSteps h p a)
      (cfg h (.child h.tm.main) (initial h)
        (Function.update (emptyChild h) h.tm.k₀ (childInput h p a)) raw (parameterWord h p) [] [] acc out) =
      some (cfg h .drainChild (initial h)
        (Function.update (emptyChild h) h.tm.k₁ (childOutput h p a)) raw (parameterWord h p) [] [] acc out) := by
  let E := TM2Embedding.embedCfg (Γ := h.tm.Γ) (σ := h.tm.σ)
    (Label.child : h.tm.Λ → Phase h) (some .drainChild)
    ((none, none) : Caches h) (extraContents h raw (parameterWord h p) [] [] acc out)
  have hc : (fun q : Option h.tm.Cfg => q.bind h.tm.step)^[childSteps h p a]
      (some (initList h.tm (childInput h p a))) = some (haltList h.tm (childOutput h p a)) := by
    have ht := (h.outputsFun (p, a)).evals_in_steps
    simpa only [childSteps, childInput_code, childOutput, wordEncoding] using ht
  have he := TM2Embedding.simulate_run h.tm.step (step (program h)) E
    (fun c d hd => TM2Embedding.step_liftStmt Label.child (some .drainChild)
      h.tm.m (program h) (fun _ => rfl) ((none, none) : Caches h)
      (extraContents h raw (parameterWord h p) [] [] acc out) c d hd)
    (childSteps h p a) (initList h.tm (childInput h p a)) (haltList h.tm (childOutput h p a)) hc
  have hi : E (initList h.tm (childInput h p a)) =
      cfg h (.child h.tm.main) (initial h)
        (Function.update (emptyChild h) h.tm.k₀ (childInput h p a)) raw (parameterWord h p) [] [] acc out := by
    simp only [E, TM2Embedding.embedCfg, initList_stacks, cfg, contents, initial]
    rfl
  have ho : E (haltList h.tm (childOutput h p a)) =
      cfg h .drainChild (initial h)
        (Function.update (emptyChild h) h.tm.k₁ (childOutput h p a)) raw (parameterWord h p) [] [] acc out := by
    simp only [E, TM2Embedding.embedCfg, haltList_stacks, cfg, contents, initial]
    rfl
  change run h (childSteps h p a) (E (initList h.tm (childInput h p a))) =
    some (E (haltList h.tm (childOutput h p a))) at he
  rw [hi, ho] at he
  exact he

theorem separator_step (S : ∀ k, List (h.tm.Γ k))
    (raw : List (RawSymbol (ep := ep) (ea := ea))) (p r b : List (InLetter h))
    (acc : List (OutLetter h)) (out : List B) (w : List (InLetter h)) :
    step (program h)
      (cfg h .separator (initial h) (Function.update S h.tm.k₀ w) raw p r b acc out) =
      some (cfg h .copyParameter (initial h)
        (Function.update S h.tm.k₀ (separator h :: w)) raw p r b acc out) := by
  simp [cfg, program, step, stepAux, contents, TM2Embedding.joinStacks]
  change Function.update (contents h (Function.update S h.tm.k₀ w) raw p r b acc out)
    (.inl h.tm.k₀) (separator h :: w) = _
  rw [update_child, Function.update_idem]
  rfl

theorem prepare_record_run (p : P) (a : A) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (acc : List (OutLetter h)) (out : List B) :
    run h ((ea.encode a).length + 2 * (ep.encode p).length + 4)
      (cfg h .restoreRecord (initial h) (emptyChild h) raw (parameterWord h p)
        (rightCode h (ea.encode a)).reverse [] acc out) =
      some (cfg h (.child h.tm.main) (initial h)
        (Function.update (emptyChild h) h.tm.k₀ (childInput h p a)) raw (parameterWord h p) [] [] acc out) := by
  have hr := restoreRecord_run h h.tm.initialState none none (emptyChild h) raw
    (parameterWord h p) (rightCode h (ea.encode a)).reverse [] acc out []
  simp only [empty_update, List.reverse_reverse, List.append_nil, List.length_reverse,
    rightCode, List.length_map] at hr
  change run h ((ea.encode a).length + 1)
    (cfg h .restoreRecord (initial h) (emptyChild h) raw (parameterWord h p)
      (rightCode h (ea.encode a)).reverse [] acc out) =
    some (cfg h .separator (initial h)
      (Function.update (emptyChild h) h.tm.k₀ (rightCode h (ea.encode a))) raw
      (parameterWord h p) [] [] acc out) at hr
  rw [show (ea.encode a).length + 2 * (ep.encode p).length + 4 =
    ((ea.encode a).length + 1) + (((ep.encode p).length + 1) + ((ep.encode p).length + 1) + 1) by omega,
    run_add h hr]
  rw [run_step h (separator_step h (emptyChild h) raw (parameterWord h p) [] [] acc out _)]
  have hp := copyParameter_run h h.tm.initialState none none (emptyChild h) raw
    (parameterWord h p) [] [] acc out (separator h :: rightCode h (ea.encode a))
  simp only [parameterWord, List.reverse_reverse, List.append_nil, List.length_reverse,
    leftCode, List.length_map] at hp
  change run h ((ep.encode p).length + 1)
    (cfg h .copyParameter (initial h)
      (Function.update (emptyChild h) h.tm.k₀ (separator h :: rightCode h (ea.encode a)))
      raw (parameterWord h p) [] [] acc out) =
    some (cfg h .restoreParameter (initial h)
      (Function.update (emptyChild h) h.tm.k₀ (childInput h p a)) raw [] []
      (leftCode h (ep.encode p)) acc out) at hp
  rw [run_add h hp]
  have hrestore := restoreParameter_run h h.tm.initialState none none
    (Function.update (emptyChild h) h.tm.k₀ (childInput h p a)) raw [] []
    (leftCode h (ep.encode p)) acc out
  simpa only [List.append_nil, leftCode, List.length_map, parameterWord, childInput, initial] using hrestore

theorem clearParameter_step_cons (s : h.tm.σ) (reg : Caches h)
    (S : ∀ k, List (h.tm.Γ k)) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (a : InLetter h) (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    step (program h) (cfg h .clearParameter (s, reg) S raw (a :: p) r b acc out) =
      some (cfg h .clearParameter (s, (some a, reg.2)) S raw p r b acc out) := by
  simp [cfg, program, step, stepAux, contents, TM2Embedding.joinStacks, extraContents]
  exact update_parameter h S raw (a :: p) p r b acc out

theorem clearParameter_step_nil (s : h.tm.σ) (reg : Caches h)
    (S : ∀ k, List (h.tm.Γ k)) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    step (program h) (cfg h .clearParameter (s, reg) S raw [] r b acc out) =
      some (cfg h .output (s, (none, reg.2)) S raw [] r b acc out) := by
  simp [cfg, program, step, stepAux, contents, TM2Embedding.joinStacks, extraContents]

theorem clearParameter_run (s : h.tm.σ) (reg : Caches h)
    (S : ∀ k, List (h.tm.Γ k)) (raw : List (RawSymbol (ep := ep) (ea := ea)))
    (p r b : List (InLetter h)) (acc : List (OutLetter h)) (out : List B) :
    run h (p.length + 1) (cfg h .clearParameter (s, reg) S raw p r b acc out) =
      some (cfg h .output (s, (none, reg.2)) S raw [] r b acc out) := by
  induction p generalizing reg with
  | nil => simpa [run] using clearParameter_step_nil h s reg S raw r b acc out
  | cons a p ih =>
    rw [List.length_cons, run_step h (clearParameter_step_cons h s reg S raw a p r b acc out)]
    exact ih (some a, reg.2)

def halted (out : List B) : Cfg (Alphabet h) (Phase h) (State h) :=
  ⟨none, initial h, contents h (emptyChild h) [] [] [] [] [] out⟩

theorem finish_step (out : List B) :
    step (program h) (cfg h .finish (initial h) (emptyChild h) [] [] [] [] [] out) =
      some (halted h out) := rfl

noncomputable def recordTime (p : P) (a : A) : ℕ :=
  2 * (ea.encode a).length + 2 * (ep.encode p).length + 6 + childSteps h p a + (f (p, a)).length

theorem record_iteration (p : P) (a : A) (xs : List A)
    (acc : List (OutLetter h)) (out : List B) :
    run h (recordTime h p a)
      (cfg h .record (initial h) (emptyChild h) (rawRecords (ep := ep) (ea := ea) (a :: xs))
        (parameterWord h p) [] [] acc out) =
      some (cfg h .record (initial h) (emptyChild h) (rawRecords (ep := ep) (ea := ea) xs)
        (parameterWord h p) [] [] ((childOutput h p a).reverse ++ acc) out) := by
  have hr := record_run h h.tm.initialState (none, none) (emptyChild h) (ea.encode a)
    (rawRecords (ep := ep) (ea := ea) xs) (parameterWord h p) [] [] acc out
  simp only [List.append_nil] at hr
  change run h ((ea.encode a).length + 1)
    (cfg h .record (initial h) (emptyChild h)
      ((ea.encode a).map (fun c => .right (some c)) ++ .right none :: rawRecords (ep := ep) (ea := ea) xs)
      (parameterWord h p) [] [] acc out) =
    some (cfg h .restoreRecord (initial h) (emptyChild h)
      (rawRecords (ep := ep) (ea := ea) xs) (parameterWord h p)
      (rightCode h (ea.encode a)).reverse [] acc out) at hr
  rw [rawRecords_cons, show recordTime h p a = ((ea.encode a).length + 1) +
    (((ea.encode a).length + 2 * (ep.encode p).length + 4) +
      (childSteps h p a + ((f (p, a)).length + 1))) by dsimp [recordTime]; omega,
    run_add h hr,
    run_add h (prepare_record_run h p a (rawRecords xs) acc out),
    run_add h (child_run h p a (rawRecords xs) acc out)]
  have hd := drainChild_run h h.tm.initialState none none (emptyChild h) (rawRecords xs)
    (parameterWord h p) [] [] acc out (childOutput h p a)
  simp only [childOutput_length, empty_update] at hd
  exact hd

def flatOutput (p : P) (xs : List A) : List B := xs.flatMap (fun a => f (p, a))

noncomputable def recordsTime (p : P) : List A → ℕ
  | [] => 0
  | a :: xs => recordTime h p a + recordsTime p xs

theorem records_run (p : P) (xs : List A) (acc : List (OutLetter h)) (out : List B) :
    run h (recordsTime h p xs + (ep.encode p).length + acc.length + (flatOutput (f := f) p xs).length + 4)
      (cfg h .record (initial h) (emptyChild h) (rawRecords (ep := ep) (ea := ea) xs)
        (parameterWord h p) [] [] acc out) =
      some (halted h ((acc.map (outputSymbol h)).reverse ++ flatOutput (f := f) p xs ++ out)) := by
  induction xs generalizing acc with
  | nil =>
    simp only [recordsTime, flatOutput, List.flatMap_nil, List.length_nil,
      Nat.zero_add, Nat.add_zero, rawRecords, encodeFields, List.map_nil, List.append_nil]
    have hn := record_nil_step h h.tm.initialState (none, none) (emptyChild h)
      (parameterWord h p) [] [] acc out
    change step (program h)
      (cfg h .record (initial h) (emptyChild h) [] (parameterWord h p) [] [] acc out) =
      some (cfg h .clearParameter (initial h) (emptyChild h) [] (parameterWord h p) [] [] acc out) at hn
    rw [show (ep.encode p).length + acc.length + 4 =
      (((ep.encode p).length + 1) + ((acc.length + 1) + 1)) + 1 by omega,
      run_step h hn]
    have hc := clearParameter_run h h.tm.initialState (none, none) (emptyChild h) []
      (parameterWord h p) [] [] acc out
    simp only [parameterWord, leftCode, List.length_reverse, List.length_map] at hc
    change run h ((ep.encode p).length + 1)
      (cfg h .clearParameter (initial h) (emptyChild h) [] (parameterWord h p) [] [] acc out) =
      some (cfg h .output (initial h) (emptyChild h) [] [] [] [] acc out) at hc
    rw [run_add h hc]
    have ho := output_run h h.tm.initialState none none (emptyChild h) [] [] [] [] acc out
    change run h (acc.length + 1) (cfg h .output (initial h) (emptyChild h) [] [] [] [] acc out) =
      some (cfg h .finish (initial h) (emptyChild h) [] [] [] [] []
        ((acc.map (outputSymbol h)).reverse ++ out)) at ho
    rw [run_add h ho]
    simpa only [run, flatOutput, List.flatMap_nil, List.append_nil] using
      finish_step h ((acc.map (outputSymbol h)).reverse ++ out)
  | cons a xs ih =>
    have he : recordsTime h p (a :: xs) + (ep.encode p).length + acc.length +
        (flatOutput (f := f) p (a :: xs)).length + 4 = recordTime h p a +
        (recordsTime h p xs + (ep.encode p).length + ((childOutput h p a).reverse ++ acc).length +
          (flatOutput (f := f) p xs).length + 4) := by
      simp only [recordsTime, flatOutput, List.flatMap_cons, List.length_append,
        List.length_reverse, childOutput_length]
      omega
    rw [he, run_add h (record_iteration h p a xs acc out), ih]
    simp only [List.map_append, List.map_reverse, List.reverse_append, List.reverse_reverse,
      childOutput_decode, flatOutput, List.flatMap_cons, List.append_assoc]

def inputWord (p : P) (xs : List A) : List (RawSymbol (ep := ep) (ea := ea)) :=
  (ep.encode p).map .left ++ .sep :: rawRecords (ep := ep) (ea := ea) xs

noncomputable def runningTime (p : P) (xs : List A) : ℕ :=
  recordsTime h p xs + 2 * (ep.encode p).length + (flatOutput (f := f) p xs).length + 5

theorem program_run (p : P) (xs : List A) :
    run h (runningTime h p xs)
      (cfg h .parameter (initial h) (emptyChild h) (inputWord p xs) [] [] [] [] []) =
      some (halted h (flatOutput (f := f) p xs)) := by
  have hp := parameter_run h h.tm.initialState (none, none) (emptyChild h) (ep.encode p)
    (rawRecords (ep := ep) (ea := ea) xs) [] [] [] [] []
  simp only [List.append_nil] at hp
  change run h ((ep.encode p).length + 1)
    (cfg h .parameter (initial h) (emptyChild h) (inputWord p xs) [] [] [] [] []) =
    some (cfg h .record (initial h) (emptyChild h) (rawRecords xs) (parameterWord h p) [] [] [] []) at hp
  rw [show runningTime h p xs = ((ep.encode p).length + 1) +
    (recordsTime h p xs + (ep.encode p).length + ([] : List (OutLetter h)).length +
      (flatOutput (f := f) p xs).length + 4) by
      dsimp [runningTime]; omega,
    run_add h hp]
  simpa only [List.map_nil, List.reverse_nil, List.nil_append, List.append_nil] using records_run h p xs [] []

end Inhabited
end ProteinFolding.TM2ListMap
