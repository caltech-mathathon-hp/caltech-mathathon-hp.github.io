import ProteinFolding.Common.TM2BoundedSearchMachine

/-! Stack identities and faithful lifting of the supplied actual predicate
machine into the bounded-search controller. -/

namespace ProteinFolding.TM2BoundedSearch

open Computability Turing TM2
noncomputable section

variable {A : Type} {ea : FinEncoding A} {test : A × ℕ → Bool}
variable (hp : TM2ComputableInPolyTime (pairEncoding ea unaryFinEncodingNat) finEncodingBoolBool test)

theorem update_active (S : ∀ k, List ((savedPredicate hp).tm.Γ k)) (d : Data (ea := ea))
    (k : (savedPredicate hp).tm.K) (w : List ((savedPredicate hp).tm.Γ k)) :
    Function.update (contents hp S d) (.inl k) w = contents hp (Function.update S k w) d :=
  TM2Embedding.joinStacks_update S (auxContents d) k w

theorem update_input (S : ∀ k, List ((savedPredicate hp).tm.Γ k)) (d : Data (ea := ea))
    (w : List (InputSymbol (ea := ea))) :
    Function.update (contents hp S d) (.inr .input) w = contents hp S {d with input := w} := by
  funext k
  cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, auxContents]

theorem update_buffer (S : ∀ k, List ((savedPredicate hp).tm.Γ k)) (d : Data (ea := ea))
    (w : List (InputSymbol (ea := ea))) :
    Function.update (contents hp S d) (.inr .buffer) w = contents hp S {d with buffer := w} := by
  funext k
  cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, auxContents]

theorem update_current (S : ∀ k, List ((savedPredicate hp).tm.Γ k)) (d : Data (ea := ea)) (n : ℕ) :
    Function.update (contents hp S d) (.inr .current) (List.replicate n ()) =
      contents hp S {d with current := n} := by
  funext k
  cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, auxContents]

theorem update_remaining (S : ∀ k, List ((savedPredicate hp).tm.Γ k)) (d : Data (ea := ea)) (n : ℕ) :
    Function.update (contents hp S d) (.inr .remaining) (List.replicate n ()) =
      contents hp S {d with remaining := n} := by
  funext k
  cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, auxContents]

theorem update_output (S : ∀ k, List ((savedPredicate hp).tm.Γ k)) (d : Data (ea := ea)) (w : List Bool) :
    Function.update (contents hp S d) (.inr .output) w = contents hp S {d with output := w} := by
  funext k
  cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, auxContents]

theorem oneStack_self (k : (savedPredicate hp).tm.K) (w : List ((savedPredicate hp).tm.Γ k)) :
    oneStack hp k w k = w := by simp [oneStack]

theorem oneStack_empty (k : (savedPredicate hp).tm.K) :
    oneStack hp k [] = emptyStacks hp := by
  funext j
  by_cases h : j = k
  · subst j; simp [oneStack, emptyStacks]
  · simp [oneStack, emptyStacks, h]

theorem oneStack_update (k : (savedPredicate hp).tm.K) (w w' : List ((savedPredicate hp).tm.Γ k)) :
    Function.update (oneStack hp k w) k w' = oneStack hp k w' := by
  simp [oneStack, Function.update_idem]

theorem initList_stacks (w : List ((savedPredicate hp).tm.Γ (savedPredicate hp).tm.k₀)) :
    (initList (savedPredicate hp).tm w).stk = oneStack hp (savedPredicate hp).tm.k₀ w := by
  funext k
  by_cases h : k = (savedPredicate hp).tm.k₀
  · subst k; simp [initList, oneStack]
  · simp [initList, oneStack, emptyStacks, h]

theorem haltList_stacks (w : List ((savedPredicate hp).tm.Γ (savedPredicate hp).tm.k₁)) :
    (haltList (savedPredicate hp).tm w).stk = oneStack hp (savedPredicate hp).tm.k₁ w := by
  funext k
  by_cases h : k = (savedPredicate hp).tm.k₁
  · subst k; simp [haltList, oneStack]
  · simp [haltList, oneStack, emptyStacks, h]

def inputWord (x : A) (j : ℕ) : List (InputSymbol (ea := ea)) :=
  (pairEncoding ea unaryFinEncodingNat).encode (x, j)

def callInput (x : A) (j : ℕ) : List ((savedPredicate hp).tm.Γ (savedPredicate hp).tm.k₀) :=
  (inputWord (ea := ea) x j).map (savedPredicate hp).inputAlphabet.symm

def outputLeft (s : InputSymbol (ea := ea)) : (savedPredicate hp).tm.Γ (savedPredicate hp).tm.k₁ :=
  (savedPredicate hp).outputAlphabet.symm (.left s)

def outputSeparator : (savedPredicate hp).tm.Γ (savedPredicate hp).tm.k₁ :=
  (savedPredicate hp).outputAlphabet.symm .sep

def outputBool (b : Bool) : (savedPredicate hp).tm.Γ (savedPredicate hp).tm.k₁ :=
  (savedPredicate hp).outputAlphabet.symm (.right b)

def callOutput (u : List (InputSymbol (ea := ea))) (b : Bool) :
    List ((savedPredicate hp).tm.Γ (savedPredicate hp).tm.k₁) :=
  u.map (outputLeft hp) ++ [outputSeparator hp, outputBool hp b]

theorem callOutput_encoding (x : A) (j : ℕ) (b : Bool) :
    (((savedEncoding (ea := ea)).encode ((x, j), b)).map (savedPredicate hp).outputAlphabet.symm) =
      callOutput hp (inputWord (ea := ea) x j) b := by
  simp [savedEncoding, pairEncoding, finEncodingBoolBool, encodeBool, callOutput,
    inputWord, outputLeft, outputSeparator, outputBool, List.map_append, List.map_map, Function.comp_def]

theorem predicate_run (x : A) (j : ℕ) (d : Data (ea := ea)) :
    run hp ((savedPredicate hp).outputsFun (x, j)).steps
      (cfg hp (.inl (savedPredicate hp).tm.main)
        (oneStack hp (savedPredicate hp).tm.k₀ (callInput hp x j)) d) =
      some (cfg hp (.inr .readWord)
        (oneStack hp (savedPredicate hp).tm.k₁ (callOutput hp (inputWord (ea := ea) x j) (test (x, j)))) d) := by
  let hs := (savedPredicate hp).outputsFun (x, j)
  have hrun := hs.evals_in_steps
  change (fun u : Option (savedPredicate hp).tm.Cfg => u.bind (step (savedPredicate hp).tm.m))^[hs.steps]
      (some (initList (savedPredicate hp).tm (callInput hp x j))) =
      some (haltList (savedPredicate hp).tm
        (((savedEncoding (ea := ea)).encode ((x, j), test (x, j))).map (savedPredicate hp).outputAlphabet.symm)) at hrun
  rw [callOutput_encoding] at hrun
  have hlift := TM2Embedding.simulate_run (step (savedPredicate hp).tm.m) (step (program hp))
    (TM2Embedding.embedCfg Sum.inl (some (.inr Phase.readWord)) (none, false) (auxContents d))
    (fun a b hh => TM2Embedding.step_liftStmt Sum.inl (some (.inr Phase.readWord))
      (savedPredicate hp).tm.m (program hp) (fun _ => rfl) (none, false) (auxContents d) a b hh)
    hs.steps _ _ hrun
  have hi : TM2Embedding.embedCfg Sum.inl (some (.inr Phase.readWord)) (none, false) (auxContents d)
      (initList (savedPredicate hp).tm (callInput hp x j)) =
      cfg hp (.inl (savedPredicate hp).tm.main) (oneStack hp (savedPredicate hp).tm.k₀ (callInput hp x j)) d := by
    simp only [TM2Embedding.embedCfg, initList, cfg, initialState, contents, Option.elim_some]
    rw [← initList_stacks]
    rfl
  have ho : TM2Embedding.embedCfg Sum.inl (some (.inr Phase.readWord)) (none, false) (auxContents d)
      (haltList (savedPredicate hp).tm (callOutput hp (inputWord (ea := ea) x j) (test (x, j)))) =
      cfg hp (.inr .readWord) (oneStack hp (savedPredicate hp).tm.k₁
        (callOutput hp (inputWord (ea := ea) x j) (test (x, j)))) d := by
    simp only [TM2Embedding.embedCfg, haltList, cfg, initialState, contents, Option.elim_none]
    rw [← haltList_stacks]
    rfl
  simpa only [run, hi, ho] using hlift

end
end ProteinFolding.TM2BoundedSearch
