import ProteinFolding.Common.TM2BoundedSearchStacks

/-! Reading the predicate result while recovering its saved input word.
Each saved symbol is pushed into the reverse-order buffer. The Boolean is
consumed and all predicate-machine stacks are empty before the next round.
-/

namespace ProteinFolding.TM2BoundedSearch

open Computability Turing TM2
noncomputable section

variable {A : Type} {ea : FinEncoding A} {test : A × ℕ → Bool}
variable (hp : TM2ComputableInPolyTime (pairEncoding ea unaryFinEncodingNat) finEncodingBoolBool test)

theorem readWord_cons (d : Data (ea := ea)) (a : InputSymbol (ea := ea))
    (u : List (InputSymbol (ea := ea))) (b : Bool) :
    step (program hp)
      (cfg hp (.inr .readWord) (oneStack hp (savedPredicate hp).tm.k₁ (callOutput hp (a :: u) b)) d) =
      some (cfg hp (.inr .readWord) (oneStack hp (savedPredicate hp).tm.k₁ (callOutput hp u b))
        {d with buffer := a :: d.buffer}) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents,
    TM2Embedding.joinStacks, oneStack_self, auxContents, callOutput, savedHead, outputLeft]
  change Function.update
    (Function.update (contents hp (oneStack hp (savedPredicate hp).tm.k₁ (callOutput hp (a :: u) b)) d)
      (.inl (savedPredicate hp).tm.k₁) (callOutput hp u b)) (.inr .buffer) (a :: d.buffer) =
        contents hp (oneStack hp (savedPredicate hp).tm.k₁ (callOutput hp u b)) {d with buffer := a :: d.buffer}
  rw [update_active, oneStack_update, update_buffer]

theorem readWord_separator (d : Data (ea := ea)) (b : Bool) :
    step (program hp)
      (cfg hp (.inr .readWord) (oneStack hp (savedPredicate hp).tm.k₁ (callOutput hp [] b)) d) =
      some (cfg hp (.inr .readBool) (oneStack hp (savedPredicate hp).tm.k₁ [outputBool hp b]) d) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents,
    TM2Embedding.joinStacks, oneStack_self, auxContents, callOutput, savedHead, outputSeparator]
  change Function.update (contents hp (oneStack hp (savedPredicate hp).tm.k₁ (callOutput hp [] b)) d)
    (.inl (savedPredicate hp).tm.k₁) [outputBool hp b] =
      contents hp (oneStack hp (savedPredicate hp).tm.k₁ [outputBool hp b]) d
  rw [update_active, oneStack_update]

theorem readWord_run (d : Data (ea := ea)) (u : List (InputSymbol (ea := ea))) (b : Bool) :
    run hp (u.length + 1)
      (cfg hp (.inr .readWord) (oneStack hp (savedPredicate hp).tm.k₁ (callOutput hp u b)) d) =
      some (cfg hp (.inr .readBool) (oneStack hp (savedPredicate hp).tm.k₁ [outputBool hp b])
        {d with buffer := u.reverse ++ d.buffer}) := by
  induction u generalizing d with
  | nil => simpa only [run, List.length_nil, Nat.zero_add, Function.iterate_one, Option.bind_some,
      List.reverse_nil, List.nil_append] using readWord_separator hp d b
  | cons a u ih =>
    rw [List.length_cons, run_step hp (readWord_cons hp d a u b)]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
      ih {d with buffer := a :: d.buffer}

theorem readBool_true (d : Data (ea := ea)) :
    step (program hp)
      (cfg hp (.inr .readBool) (oneStack hp (savedPredicate hp).tm.k₁ [outputBool hp true]) d) =
      some (cfg hp (.inr .drainRemaining) (emptyStacks hp) d) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents,
    TM2Embedding.joinStacks, oneStack_self, auxContents, savedAnswer, outputBool]
  change Function.update (contents hp (oneStack hp (savedPredicate hp).tm.k₁ [outputBool hp true]) d)
    (.inl (savedPredicate hp).tm.k₁) [] = contents hp (emptyStacks hp) d
  rw [update_active, oneStack_update, oneStack_empty]

theorem readBool_false (d : Data (ea := ea)) (r : ℕ) :
    step (program hp)
      (cfg hp (.inr .readBool) (oneStack hp (savedPredicate hp).tm.k₁ [outputBool hp false])
        {d with remaining := r + 1}) =
      some (cfg hp (.inr .loop) (emptyStacks hp)
        {d with remaining := r, current := d.current + 1, buffer := .right true :: d.buffer}) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents,
    TM2Embedding.joinStacks, oneStack_self, auxContents, savedAnswer, outputBool, List.replicate_succ]
  change Function.update
    (Function.update
      (Function.update
        (Function.update (contents hp (oneStack hp (savedPredicate hp).tm.k₁ [outputBool hp false])
          {d with remaining := r + 1}) (.inl (savedPredicate hp).tm.k₁) [])
        (.inr .remaining) (List.replicate r ())) (.inr .current) (List.replicate (d.current + 1) ()))
    (.inr .buffer) (.right true :: d.buffer) =
      contents hp (emptyStacks hp)
        {d with remaining := r, current := d.current + 1, buffer := .right true :: d.buffer}
  rw [update_active, oneStack_update, oneStack_empty, update_remaining, update_current, update_buffer]

end
end ProteinFolding.TM2BoundedSearch
