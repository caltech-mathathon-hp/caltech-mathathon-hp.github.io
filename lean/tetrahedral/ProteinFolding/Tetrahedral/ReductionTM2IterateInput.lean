import ProteinFolding.Tetrahedral.ReductionTM2IterateStacks

namespace ProteinFolding.Tetrahedral.ReductionTM2.Iterate

open Computability Turing TM2
noncomputable section
variable {A : Type} {ea : FinEncoding A} {f : A → A}
variable (h : TM2ComputableInPolyTime ea ea f) [Inhabited ea.Γ]

theorem readState_cons (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea))
    (a : ea.Γ) (u : List (InputSymbol (ea := ea))) :
    step (program h) (cfg h (.inr .readState) S {d with input := .left a :: u}) =
      some (cfg h (.inr .readState) S {d with input := u, buffer := a :: d.buffer}) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents,
    TM2Embedding.joinStacks, extraContents, leftHead]
  change Function.update (Function.update (contents h S {d with input := .left a :: u}) (.inr .input) u)
    (.inr .buffer) (a :: d.buffer) = contents h S {d with input := u, buffer := a :: d.buffer}
  rw [update_input, update_buffer]

theorem readState_sep (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea)) (u : List (InputSymbol (ea := ea))) :
    step (program h) (cfg h (.inr .readState) S {d with input := .sep :: u}) =
      some (cfg h (.inr .readCount) S {d with input := u}) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents,
    TM2Embedding.joinStacks, extraContents, leftHead]
  exact update_input h S _ _

theorem readState_run (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea))
    (w : List ea.Γ) (u : List (InputSymbol (ea := ea))) :
    run h (w.length + 1) (cfg h (.inr .readState) S {d with input := w.map .left ++ .sep :: u}) =
      some (cfg h (.inr .readCount) S {d with input := u, buffer := w.reverse ++ d.buffer}) := by
  induction w generalizing d with
  | nil => simpa only [List.length_nil, Nat.zero_add, List.map_nil, List.nil_append,
      List.reverse_nil, run, Function.iterate_one, Option.bind_some] using readState_sep h S d u
  | cons a w ih =>
    simp only [List.length_cons, List.map_cons, List.cons_append]
    rw [run_step h (readState_cons h S d a _)]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih {d with buffer := a :: d.buffer}

theorem readCount_cons (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea)) (u : List (InputSymbol (ea := ea))) :
    step (program h) (cfg h (.inr .readCount) S {d with input := .right true :: u}) =
      some (cfg h (.inr .readCount) S {d with input := u, remaining := d.remaining + 1}) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents,
    TM2Embedding.joinStacks, extraContents]
  change Function.update (Function.update (contents h S {d with input := .right true :: u}) (.inr .input) u)
    (.inr .remaining) (List.replicate (d.remaining + 1) ()) = contents h S {d with input := u, remaining := d.remaining + 1}
  rw [update_input, update_remaining]

theorem readCount_nil (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea)) :
    step (program h) (cfg h (.inr .readCount) S {d with input := []}) =
      some (cfg h (.inr .loop) S {d with input := []}) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents,
    TM2Embedding.joinStacks, extraContents]

theorem readCount_run (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea)) (n : ℕ) :
    run h (n + 1) (cfg h (.inr .readCount) S {d with input := (unaryEncodeNat n).map .right}) =
      some (cfg h (.inr .loop) S {d with input := [], remaining := d.remaining + n}) := by
  induction n generalizing d with
  | zero => simpa only [unaryEncodeNat, List.map_nil, Nat.add_zero, run, Function.iterate_one,
      Option.bind_some] using readCount_nil h S d
  | succ n ih =>
    simp only [unaryEncodeNat, List.map_cons]
    rw [run_step h (readCount_cons h S d _)]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih {d with remaining := d.remaining + 1}

def loopData (a : A) (n : ℕ) : Data (ea := ea) := ⟨[], (ea.encode a).reverse, n, []⟩

theorem input_run (a : A) (n : ℕ) :
    run h ((ea.encode a).length + n + 2)
      (cfg h (.inr .readState) (emptyStacks h) ⟨(pairEncoding ea unaryFinEncodingNat).encode (a, n), [], 0, []⟩) =
      some (cfg h (.inr .loop) (emptyStacks h) (loopData (ea := ea) a n)) := by
  rw [show (ea.encode a).length + n + 2 = ((ea.encode a).length + 1) + (n + 1) by omega]
  change run h (((ea.encode a).length + 1) + (n + 1))
    (cfg h (.inr .readState) (emptyStacks h)
      {({input := [], buffer := [], remaining := 0, output := []} : Data (ea := ea)) with
        input := (ea.encode a).map .left ++ .sep :: (unaryEncodeNat n).map .right}) = _
  rw [run_add h (readState_run h _ _ (ea.encode a) ((unaryEncodeNat n).map .right))]
  simpa [loopData, unaryEncodeNat] using readCount_run h (emptyStacks h)
    (⟨[], (ea.encode a).reverse, 0, []⟩ : Data (ea := ea)) n

end
end ProteinFolding.Tetrahedral.ReductionTM2.Iterate
