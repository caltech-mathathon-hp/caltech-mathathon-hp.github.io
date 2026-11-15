import ProteinFolding.Common.TM2BoundedSearchStacks

/-! The bounded-search frontend stores the original encoded argument and a
separator in reverse order, then reads the unary bound into its remaining
counter. The input word and temporary finite registers are cleared. -/

namespace ProteinFolding.TM2BoundedSearch

open Computability Turing TM2
noncomputable section

variable {A : Type} {ea : FinEncoding A} {test : A × ℕ → Bool}
variable (hp : TM2ComputableInPolyTime (pairEncoding ea unaryFinEncodingNat) finEncodingBoolBool test)

theorem scanX_cons (S : ∀ k, List ((savedPredicate hp).tm.Γ k)) (d : Data (ea := ea))
    (a : ea.Γ) (u : List (InputSymbol (ea := ea))) :
    step (program hp) (cfg hp (.inr .scanX) S {d with input := .left a :: u}) =
      some (cfg hp (.inr .scanX) S {d with input := u, buffer := .left a :: d.buffer}) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents,
    TM2Embedding.joinStacks, auxContents, leftHead]
  change Function.update
    (Function.update (contents hp S {d with input := .left a :: u}) (.inr .input) u)
    (.inr .buffer) (.left a :: d.buffer) = contents hp S {d with input := u, buffer := .left a :: d.buffer}
  rw [update_input, update_buffer]

theorem scanX_sep (S : ∀ k, List ((savedPredicate hp).tm.Γ k)) (d : Data (ea := ea))
    (u : List (InputSymbol (ea := ea))) :
    step (program hp) (cfg hp (.inr .scanX) S {d with input := .sep :: u}) =
      some (cfg hp (.inr .scanRemaining) S {d with input := u, buffer := .sep :: d.buffer}) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents,
    TM2Embedding.joinStacks, auxContents, leftHead]
  change Function.update
    (Function.update (contents hp S {d with input := .sep :: u}) (.inr .input) u)
    (.inr .buffer) (.sep :: d.buffer) = contents hp S {d with input := u, buffer := .sep :: d.buffer}
  rw [update_input, update_buffer]

theorem scanX_run (S : ∀ k, List ((savedPredicate hp).tm.Γ k)) (d : Data (ea := ea))
    (w : List ea.Γ) (u : List (InputSymbol (ea := ea))) :
    run hp (w.length + 1) (cfg hp (.inr .scanX) S {d with input := w.map .left ++ .sep :: u}) =
      some (cfg hp (.inr .scanRemaining) S
        {d with input := u, buffer := .sep :: ((w.map .left).reverse ++ d.buffer)}) := by
  induction w generalizing d with
  | nil => simpa only [List.length_nil, Nat.zero_add, List.map_nil, List.nil_append,
      List.reverse_nil, run, Function.iterate_one, Option.bind_some] using scanX_sep hp S d u
  | cons a w ih =>
    simp only [List.length_cons, List.map_cons, List.cons_append]
    rw [run_step hp (scanX_cons hp S d a _)]
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using
      ih {d with buffer := .left a :: d.buffer}

theorem scanRemaining_cons (S : ∀ k, List ((savedPredicate hp).tm.Γ k)) (d : Data (ea := ea))
    (u : List (InputSymbol (ea := ea))) :
    step (program hp) (cfg hp (.inr .scanRemaining) S {d with input := .right true :: u}) =
      some (cfg hp (.inr .scanRemaining) S {d with input := u, remaining := d.remaining + 1}) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents, TM2Embedding.joinStacks, auxContents]
  change Function.update
    (Function.update (contents hp S {d with input := .right true :: u}) (.inr .input) u)
    (.inr .remaining) (List.replicate (d.remaining + 1) ()) =
      contents hp S {d with input := u, remaining := d.remaining + 1}
  rw [update_input, update_remaining]

theorem scanRemaining_nil (S : ∀ k, List ((savedPredicate hp).tm.Γ k)) (d : Data (ea := ea)) :
    step (program hp) (cfg hp (.inr .scanRemaining) S {d with input := []}) =
      some (cfg hp (.inr .loop) S {d with input := []}) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents, TM2Embedding.joinStacks, auxContents]

theorem scanRemaining_run (S : ∀ k, List ((savedPredicate hp).tm.Γ k)) (d : Data (ea := ea)) (n : ℕ) :
    run hp (n + 1) (cfg hp (.inr .scanRemaining) S {d with input := (unaryEncodeNat n).map .right}) =
      some (cfg hp (.inr .loop) S {d with input := [], remaining := d.remaining + n}) := by
  induction n generalizing d with
  | zero => simpa only [unaryEncodeNat, List.map_nil, Nat.add_zero, run, Function.iterate_one,
      Option.bind_some] using scanRemaining_nil hp S d
  | succ n ih =>
    simp only [unaryEncodeNat, List.map_cons]
    rw [run_step hp (scanRemaining_cons hp S d _)]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih {d with remaining := d.remaining + 1}

def loopData (x : A) (j r : ℕ) : Data (ea := ea) :=
  ⟨[], (inputWord (ea := ea) x j).reverse, j, r, []⟩

theorem input_run (x : A) (k : ℕ) :
    run hp ((ea.encode x).length + k + 2)
      (cfg hp (.inr .scanX) (emptyStacks hp)
        ⟨(pairEncoding ea unaryFinEncodingNat).encode (x, k), [], 0, 0, []⟩) =
      some (cfg hp (.inr .loop) (emptyStacks hp) (loopData x 0 k)) := by
  rw [show (ea.encode x).length + k + 2 = ((ea.encode x).length + 1) + (k + 1) by omega]
  change run hp (((ea.encode x).length + 1) + (k + 1))
      (cfg hp (.inr .scanX) (emptyStacks hp)
        {({ input := [], buffer := [], current := 0, remaining := 0, output := [] } : Data (ea := ea)) with
          input := (ea.encode x).map .left ++ .sep :: (unaryEncodeNat k).map .right}) = _
  rw [run_add hp (scanX_run hp _ _ (ea.encode x) ((unaryEncodeNat k).map .right))]
  simpa [loopData, inputWord, pairEncoding, unaryFinEncodingNat, unaryEncodeNat] using
    scanRemaining_run hp (emptyStacks hp)
      (⟨[], .sep :: ((ea.encode x).map .left).reverse, 0, 0, []⟩ : Data (ea := ea)) k

end
end ProteinFolding.TM2BoundedSearch
