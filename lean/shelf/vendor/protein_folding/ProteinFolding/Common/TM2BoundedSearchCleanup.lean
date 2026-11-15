import ProteinFolding.Common.TM2BoundedSearchStacks

/-! Complete cleanup for the bounded-search controller: discard the unused
search budget and saved argument, serialize the unary answer, restore the
initial state, and leave every other stack empty. -/

namespace ProteinFolding.TM2BoundedSearch

open Computability Turing TM2
noncomputable section

variable {A : Type} {ea : FinEncoding A} {test : A × ℕ → Bool}
variable (hp : TM2ComputableInPolyTime (pairEncoding ea unaryFinEncodingNat) finEncodingBoolBool test)

def halted (o : List Bool) : Cfg (Alphabet hp) (Label hp) (State hp) :=
  ⟨none, initialState hp, contents hp (emptyStacks hp) ⟨[], [], 0, 0, o⟩⟩

theorem drainRemaining_succ (u : List (InputSymbol (ea := ea))) (j r : ℕ) :
    step (program hp) (cfg hp (.inr .drainRemaining) (emptyStacks hp) ⟨[], u, j, r + 1, []⟩) =
      some (cfg hp (.inr .drainRemaining) (emptyStacks hp) ⟨[], u, j, r, []⟩) := by
  simp [cfg, program, step, stepAux, clearControl, initialState, contents,
    TM2Embedding.joinStacks, auxContents, List.replicate_succ]
  exact update_remaining hp (emptyStacks hp) ⟨[], u, j, r + 1, []⟩ r

theorem drainRemaining_zero (u : List (InputSymbol (ea := ea))) (j : ℕ) :
    step (program hp) (cfg hp (.inr .drainRemaining) (emptyStacks hp) ⟨[], u, j, 0, []⟩) =
      some (cfg hp (.inr .drainBuffer) (emptyStacks hp) ⟨[], u, j, 0, []⟩) := by
  simp [cfg, program, step, stepAux, clearControl, initialState, contents,
    TM2Embedding.joinStacks, auxContents]

theorem drainBuffer_cons (a : InputSymbol (ea := ea)) (u : List (InputSymbol (ea := ea))) (j : ℕ) :
    step (program hp) (cfg hp (.inr .drainBuffer) (emptyStacks hp) ⟨[], a :: u, j, 0, []⟩) =
      some (cfg hp (.inr .drainBuffer) (emptyStacks hp) ⟨[], u, j, 0, []⟩) := by
  simp [cfg, program, step, stepAux, clearControl, initialState, contents,
    TM2Embedding.joinStacks, auxContents]
  exact update_buffer hp (emptyStacks hp) ⟨[], a :: u, j, 0, []⟩ u

theorem drainBuffer_nil (j : ℕ) :
    step (program hp) (cfg hp (.inr .drainBuffer) (emptyStacks hp) ⟨[], [], j, 0, []⟩) =
      some (cfg hp (.inr .emit) (emptyStacks hp) ⟨[], [], j, 0, []⟩) := by
  simp [cfg, program, step, stepAux, clearControl, initialState, contents,
    TM2Embedding.joinStacks, auxContents]

theorem emit_succ (j : ℕ) (o : List Bool) :
    step (program hp) (cfg hp (.inr .emit) (emptyStacks hp) ⟨[], [], j + 1, 0, o⟩) =
      some (cfg hp (.inr .emit) (emptyStacks hp) ⟨[], [], j, 0, true :: o⟩) := by
  simp [cfg, program, step, stepAux, clearControl, initialState, contents,
    TM2Embedding.joinStacks, auxContents, List.replicate_succ]
  change Function.update
    (Function.update (contents hp (emptyStacks hp) ⟨[], [], j + 1, 0, o⟩)
      (.inr .current) (List.replicate j ())) (.inr .output) (true :: o) = _
  rw [update_current, update_output]
  rfl

theorem emit_zero (o : List Bool) :
    step (program hp) (cfg hp (.inr .emit) (emptyStacks hp) ⟨[], [], 0, 0, o⟩) =
      some (halted hp o) := by
  simp [cfg, program, halted, step, stepAux, initialState, contents,
    TM2Embedding.joinStacks, auxContents]

theorem drainRemaining_run (u : List (InputSymbol (ea := ea))) (j r : ℕ) :
    run hp (r + 1) (cfg hp (.inr .drainRemaining) (emptyStacks hp) ⟨[], u, j, r, []⟩) =
      some (cfg hp (.inr .drainBuffer) (emptyStacks hp) ⟨[], u, j, 0, []⟩) := by
  induction r with
  | zero => simpa only [run, Function.iterate_one, Option.bind_some] using drainRemaining_zero hp u j
  | succ r ih => rw [run_step hp (drainRemaining_succ hp u j r), ih]

theorem drainBuffer_run (u : List (InputSymbol (ea := ea))) (j : ℕ) :
    run hp (u.length + 1) (cfg hp (.inr .drainBuffer) (emptyStacks hp) ⟨[], u, j, 0, []⟩) =
      some (cfg hp (.inr .emit) (emptyStacks hp) ⟨[], [], j, 0, []⟩) := by
  induction u with
  | nil => simpa only [run, Function.iterate_one, Option.bind_some] using drainBuffer_nil hp j
  | cons a u ih => rw [List.length_cons, run_step hp (drainBuffer_cons hp a u j), ih]

theorem emit_run (j : ℕ) (o : List Bool) :
    run hp (j + 1) (cfg hp (.inr .emit) (emptyStacks hp) ⟨[], [], j, 0, o⟩) =
      some (halted hp (unaryEncodeNat j ++ o)) := by
  induction j generalizing o with
  | zero => simpa only [run, Function.iterate_one, Option.bind_some, unaryEncodeNat,
      List.nil_append] using emit_zero hp o
  | succ j ih =>
    rw [run_step hp (emit_succ hp j o), ih]
    have he : unaryEncodeNat j ++ true :: o = unaryEncodeNat (j + 1) ++ o := by
      clear ih
      induction j with
      | zero => rfl
      | succ j hj => simpa only [unaryEncodeNat, List.cons_append] using congrArg (true :: ·) hj
    rw [he]

theorem cleanup_buffer_run (u : List (InputSymbol (ea := ea))) (j : ℕ) :
    run hp (u.length + j + 2)
      (cfg hp (.inr .drainBuffer) (emptyStacks hp) ⟨[], u, j, 0, []⟩) =
      some (halted hp (unaryEncodeNat j)) := by
  rw [show u.length + j + 2 = (u.length + 1) + (j + 1) by omega,
    run_add hp (drainBuffer_run hp u j), emit_run]
  simp only [List.append_nil]

theorem cleanup_run (u : List (InputSymbol (ea := ea))) (j r : ℕ) :
    run hp (r + u.length + j + 3)
      (cfg hp (.inr .drainRemaining) (emptyStacks hp) ⟨[], u, j, r, []⟩) =
      some (halted hp (unaryEncodeNat j)) := by
  rw [show r + u.length + j + 3 = (r + 1) + (u.length + j + 2) by omega,
    run_add hp (drainRemaining_run hp u j r)]
  exact cleanup_buffer_run hp u j

end
end ProteinFolding.TM2BoundedSearch
