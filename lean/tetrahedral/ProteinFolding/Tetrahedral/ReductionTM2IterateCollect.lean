import ProteinFolding.Tetrahedral.ReductionTM2IterateStacks

namespace ProteinFolding.Tetrahedral.ReductionTM2.Iterate

open Computability Turing TM2
noncomputable section
variable {A : Type} {ea : FinEncoding A} {f : A → A}
variable (h : TM2ComputableInPolyTime ea ea f) [Inhabited ea.Γ]

theorem collect_cons (d : Data (ea := ea)) (a : h.tm.Γ h.tm.k₁) (w : List (h.tm.Γ h.tm.k₁)) :
    step (program h) (cfg h (.inr .collect) (oneStack h h.tm.k₁ (a :: w)) d) =
      some (cfg h (.inr .collect) (oneStack h h.tm.k₁ w) {d with buffer := h.outputAlphabet a :: d.buffer}) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents,
    TM2Embedding.joinStacks, extraContents, oneStack_self]
  change Function.update
    (Function.update (contents h (oneStack h h.tm.k₁ (a :: w)) d) (.inl h.tm.k₁) w)
    (.inr .buffer) (h.outputAlphabet a :: d.buffer) =
      contents h (oneStack h h.tm.k₁ w) {d with buffer := h.outputAlphabet a :: d.buffer}
  rw [update_active, oneStack_update, update_buffer]

theorem collect_nil (d : Data (ea := ea)) :
    step (program h) (cfg h (.inr .collect) (emptyStacks h) d) =
      some (cfg h (.inr .loop) (emptyStacks h) d) := by
  simp [cfg, initialState, program, step, stepAux, contents,
    TM2Embedding.joinStacks, extraContents, emptyStacks]

theorem collect_run (d : Data (ea := ea)) (w : List (h.tm.Γ h.tm.k₁)) :
    run h (w.length + 1) (cfg h (.inr .collect) (oneStack h h.tm.k₁ w) d) =
      some (cfg h (.inr .loop) (emptyStacks h) {d with buffer := (w.map h.outputAlphabet).reverse ++ d.buffer}) := by
  induction w generalizing d with
  | nil => simpa only [List.length_nil, Nat.zero_add, List.map_nil, List.reverse_nil, List.nil_append,
      oneStack_empty, run, Function.iterate_one, Option.bind_some] using collect_nil h d
  | cons a w ih =>
    simp only [List.length_cons]
    rw [run_step h (collect_cons h d a w)]
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using
      ih {d with buffer := h.outputAlphabet a :: d.buffer}

theorem collect_call_run (d : Data (ea := ea)) (a : A) :
    run h ((ea.encode a).length + 1) (cfg h (.inr .collect) (oneStack h h.tm.k₁ (callOutput h a)) {d with buffer := []}) =
      some (cfg h (.inr .loop) (emptyStacks h) {d with buffer := (ea.encode a).reverse}) := by
  simpa only [callOutput, List.length_map, List.map_map, Function.comp_def, Equiv.apply_symm_apply,
    List.map_id, List.map_id', List.append_nil] using collect_run h {d with buffer := []} (callOutput h a)

end
end ProteinFolding.Tetrahedral.ReductionTM2.Iterate
