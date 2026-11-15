import ProteinFolding.Tetrahedral.ReductionTM2IterateInput
import ProteinFolding.Tetrahedral.ReductionTM2IterateTransfer
import ProteinFolding.Tetrahedral.ReductionTM2IterateCollect

namespace ProteinFolding.Tetrahedral.ReductionTM2.Iterate

open Computability Turing TM2
noncomputable section
variable {A : Type} {ea : FinEncoding A} {f : A → A}
variable (h : TM2ComputableInPolyTime ea ea f) [Inhabited ea.Γ]

theorem loop_positive (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea)) (n : ℕ) :
    step (program h) (cfg h (.inr .loop) S {d with remaining := n + 1}) =
      some (cfg h (.inr .prepare) S {d with remaining := n}) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents,
    TM2Embedding.joinStacks, extraContents, List.replicate_succ]
  exact update_remaining h S _ n

theorem loop_zero (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea)) :
    step (program h) (cfg h (.inr .loop) S {d with remaining := 0}) =
      some (cfg h (.inr .finish) S {d with remaining := 0}) := by
  simp [cfg, initialState, program, clearControl, step, stepAux, contents,
    TM2Embedding.joinStacks, extraContents]

theorem prepare_call_run (a : A) (n : ℕ) :
    run h ((ea.encode a).length + 1) (cfg h (.inr .prepare) (emptyStacks h) (loopData (ea := ea) a n)) =
      some (cfg h (.inl h.tm.main) (oneStack h h.tm.k₀ (callInput h a))
        {(loopData (ea := ea) a n) with buffer := []}) := by
  simpa only [List.length_reverse, oneStack_empty, List.map_reverse, List.reverse_reverse,
    List.append_nil, loopData, callInput] using prepare_run h (loopData (ea := ea) a n) (ea.encode a).reverse []

def roundSteps (a : A) : ℕ := (ea.encode a).length + (h.outputsFun a).steps + (ea.encode (f a)).length + 3

theorem round_run (a : A) (n : ℕ) :
    run h (roundSteps h a) (cfg h (.inr .loop) (emptyStacks h) (loopData (ea := ea) a (n + 1))) =
      some (cfg h (.inr .loop) (emptyStacks h) (loopData (ea := ea) (f a) n)) := by
  rw [show roundSteps h a =
      (((ea.encode a).length + 1) + ((h.outputsFun a).steps + ((ea.encode (f a)).length + 1))) + 1 by
      unfold roundSteps; omega]
  have hl : step (program h) (cfg h (.inr .loop) (emptyStacks h) (loopData (ea := ea) a (n + 1))) =
      some (cfg h (.inr .prepare) (emptyStacks h) (loopData (ea := ea) a n)) := by
    simpa only [loopData] using loop_positive h (emptyStacks h) (loopData (ea := ea) a n) n
  rw [run_step h hl]
  rw [run_add h (prepare_call_run h a n)]
  rw [run_add h (child_run h a {(loopData (ea := ea) a n) with buffer := []})]
  simpa only [loopData] using collect_call_run h (loopData (ea := ea) a n) (f a)

def halted (w : List ea.Γ) : Cfg (Alphabet h) (Label h) (State h) :=
  ⟨none, initialState h, contents h (emptyStacks h) ⟨[], [], 0, w⟩⟩

theorem done_step (w : List ea.Γ) :
    step (program h) (cfg h (.inr .done) (emptyStacks h) ⟨[], [], 0, w⟩) = some (halted h w) := rfl

theorem finish_call_run (a : A) :
    run h ((ea.encode a).length + 2) (cfg h (.inr .finish) (emptyStacks h) (loopData (ea := ea) a 0)) =
      some (halted h (ea.encode a)) := by
  have hf : run h ((ea.encode a).length + 1)
      (cfg h (.inr .finish) (emptyStacks h) (loopData (ea := ea) a 0)) =
      some (cfg h (.inr .done) (emptyStacks h) ⟨[], [], 0, ea.encode a⟩) := by
    simpa only [List.length_reverse, List.reverse_reverse, List.append_nil, loopData] using
      finish_run h (emptyStacks h) (loopData (ea := ea) a 0) (ea.encode a).reverse []
  rw [show (ea.encode a).length + 2 = ((ea.encode a).length + 1) + 1 by omega, run_add h hf]
  simpa only [run, Function.iterate_one, Option.bind_some] using done_step h (ea.encode a)

theorem finish_loop_run (a : A) :
    run h ((ea.encode a).length + 3) (cfg h (.inr .loop) (emptyStacks h) (loopData (ea := ea) a 0)) =
      some (halted h (ea.encode a)) := by
  rw [show (ea.encode a).length + 3 = ((ea.encode a).length + 2) + 1 by omega,
    run_step h (show step (program h) (cfg h (.inr .loop) (emptyStacks h) (loopData (ea := ea) a 0)) =
      some (cfg h (.inr .finish) (emptyStacks h) (loopData (ea := ea) a 0)) by
        simpa only [loopData] using loop_zero h (emptyStacks h) (loopData (ea := ea) a 0))]
  exact finish_call_run h a

end
end ProteinFolding.Tetrahedral.ReductionTM2.Iterate
