import ProteinFolding.Tetrahedral.ReductionTM2IterateStacks

namespace ProteinFolding.Tetrahedral.ReductionTM2.Iterate

open Computability Turing TM2
noncomputable section
variable {A : Type} {ea : FinEncoding A} {f : A → A}
variable (h : TM2ComputableInPolyTime ea ea f) [Inhabited ea.Γ]

def transferRawProgram : Label h → Stmt (Alphabet h) (Label h) ((h.tm.σ × Bool) × Option ea.Γ) :=
  fun l => TM2Renaming.relabelStmt (transferEquiv h).symm (program h l)

theorem transferRaw_prepare : transferRawProgram h (.inr .prepare) =
    TM2Transfer.transferStmt (Γ := Alphabet h) (σ := h.tm.σ × Bool)
      (.inr .buffer) (.inl h.tm.k₀) h.inputAlphabet.symm (.inr .prepare) (.inl h.tm.main) := by
  simp only [transferRawProgram, program, TM2Renaming.relabelStmt_symm]

theorem transferRaw_finish : transferRawProgram h (.inr .finish) =
    TM2Transfer.transferStmt (Γ := Alphabet h) (σ := h.tm.σ × Bool)
      (.inr .buffer) (.inr .output) id (.inr .finish) (.inr .done) := by
  simp only [transferRawProgram, program, TM2Renaming.relabelStmt_symm]

theorem transferRaw_restore :
    (fun l => TM2Renaming.relabelStmt (transferEquiv h) (transferRawProgram h l)) = program h := by
  funext l
  exact TM2Renaming.relabelStmt_symm (transferEquiv h).symm (program h l)

theorem prepare_contents (d : Data (ea := ea)) (u : List ea.Γ) (v : List (h.tm.Γ h.tm.k₀)) :
    TM2Transfer.setStacks (Γ := Alphabet h) (.inr Extra.buffer) (.inl h.tm.k₀)
      (contents h (emptyStacks h) {d with buffer := []}) u v =
      contents h (oneStack h h.tm.k₀ v) {d with buffer := u} := by
  rw [TM2Transfer.setStacks, update_buffer, update_active]
  rfl

theorem prepare_run (d : Data (ea := ea)) (u : List ea.Γ) (v : List (h.tm.Γ h.tm.k₀)) :
    run h (u.length + 1) (cfg h (.inr .prepare) (oneStack h h.tm.k₀ v) {d with buffer := u}) =
      some (cfg h (.inl h.tm.main) (oneStack h h.tm.k₀ ((u.map h.inputAlphabet.symm).reverse ++ v))
        {d with buffer := []}) := by
  have hraw := TM2Transfer.transfer_run (Γ := Alphabet h) (.inr Extra.buffer) (.inl h.tm.k₀) (by simp)
    h.inputAlphabet.symm (.inr Phase.prepare) (.inl h.tm.main) (transferRawProgram h) (transferRaw_prepare h)
    (h.tm.initialState, false) none (contents h (emptyStacks h) {d with buffer := []}) u v
  have hlift := TM2Renaming.run_relabelStmt (transferEquiv h) (transferRawProgram h) (u.length + 1) _ _ hraw
  rw [transferRaw_restore] at hlift
  simpa only [run, TM2Renaming.mapCfg, TM2Transfer.transferCfg, prepare_contents,
    cfg, initialState, transferEquiv] using hlift

theorem finish_contents (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea)) (u v : List ea.Γ) :
    TM2Transfer.setStacks (Γ := Alphabet h) (.inr Extra.buffer) (.inr Extra.output)
      (contents h S {d with buffer := [], output := []}) u v =
      contents h S {d with buffer := u, output := v} := by
  rw [TM2Transfer.setStacks, update_buffer, update_output]

theorem finish_run (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea)) (u v : List ea.Γ) :
    run h (u.length + 1) (cfg h (.inr .finish) S {d with buffer := u, output := v}) =
      some (cfg h (.inr .done) S {d with buffer := [], output := u.reverse ++ v}) := by
  have hraw := TM2Transfer.transfer_run (Γ := Alphabet h) (.inr Extra.buffer) (.inr Extra.output) (by simp)
    id (.inr Phase.finish) (.inr Phase.done) (transferRawProgram h) (transferRaw_finish h)
    (h.tm.initialState, false) none (contents h S {d with buffer := [], output := []}) u v
  have hlift := TM2Renaming.run_relabelStmt (transferEquiv h) (transferRawProgram h) (u.length + 1) _ _ hraw
  rw [transferRaw_restore] at hlift
  simpa only [run, TM2Renaming.mapCfg, TM2Transfer.transferCfg, finish_contents,
    cfg, initialState, transferEquiv, List.map_id] using hlift

end
end ProteinFolding.Tetrahedral.ReductionTM2.Iterate
