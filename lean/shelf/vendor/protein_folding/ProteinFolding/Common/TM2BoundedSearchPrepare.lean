import ProteinFolding.Common.TM2BoundedSearchStacks
import ProteinFolding.Common.TM2RenamingExtra

/-! Moving the reversed saved input back into the predicate machine's input
stack. State conjugation permits reuse of the fully counted transfer loop.
-/

namespace ProteinFolding.TM2BoundedSearch

open Computability Turing TM2
noncomputable section

variable {A : Type} {ea : FinEncoding A} {test : A × ℕ → Bool}
variable (hp : TM2ComputableInPolyTime (pairEncoding ea unaryFinEncodingNat) finEncodingBoolBool test)

def prepareRawProgram : Label hp →
    Stmt (Alphabet hp) (Label hp) (((savedPredicate hp).tm.σ × Bool) × Option (InputSymbol (ea := ea))) :=
  fun l => TM2Renaming.relabelStmt (transferEquiv hp).symm (program hp l)

theorem prepareRaw_at : prepareRawProgram hp (.inr .prepare) =
    TM2Transfer.transferStmt (Γ := Alphabet hp) (σ := (savedPredicate hp).tm.σ × Bool)
      (.inr .buffer) (.inl (savedPredicate hp).tm.k₀) (savedPredicate hp).inputAlphabet.symm
      (.inr .prepare) (.inl (savedPredicate hp).tm.main) := by
  simp only [prepareRawProgram, program, TM2Renaming.relabelStmt_symm]

theorem prepareRaw_restore :
    (fun l => TM2Renaming.relabelStmt (transferEquiv hp) (prepareRawProgram hp l)) = program hp := by
  funext l
  exact TM2Renaming.relabelStmt_symm (transferEquiv hp).symm (program hp l)

theorem prepare_contents (d : Data (ea := ea)) (u : List (InputSymbol (ea := ea)))
    (v : List ((savedPredicate hp).tm.Γ (savedPredicate hp).tm.k₀)) :
    TM2Transfer.setStacks (Γ := Alphabet hp) (.inr Extra.buffer) (.inl (savedPredicate hp).tm.k₀)
      (contents hp (emptyStacks hp) {d with buffer := []}) u v =
      contents hp (oneStack hp (savedPredicate hp).tm.k₀ v) {d with buffer := u} := by
  rw [TM2Transfer.setStacks, update_buffer, update_active]
  rfl

theorem prepare_run (d : Data (ea := ea)) (u : List (InputSymbol (ea := ea)))
    (v : List ((savedPredicate hp).tm.Γ (savedPredicate hp).tm.k₀)) :
    run hp (u.length + 1)
      (cfg hp (.inr .prepare) (oneStack hp (savedPredicate hp).tm.k₀ v) {d with buffer := u}) =
      some (cfg hp (.inl (savedPredicate hp).tm.main)
        (oneStack hp (savedPredicate hp).tm.k₀
          ((u.map (savedPredicate hp).inputAlphabet.symm).reverse ++ v)) {d with buffer := []}) := by
  have hraw := TM2Transfer.transfer_run (Γ := Alphabet hp) (.inr Extra.buffer)
    (.inl (savedPredicate hp).tm.k₀) (by simp)
    (savedPredicate hp).inputAlphabet.symm (.inr Phase.prepare) (.inl (savedPredicate hp).tm.main)
    (prepareRawProgram hp) (prepareRaw_at hp) ((savedPredicate hp).tm.initialState, false) none
    (contents hp (emptyStacks hp) {d with buffer := []}) u v
  have hlift := TM2Renaming.run_relabelStmt (transferEquiv hp) (prepareRawProgram hp)
    (u.length + 1) _ _ hraw
  rw [prepareRaw_restore] at hlift
  simpa only [run, TM2Renaming.mapCfg, TM2Transfer.transferCfg, prepare_contents,
    cfg, initialState, transferEquiv] using hlift

end
end ProteinFolding.TM2BoundedSearch
