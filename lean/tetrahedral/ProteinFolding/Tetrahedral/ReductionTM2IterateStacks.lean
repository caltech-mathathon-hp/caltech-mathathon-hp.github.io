import ProteinFolding.Tetrahedral.ReductionTM2IterateMachine

namespace ProteinFolding.Tetrahedral.ReductionTM2.Iterate

open Computability Turing TM2
noncomputable section
variable {A : Type} {ea : FinEncoding A} {f : A → A}
variable (h : TM2ComputableInPolyTime ea ea f) [Inhabited ea.Γ]

theorem update_active (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea)) (k : h.tm.K) (w : List (h.tm.Γ k)) :
    Function.update (contents h S d) (.inl k) w = contents h (Function.update S k w) d :=
  TM2Embedding.joinStacks_update S (extraContents d) k w

theorem update_input (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea)) (w : List (InputSymbol (ea := ea))) :
    Function.update (contents h S d) (.inr .input) w = contents h S {d with input := w} := by
  funext k
  cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, extraContents]

theorem update_buffer (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea)) (w : List ea.Γ) :
    Function.update (contents h S d) (.inr .buffer) w = contents h S {d with buffer := w} := by
  funext k
  cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, extraContents]

theorem update_remaining (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea)) (n : ℕ) :
    Function.update (contents h S d) (.inr .remaining) (List.replicate n ()) =
      contents h S {d with remaining := n} := by
  funext k
  cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, extraContents]

theorem update_output (S : ∀ k, List (h.tm.Γ k)) (d : Data (ea := ea)) (w : List ea.Γ) :
    Function.update (contents h S d) (.inr .output) w = contents h S {d with output := w} := by
  funext k
  cases k with
  | inl k => simp [contents, TM2Embedding.joinStacks]
  | inr k => cases k <;> simp [contents, TM2Embedding.joinStacks, extraContents]

theorem oneStack_self (k : h.tm.K) (w : List (h.tm.Γ k)) : oneStack h k w k = w := by simp [oneStack]
theorem oneStack_empty (k : h.tm.K) : oneStack h k [] = emptyStacks h := by
  funext j
  by_cases hk : j = k
  · subst j; simp [oneStack, emptyStacks]
  · simp [oneStack, emptyStacks, hk]
theorem oneStack_update (k : h.tm.K) (w w' : List (h.tm.Γ k)) :
    Function.update (oneStack h k w) k w' = oneStack h k w' := by simp [oneStack, Function.update_idem]

theorem initList_stacks (w : List (h.tm.Γ h.tm.k₀)) :
    (initList h.tm w).stk = oneStack h h.tm.k₀ w := by
  funext k
  by_cases hk : k = h.tm.k₀
  · subst k; simp [initList, oneStack]
  · simp [initList, oneStack, emptyStacks, hk]
theorem haltList_stacks (w : List (h.tm.Γ h.tm.k₁)) :
    (haltList h.tm w).stk = oneStack h h.tm.k₁ w := by
  funext k
  by_cases hk : k = h.tm.k₁
  · subst k; simp [haltList, oneStack]
  · simp [haltList, oneStack, emptyStacks, hk]

def callInput (a : A) : List (h.tm.Γ h.tm.k₀) := (ea.encode a).map h.inputAlphabet.symm
def callOutput (a : A) : List (h.tm.Γ h.tm.k₁) := (ea.encode a).map h.outputAlphabet.symm

theorem child_run (a : A) (d : Data (ea := ea)) :
    run h (h.outputsFun a).steps (cfg h (.inl h.tm.main) (oneStack h h.tm.k₀ (callInput h a)) d) =
      some (cfg h (.inr .collect) (oneStack h h.tm.k₁ (callOutput h (f a))) d) := by
  let hs := h.outputsFun a
  have hrun := hs.evals_in_steps
  change (fun q : Option h.tm.Cfg => q.bind (step h.tm.m))^[hs.steps]
    (some (initList h.tm (callInput h a))) = some (haltList h.tm (callOutput h (f a))) at hrun
  have hlift := TM2Embedding.simulate_run (step h.tm.m) (step (program h))
    (TM2Embedding.embedCfg Sum.inl (some (.inr Phase.collect)) (none, false) (extraContents d))
    (fun a b hh => TM2Embedding.step_liftStmt Sum.inl (some (.inr Phase.collect))
      h.tm.m (program h) (fun _ => rfl) (none, false) (extraContents d) a b hh) hs.steps _ _ hrun
  have hi : TM2Embedding.embedCfg Sum.inl (some (.inr Phase.collect)) (none, false) (extraContents d)
      (initList h.tm (callInput h a)) =
      cfg h (.inl h.tm.main) (oneStack h h.tm.k₀ (callInput h a)) d := by
    simp only [TM2Embedding.embedCfg, initList, cfg, initialState, contents, Option.elim_some]
    rw [← initList_stacks]
    rfl
  have ho : TM2Embedding.embedCfg Sum.inl (some (.inr Phase.collect)) (none, false) (extraContents d)
      (haltList h.tm (callOutput h (f a))) =
      cfg h (.inr .collect) (oneStack h h.tm.k₁ (callOutput h (f a))) d := by
    simp only [TM2Embedding.embedCfg, haltList, cfg, initialState, contents, Option.elim_none]
    rw [← haltList_stacks]
    rfl
  simpa only [run, hi, ho] using hlift

end
end ProteinFolding.Tetrahedral.ReductionTM2.Iterate
