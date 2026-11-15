import ProteinFolding.Common.SAT.MatchingGadgetRaw

/-! A total semantic reduction from the frozen CNF problem to raw balanced
three-dimensional matching. It uses the occurrence-cycle gadget directly;
the clauses need not first be converted to width three. On the impossible
clause/occurrence-count branch it returns a fixed no-instance. Polynomial
output length and an actual TM2 runtime witness remain separate obligations.
-/

namespace ProteinFolding.ThreeDimensionalMatching

open SAT

theorem layout_clause_bound {q m : ℕ} (L : OccurrenceLayout q m)
    (h : LayoutSatisfiable L) : m ≤ q := by
  classical
  obtain ⟨_, h⟩ := h
  let f : Fin m → Fin q := fun j => Classical.choose (h j)
  have hf : ∀ j, L.clause (f j) = j := fun j => (Classical.choose_spec (h j)).1
  have hinj : Function.Injective f := by
    intro i j he
    have he' := congrArg L.clause he
    simpa only [hf] using he'
  simpa using Fintype.card_le_of_injective f hinj

def noInstance : Instance := ⟨1, []⟩

theorem noInstance_rejects : ¬ Accepts noInstance := by
  rintro ⟨_, chosen, hc⟩
  have hl : chosen.length = 1 := matches_length hc
  have hs : chosen.length ≤ 0 := hc.1.length_le
  omega

def cnfToMatching (φ : CNF) : Instance :=
  if h : φ.length ≤ (indexedOccurrences φ).length then gadgetInstance (formulaLayout φ) h
  else noInstance

theorem cnfToMatching_wellFormed (φ : CNF) : WellFormed (cnfToMatching φ) := by
  unfold cnfToMatching
  split
  · exact gadgetInstance_wellFormed _ _
  · simp [noInstance, WellFormed]

theorem cnfToMatching_correct (φ : CNF) :
    Accepts (cnfToMatching φ) ↔ Satisfiable φ := by
  unfold cnfToMatching
  split
  · rw [gadgetInstance_accepts_iff, formulaLayout_satisfiable_iff]
  · rename_i hbad
    have hunsat : ¬ Satisfiable φ := by
      intro hs
      exact hbad (layout_clause_bound (formulaLayout φ) ((formulaLayout_satisfiable_iff φ).mpr hs))
    exact iff_of_false noInstance_rejects hunsat

end ProteinFolding.ThreeDimensionalMatching
