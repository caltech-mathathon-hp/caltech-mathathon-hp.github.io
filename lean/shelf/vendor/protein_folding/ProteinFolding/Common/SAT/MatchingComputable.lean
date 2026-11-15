import ProteinFolding.Common.SAT.MatchingEnumerationCorrect
import ProteinFolding.Common.SAT.CNFToMatching

/-! The complete executable source map, including its actual polynomial-time
TM2 witness. The block ordering of the final coordinate is an alternative
vertex renaming of the same occurrence gadget. -/

namespace ProteinFolding.ThreeDimensionalMatching.SourceQueries

open Computability Turing SAT TM2CompositionPoly TM2ProductMap

def blockGraph (φ : CNF) : Instance := ⟨vertexCount φ, denseTriples φ⟩

def cnfToBlockMatching (φ : CNF) : Instance :=
  if φ.length ≤ (indexedOccurrences φ).length then blockGraph φ else noInstance

theorem blockGraph_eq_graphInstance (φ : CNF) :
    blockGraph φ = graphInstance (vertexCount φ)
      (fun x y z => rawRelation φ x.val y.val z.val) := by
  unfold blockGraph
  rw [denseTriples_eq_graphTriples]
  rfl

noncomputable def blockGraphComputable :
    TM2ComputableInPolyTime cnfEncoding instanceEncoding blockGraph := by
  let h := pairComputable vertexCountComputable denseTriplesComputable
  exact
    { toTM2ComputableAux := h.toTM2ComputableAux
      time := h.time
      outputsFun := h.outputsFun }

/-- An actual finite TM2 computes the total direct CNF-to-3DM map in time
polynomial in the frozen binary-variable CNF encoding length. -/
noncomputable def cnfToBlockMatchingComputable :
    TM2ComputableInPolyTime cnfEncoding instanceEncoding cnfToBlockMatching := by
  let h := TM2Conditional.iteComputable (leQuery clauseCountComputable literalCountComputable)
    blockGraphComputable (TM2Constants.constantComputable cnfEncoding instanceEncoding noInstance)
  simpa only [cnfToBlockMatching, decide_eq_true_eq] using h

theorem blockGraph_wellFormed (φ : CNF) : WellFormed (blockGraph φ) := by
  rw [blockGraph_eq_graphInstance]
  exact graphInstance_wellFormed _ _

theorem cnfToBlockMatching_wellFormed (φ : CNF) : WellFormed (cnfToBlockMatching φ) := by
  unfold cnfToBlockMatching
  split
  · exact blockGraph_wellFormed φ
  · simp [noInstance, WellFormed]

end ProteinFolding.ThreeDimensionalMatching.SourceQueries
