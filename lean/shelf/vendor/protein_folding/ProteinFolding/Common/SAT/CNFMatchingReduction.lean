import ProteinFolding.Common.SAT.MatchingComputable
import ProteinFolding.Common.SAT.MatchingRelationCorrect
import ProteinFolding.Common.ComplexityComposition

/-! The direct CNF-to-unary-3DM Karp reduction is fully proved, including
the concrete finite TM2 runtime witness. Source NP-hardness uses precisely
the explicit frozen Cook--Levin statement as a hypothesis. -/

namespace ProteinFolding.ThreeDimensionalMatching

open Computability Turing SAT SourceQueries

theorem cnfToBlockMatching_correct (φ : CNF) :
    Accepts (cnfToBlockMatching φ) ↔ Satisfiable φ := by
  unfold cnfToBlockMatching
  split
  · rename_i h
    rw [blockGraph_eq_graphInstance]
    have hn : 2 * (indexedOccurrences φ).length = vertexCount φ := (vertexCount_eq φ).symm
    have hg := congrArg (fun n => graphInstance n
      (fun x y z : Fin n => rawRelation φ x.val y.val z.val)) hn
    exact (congrArg (fun I : Instance => Accepts I ↔ Satisfiable φ) hg).mp
      (blockGraph_accepts_iff φ h)
  · rename_i hbad
    have hunsat : ¬ Satisfiable φ := by
      intro hs
      exact hbad (layout_clause_bound (formulaLayout φ) ((formulaLayout_satisfiable_iff φ).mpr hs))
    exact iff_of_false noInstance_rejects hunsat

/-- The source reduction uses the frozen binary CNF encoding and the explicit
unary-universe 3DM encoding, with a proved actual polynomial-time machine. -/
theorem cnfToBlockMatching_karp :
    KarpReduces cnfEncoding instanceEncoding Satisfiable Accepts :=
  ⟨cnfToBlockMatching, ⟨cnfToBlockMatchingComputable⟩, fun φ => (cnfToBlockMatching_correct φ).symm⟩

/-- Cook--Levin implies NP-hardness of explicit-universe unary 3DM through
the proved direct occurrence-gadget Karp reduction. -/
theorem unaryMatching_NPHard_of_cookLevin (hCL : CookLevin) :
    UnaryThreeDimensionalMatchingNPHard :=
  npHard_of_cookLevin_reduction hCL cnfToBlockMatching_karp

end ProteinFolding.ThreeDimensionalMatching
