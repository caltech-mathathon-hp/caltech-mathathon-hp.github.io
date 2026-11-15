import ProteinFolding.Tetrahedral.BulkFarZData

/-! Every far class-Z damaged source is one of the two row sources.
Its rule neighbour is uniquely the next row's root. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

local instance bulkFarZRecognitionFrameFintype : Fintype OctEdgeFrame :=
  Fintype.ofEquiv {q : BulkEdgeFrameCode // ValidBulkEdgeFrameCode q} bulkEdgeFrameCodeEquiv.symm

theorem bulkFarZ_reference_source (F : OctEdgeFrame) (odd : Bool) (d : Fin 4) :
    BulkZEdgeFrame F → bulkFastDamaged 27 (bulkEdgeCandidate 27 F 13 odd d (by decide)) →
      (bulkFarZPositiveFrame F ∧ bulkEdgeCandidate 27 F 13 odd d (by decide) = bulkFarZRoot 0) ∨
      (bulkFarZNegativeFrame F ∧ bulkEdgeCandidate 27 F 13 odd d (by decide) = bulkFarZRoot 3) := by
  revert F odd d
  decide

theorem bulkFarZ_rule_positive_target (q : Site)
    (h : bulkRuleNeighbour 27 (bulkFarZRoot 0) q) : q = bulkFarZRoot 1 :=
  bulkRuleNeighbour_unique 27 h (by decide)

theorem bulkFarZ_rule_negative_target (q : Site)
    (h : bulkRuleNeighbour 27 (bulkFarZRoot 3) q) : q = bulkFarZRoot 4 :=
  bulkRuleNeighbour_unique 27 h (by decide)

end ProteinFolding.Tetrahedral
