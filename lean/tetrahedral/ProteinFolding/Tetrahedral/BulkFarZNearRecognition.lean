import ProteinFolding.Tetrahedral.BulkFarZNearData

/-! Exhaustive source and rule recognition in the bounded Z-edge
transition range. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

local instance bulkFarZNearRecognitionFrameFintype : Fintype OctEdgeFrame :=
  Fintype.ofEquiv {q : BulkEdgeFrameCode // ValidBulkEdgeFrameCode q} bulkEdgeFrameCodeEquiv.symm

theorem bulkFarZNear_reference_source (F : OctEdgeFrame) (j : Fin 3) (odd : Bool) (d : Fin 4) :
    BulkZEdgeFrame F → bulkFastDamaged 50 (bulkEdgeCandidate 50 F (bulkFarZNearT j) odd d (by decide)) →
      (bulkFarZPositiveFrame F ∧
        bulkEdgeCandidate 50 F (bulkFarZNearT j) odd d (by decide) = bulkFarZNearRoot F j 0) ∨
      (bulkFarZNegativeFrame F ∧
        bulkEdgeCandidate 50 F (bulkFarZNearT j) odd d (by decide) = bulkFarZNearRoot F j 3) := by
  revert F j odd d
  decide

theorem bulkFarZNear_rule_positive (F : OctEdgeFrame) (j : Fin 3) :
    bulkFarZPositiveFrame F → bulkRuleNeighbour 50 (bulkFarZNearRoot F j 0) (bulkFarZNearRoot F j 1) := by
  revert F j
  decide

theorem bulkFarZNear_rule_negative (F : OctEdgeFrame) (j : Fin 3) :
    bulkFarZNegativeFrame F → bulkRuleNeighbour 50 (bulkFarZNearRoot F j 3) (bulkFarZNearRoot F j 4) := by
  revert F j
  decide

theorem bulkFarZNear_positive_target (F : OctEdgeFrame) (j : Fin 3) (hF : bulkFarZPositiveFrame F)
    (q : Site) (h : bulkRuleNeighbour 50 (bulkFarZNearRoot F j 0) q) : q = bulkFarZNearRoot F j 1 :=
  bulkRuleNeighbour_unique 50 h (bulkFarZNear_rule_positive F j hF)

theorem bulkFarZNear_negative_target (F : OctEdgeFrame) (j : Fin 3) (hF : bulkFarZNegativeFrame F)
    (q : Site) (h : bulkRuleNeighbour 50 (bulkFarZNearRoot F j 3) q) : q = bulkFarZNearRoot F j 4 :=
  bulkRuleNeighbour_unique 50 h (bulkFarZNear_rule_negative F j hF)

end ProteinFolding.Tetrahedral
