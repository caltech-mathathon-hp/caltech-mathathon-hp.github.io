import ProteinFolding.Tetrahedral.BulkFarZAscent
import ProteinFolding.Tetrahedral.BulkNearEdgeGeometry

/-! Complete local row witnesses for the transition indices 10,11,12.
They remain inside the start vertex's 31-box. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def bulkFarZNearT (j : Fin 3) : ℕ := j.val + 10
def bulkFarZNearMap (F : OctEdgeFrame) (j : Fin 3) : Site → Site :=
  bulkEdgeReanchor 27 50 13 (bulkFarZNearT j) F
def bulkFarZNearRoot (F : OctEdgeFrame) (j : Fin 3) (i : Fin 6) : Site :=
  bulkFarZNearMap F j (bulkFarZRoot i)
def bulkFarZNearOther (F : OctEdgeFrame) (j : Fin 3) (i : Fin 6) : Site :=
  bulkFarZNearMap F j (bulkFarZOther i)
def bulkFarZNearSupport (F : OctEdgeFrame) (j : Fin 3) (i : Fin 6) : Finset Site :=
  {bulkFarZNearRoot F j i, bulkFarZNearOther F j i}
def bulkFarZNearRank (F : OctEdgeFrame) (j : Fin 3) (i : Fin 6) (p : Site) : ℕ :=
  if p = bulkFarZNearRoot F j i then 0 else 1
def bulkFarZNearPrev (F : OctEdgeFrame) (j : Fin 3) (i : Fin 6) (_ : Site) : Site :=
  bulkFarZNearRoot F j i

local instance bulkFarZNearDataFrameFintype : Fintype OctEdgeFrame :=
  Fintype.ofEquiv {q : BulkEdgeFrameCode // ValidBulkEdgeFrameCode q} bulkEdgeFrameCodeEquiv.symm

theorem bulkFarZNear_reference_quick (F : OctEdgeFrame) (j : Fin 3) (i : Fin 6) :
    BulkFarZFamily F i → BulkSegmentQuickCheck 50 (bulkFarZNearSupport F j i)
      (bulkFarZNearRoot F j i) (bulkFarZNearRank F j i) (bulkFarZNearPrev F j i) := by
  unfold BulkFarZFamily
  revert F j i
  decide

theorem bulkFarZNear_reference_boxes (F : OctEdgeFrame) (j : Fin 3) (i : Fin 6) :
    BulkFarZFamily F i → ∀ p ∈ bulkFarZNearSupport F j i,
      InBulkVertexBox 50 (bulkEdgeStartIndex F) 31 p := by
  unfold BulkFarZFamily InBulkVertexBox
  revert F j i
  decide

theorem bulkFarZNear_reference_row (F : OctEdgeFrame) (j : Fin 3) (i : Fin 6) :
    BulkFarZFamily F i → ∃ p ∈ bulkFarZNearSupport F j i, bulkFastDamaged 50 p ∧ bulkZ p = 0 := by
  unfold BulkFarZFamily
  revert F j i
  decide

theorem bulkFarZNear_reference_joint (F : OctEdgeFrame) (j : Fin 3) (i : Fin 4) :
    BulkFarZAscendingFrame F i →
      bulkFarZNearMap F j (bulkFarZJointSource i) ∈ bulkFarZNearSupport F j (bulkFarZFrom i) ∧
      bulkFarZNearMap F j (bulkFarZJointTarget i) ∈ bulkFarZNearSupport F j (bulkFarZTo i) ∧
      bulkFastCoverBond 50 (bulkFarZNearMap F j (bulkFarZJointSource i))
        (bulkFarZNearMap F j (bulkFarZJointTarget i)) := by
  unfold BulkFarZAscendingFrame
  revert F j i
  decide

end ProteinFolding.Tetrahedral
