import ProteinFolding.Tetrahedral.BulkJointPlanes
import ProteinFolding.Tetrahedral.BulkBendX

/-! Local X-joint invariants in terms of the two explicit bend formulas.
Their raw forms depend only on X, charge, quadrant signs and alpha differences. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def bulkXPositiveBend (m : ℕ) (p : Site) : ℤ :=
  p.val 0 - (siteCharge p - 1) * (bulkYSign m p * bulkZSign p)
def bulkXNegativeBend (m : ℕ) (p : Site) : ℤ :=
  p.val 0 - siteCharge p * (bulkYSign m p * bulkZSign p)

def BulkXPositiveJointInvariant (m : ℕ) (p q : Site) : Prop :=
  (bulkXPositiveBend m p = -3 ∨ bulkXPositiveBend m p = -1 ∨
    bulkXPositiveBend m p = 1 ∨ bulkXPositiveBend m p = 3) ∧
  bulkAlpha m q - bulkAlpha m p =
    (if |bulkXPositiveBend m p| = 1 then 2 else -2) * (bulkYSign m p * bulkZSign p)

def BulkXNegativeJointInvariant (m : ℕ) (p : Site) : Prop :=
  (bulkXNegativeBend m p = 0 ∧ siteCharge p = 1) ∨
  (bulkXNegativeBend m p = -2 ∧ siteCharge p = 0) ∨
  (bulkXNegativeBend m p = 2 ∧ siteCharge p = 0) ∨
  (bulkXNegativeBend m p = -4 ∧ siteCharge p = 1 ∧ bulkYSign m p = bulkZSign p) ∨
  (bulkXNegativeBend m p = 4 ∧ siteCharge p = 1 ∧ bulkYSign m p = -bulkZSign p)

instance (m : ℕ) (p q : Site) : Decidable (BulkXPositiveJointInvariant m p q) := by
  unfold BulkXPositiveJointInvariant
  infer_instance
instance (m : ℕ) (p : Site) : Decidable (BulkXNegativeJointInvariant m p) := by
  unfold BulkXNegativeJointInvariant
  infer_instance

local instance bulkXJointInvariantReferenceFrameFintype : Fintype OctEdgeFrame :=
  Fintype.ofEquiv {q : BulkEdgeFrameCode // ValidBulkEdgeFrameCode q} bulkEdgeFrameCodeEquiv.symm

theorem bulkXJoint_reference_invariants (F : OctEdgeFrame) (odd : Bool) (d e : Fin 4) :
    BulkXEdgeFrame F → bulkFastMerge 21 (bulkEdgeCandidate 21 F 10 odd d (by decide))
      (step (bulkEdgeCandidate 21 F 10 odd d (by decide)) e) →
      BulkXPositiveJointInvariant 21 (bulkEdgeCandidate 21 F 10 odd d (by decide))
        (step (bulkEdgeCandidate 21 F 10 odd d (by decide)) e) ∧
      BulkXNegativeJointInvariant 21 (bulkEdgeCandidate 21 F 10 odd d (by decide)) ∧
      BulkXPositiveJointInvariant 21 (step (bulkEdgeCandidate 21 F 10 odd d (by decide)) e)
        (bulkEdgeCandidate 21 F 10 odd d (by decide)) ∧
      BulkXNegativeJointInvariant 21 (step (bulkEdgeCandidate 21 F 10 odd d (by decide)) e) := by
  revert F odd d e
  decide

end ProteinFolding.Tetrahedral
