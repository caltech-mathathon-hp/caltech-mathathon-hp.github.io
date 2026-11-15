import ProteinFolding.Tetrahedral.BulkXJointInvariants
import ProteinFolding.Tetrahedral.BulkInwardNeighbour

/-! Concrete escape and X-joint data used by the final bulk proof. -/

namespace ProteinFolding.Tetrahedral

def BulkEscapes (m : ℕ) (p : BulkVertex m) : Prop :=
  ∃ q : BulkVertex m, (bulkFiniteGraph m).Reachable p q ∧
    ((bulkFiniteGraph m).degree q ≤ 1 ∨ bulkSegmentPotential m p < bulkSegmentPotential m q)

structure BulkXJointData (m : ℕ) (p q : BulkVertex m) : Prop where
  adj : (bulkFiniteGraph m).Adj p q
  positive : BulkXPositiveJointInvariant m p.val q.val
  negative : BulkXNegativeJointInvariant m p.val
  inward : BulkHasInwardNeighbour m p.val
  x_bound : |p.val.val 0| ≤ 3
  alpha_bound : |bulkAlpha m p.val| ≤ octRadius m - 37
  axes : 2 ≤ |bulkY m p.val| ∧ 2 ≤ |bulkZ p.val|
  signs : bulkYSign m q.val = bulkYSign m p.val ∧ bulkZSign q.val = bulkZSign p.val
  merge : bulkMerge m p.val q.val ∨ bulkMerge m q.val p.val

end ProteinFolding.Tetrahedral
