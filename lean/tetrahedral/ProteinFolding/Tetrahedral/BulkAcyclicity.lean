import ProteinFolding.Tetrahedral.BulkEscapeCases
import ProteinFolding.Tetrahedral.BulkEscapeComposition

/-! The actual exhaustive joint classification discharges the generic
escape composition. No global certificate premise remains. -/

namespace ProteinFolding.Tetrahedral

theorem bulkEveryVertex_escapes (m : ℕ) (hm : 50 ≤ m) (p : BulkVertex m) : BulkEscapes m p :=
  bulkEveryVertex_escapes_of_joint_cases m hm (bulkJoint_escape_or_XData m hm) p

theorem bulkFiniteGraph_acyclic (m : ℕ) (hm : 50 ≤ m) : (bulkFiniteGraph m).IsAcyclic :=
  bulkFiniteGraph_acyclic_of_joint_cases m hm (bulkJoint_escape_or_XData m hm)

end ProteinFolding.Tetrahedral
