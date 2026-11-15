import ProteinFolding.Tetrahedral.BulkNearJointFrameCases0
import ProteinFolding.Tetrahedral.BulkNearJointFrame0123
import ProteinFolding.Tetrahedral.BulkNearJointFrame0132
import ProteinFolding.Tetrahedral.BulkNearJointFrame0213
import ProteinFolding.Tetrahedral.BulkNearJointFrame0231
import ProteinFolding.Tetrahedral.BulkNearJointFrame0312
import ProteinFolding.Tetrahedral.BulkNearJointFrame0321

namespace ProteinFolding.Tetrahedral

theorem bulkNearJoint_position_reference_0 (F : OctEdgeFrame) (hk : F.k = 0) :
    ∀ (t : Fin 10) (odd : Bool) (d e : Fin 4), BulkNearJointPositionCheck F t odd d e := by
  exact bulkNearJointFrame_cases_0 F hk
    (fun G => ∀ (t : Fin 10) (odd : Bool) (d e : Fin 4), BulkNearJointPositionCheck G t odd d e)
    bulkNearJoint_position_frame_0123
    bulkNearJoint_position_frame_0132
    bulkNearJoint_position_frame_0213
    bulkNearJoint_position_frame_0231
    bulkNearJoint_position_frame_0312
    bulkNearJoint_position_frame_0321

end ProteinFolding.Tetrahedral
