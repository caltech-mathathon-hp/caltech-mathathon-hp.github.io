import ProteinFolding.Tetrahedral.BulkNearJointFrameCases3
import ProteinFolding.Tetrahedral.BulkNearJointFrame3012
import ProteinFolding.Tetrahedral.BulkNearJointFrame3021
import ProteinFolding.Tetrahedral.BulkNearJointFrame3102
import ProteinFolding.Tetrahedral.BulkNearJointFrame3120
import ProteinFolding.Tetrahedral.BulkNearJointFrame3201
import ProteinFolding.Tetrahedral.BulkNearJointFrame3210

namespace ProteinFolding.Tetrahedral

theorem bulkNearJoint_position_reference_3 (F : OctEdgeFrame) (hk : F.k = 3) :
    ∀ (t : Fin 10) (odd : Bool) (d e : Fin 4), BulkNearJointPositionCheck F t odd d e := by
  exact bulkNearJointFrame_cases_3 F hk
    (fun G => ∀ (t : Fin 10) (odd : Bool) (d e : Fin 4), BulkNearJointPositionCheck G t odd d e)
    bulkNearJoint_position_frame_3012
    bulkNearJoint_position_frame_3021
    bulkNearJoint_position_frame_3102
    bulkNearJoint_position_frame_3120
    bulkNearJoint_position_frame_3201
    bulkNearJoint_position_frame_3210

end ProteinFolding.Tetrahedral
