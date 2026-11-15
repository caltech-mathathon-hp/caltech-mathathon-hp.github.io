import ProteinFolding.Tetrahedral.BulkNearJointFrameCases1
import ProteinFolding.Tetrahedral.BulkNearJointFrame1023
import ProteinFolding.Tetrahedral.BulkNearJointFrame1032
import ProteinFolding.Tetrahedral.BulkNearJointFrame1203
import ProteinFolding.Tetrahedral.BulkNearJointFrame1230
import ProteinFolding.Tetrahedral.BulkNearJointFrame1302
import ProteinFolding.Tetrahedral.BulkNearJointFrame1320

namespace ProteinFolding.Tetrahedral

theorem bulkNearJoint_position_reference_1 (F : OctEdgeFrame) (hk : F.k = 1) :
    ∀ (t : Fin 10) (odd : Bool) (d e : Fin 4), BulkNearJointPositionCheck F t odd d e := by
  exact bulkNearJointFrame_cases_1 F hk
    (fun G => ∀ (t : Fin 10) (odd : Bool) (d e : Fin 4), BulkNearJointPositionCheck G t odd d e)
    bulkNearJoint_position_frame_1023
    bulkNearJoint_position_frame_1032
    bulkNearJoint_position_frame_1203
    bulkNearJoint_position_frame_1230
    bulkNearJoint_position_frame_1302
    bulkNearJoint_position_frame_1320

end ProteinFolding.Tetrahedral
