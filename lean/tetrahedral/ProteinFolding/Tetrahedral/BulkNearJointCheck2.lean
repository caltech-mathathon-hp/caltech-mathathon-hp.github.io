import ProteinFolding.Tetrahedral.BulkNearJointFrameCases2
import ProteinFolding.Tetrahedral.BulkNearJointFrame2013
import ProteinFolding.Tetrahedral.BulkNearJointFrame2031
import ProteinFolding.Tetrahedral.BulkNearJointFrame2103
import ProteinFolding.Tetrahedral.BulkNearJointFrame2130
import ProteinFolding.Tetrahedral.BulkNearJointFrame2301
import ProteinFolding.Tetrahedral.BulkNearJointFrame2310

namespace ProteinFolding.Tetrahedral

theorem bulkNearJoint_position_reference_2 (F : OctEdgeFrame) (hk : F.k = 2) :
    ∀ (t : Fin 10) (odd : Bool) (d e : Fin 4), BulkNearJointPositionCheck F t odd d e := by
  exact bulkNearJointFrame_cases_2 F hk
    (fun G => ∀ (t : Fin 10) (odd : Bool) (d e : Fin 4), BulkNearJointPositionCheck G t odd d e)
    bulkNearJoint_position_frame_2013
    bulkNearJoint_position_frame_2031
    bulkNearJoint_position_frame_2103
    bulkNearJoint_position_frame_2130
    bulkNearJoint_position_frame_2301
    bulkNearJoint_position_frame_2310

end ProteinFolding.Tetrahedral
