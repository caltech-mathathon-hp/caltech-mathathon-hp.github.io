import ProteinFolding.Tetrahedral.NearFieldFrameEndpoints
import ProteinFolding.Tetrahedral.NearFieldFrameCapColumns
import ProteinFolding.Tetrahedral.NearFieldFrameTethers
import ProteinFolding.Tetrahedral.NearFieldFrameTetherHalfspaces
import ProteinFolding.Tetrahedral.NearFieldFrameBulkColumns
import ProteinFolding.Tetrahedral.NearFieldFrameFolds
import ProteinFolding.Tetrahedral.NearFieldFrameTetherCaps

namespace ProteinFolding.Tetrahedral

example : nearFrameLength 0 - 2 = 6 := by decide
example : nearFrameLength 2 - 2 = 3 := by decide
example : nearFrameLength 4 - 2 = 10 := by decide

#print axioms nearFrameOffset_colour
#print axioms nearFrameOffset_step
#print axioms nearFramePoint_injective
#print axioms nearFramePath_isChain
#print axioms nearFramePList_mem_skin_one
#print axioms nearFrame_start_eq
#print axioms nearFrame_end_eq
#print axioms nearFramePLists_disjoint
#print axioms frameLinkerCap_step
#print axioms NearField.frameBorrowPoint_adj
#print axioms NearField.frameBorrowPoint_injective
#print axioms NearField.frameBorrowPoint_outside
#print axioms NearField.frameBorrowPoint_ne_frameP
#print axioms frameEndpointColumns_disjoint
#print axioms frameEndpointColumn_ne_frameP
#print axioms faceColumn_ne_frameP
#print axioms interiorFaceColumn_ne_frameP
#print axioms faceEntryCap_ne_frameP
#print axioms NearField.frameBorrowPoints_ne
#print axioms NearField.frameBorrowPoint_ne_faceColumn
#print axioms NearField.entryTetherFold_ne_frameP
#print axioms NearField.exitTetherFold_ne_frameP
#print axioms NearField.entryTetherFold_positive
#print axioms NearField.exitTetherFold_positive
#print axioms NearField.FacePositive.ne_frameBorrowPoint
#print axioms NearField.FacePositive.ne_frameEndpointColumn
#print axioms column_owner_deleted_of_eq_frameP
#print axioms bulkColumn_ne_frameP
#print axioms NearField.framePFold_first_seam
#print axioms NearField.framePFold_last_seam
#print axioms NearField.framePFolds_disjoint
#print axioms NearField.tetherFold_dangling_eq_endpoint
#print axioms NearField.tetherFold_ne_other_dangling

end ProteinFolding.Tetrahedral
