import ProteinFolding.Tetrahedral.BulkFastLocal
import ProteinFolding.Tetrahedral.FaceRowsGeometry

/-! Kernel-checked local reference points for N3. These concern the actual
canonical merge-and-patch graph, using its proved four-neighbour evaluator. -/

namespace ProteinFolding.Tetrahedral.NearField

def secondRowFarReference : Site := faceSurfaceSite 23 0 10 10 1 (by decide)

def secondRowLeftReference (b : Fin 10) : Site :=
  faceSurfaceSite 50 0 (47 - b.val) b.val 1 (by have h := b.isLt; omega)

def secondRowRightReference (a : Fin 10) : Site :=
  faceSurfaceSite 50 0 a.val (47 - a.val) 1 (by have h := a.isLt; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem secondRowFarReference_degree :
    (bulkFastCoverDirections 23 secondRowFarReference).card = 2 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem secondRowLeftReference_degree (b : Fin 10) :
    bulkFastInterior 50 (secondRowLeftReference b) →
      (bulkFastCoverDirections 50 (secondRowLeftReference b)).card = 2 := by
  fin_cases b <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem secondRowRightReference_degree (a : Fin 10) :
    bulkFastInterior 50 (secondRowRightReference a) →
      (bulkFastCoverDirections 50 (secondRowRightReference a)).card = 2 := by
  fin_cases a <;> decide

end ProteinFolding.Tetrahedral.NearField
