import ProteinFolding.Tetrahedral.NearFieldFrameBulkColumns
import ProteinFolding.Tetrahedral.NearFieldBorrowedBulkClearance
import ProteinFolding.Tetrahedral.NearFieldFrameSeparation

/-! The initial terminal H is the unused F' corner U_b, with its actual column. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

def terminalColumn (p : ConstructionParameters) : DanglingColumn p.side :=
  faceDanglingColumn p.side 0 (p.side - 2) 0 (by have h := p.side_ge; omega)

private theorem terminalFaceOwner_eq_entry (m : ℕ) (hm : 3 ≤ m) :
    (faceDanglingColumn m 0 (m - 2) 0 (by omega)).owner =
      octEdgeZigzag m entryEdgeFrame (2 * m - 3) := by
  apply Subtype.ext
  rw [entryEdgeZigzag_coordinates (by omega : 1 ≤ m)]
  funext c
  fin_cases c <;> dsimp [faceDanglingColumn, faceSurfaceSite, faceSurfaceCoordinates,
    entryEdgeCoordinates, octRadius] <;> omega

theorem terminalColumn_owner (p : ConstructionParameters) :
    (terminalColumn p).owner = octEdgeZigzag p.side entryEdgeFrame (2 * p.side - 3) :=
  terminalFaceOwner_eq_entry p.side (by have h := p.side_ge; omega)

theorem terminalColumn_point_bounds (p : ConstructionParameters) (n : ℕ) :
    1 ≤ ((terminalColumn p).point n).val 0 ∧ ((terminalColumn p).point n).val 0 ≤ 2 ∧
      2 * octRadius p.side ≤ ((terminalColumn p).point n).val 1 ∧
        ((terminalColumn p).point n).val 2 ≤ -2 := by
  have hm := p.side_ge
  have hx := faceDanglingColumn_point_coordinates p.side 0 (p.side - 2) 0 (by omega) n 0
  have hy := faceDanglingColumn_point_coordinates p.side 0 (p.side - 2) 0 (by omega) n 1
  have hz := faceDanglingColumn_point_coordinates p.side 0 (p.side - 2) 0 (by omega) n 2
  dsimp only [terminalColumn]
  dsimp [octRadius] at hx hy hz ⊢
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

private theorem terminalBounds_ne_frame (m f : ℕ) (kind : Fin 6) (hm : 30 ≤ m)
    (hfhi : (f : ℤ) + 10 ≤ octRadius m) (x y z : ℤ)
    (hb : 1 ≤ x ∧ x ≤ 2 ∧ 2 * octRadius m ≤ y ∧ z ≤ -2)
    (hx : nearFrameReference m f kind 0 + nearFrameCoordinateLow kind 0 ≤ x ∧
      x ≤ nearFrameReference m f kind 0 + nearFrameCoordinateHigh kind 0)
    (hy : nearFrameReference m f kind 1 + nearFrameCoordinateLow kind 1 ≤ y ∧
      y ≤ nearFrameReference m f kind 1 + nearFrameCoordinateHigh kind 1)
    (hz : nearFrameReference m f kind 2 + nearFrameCoordinateLow kind 2 ≤ z ∧
      z ≤ nearFrameReference m f kind 2 + nearFrameCoordinateHigh kind 2) : False := by
  fin_cases kind <;> dsimp [nearFrameReference, nearFrameCoordinateLow, nearFrameCoordinateHigh, octRadius]
    at hx hy hz hfhi hb <;> omega

theorem terminalColumn_ne_frameP (p : ConstructionParameters) (f : ℕ) (kind : Fin 6)
    (hf : f % 2 = 1) (hfhi : (f : ℤ) + 10 ≤ octRadius p.side)
    (n : ℕ) (r : Fin (nearFrameLength kind)) (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    (terminalColumn p).point n ≠ nearFramePoint p.side f kind hf r := by
  intro heq
  have hb := terminalColumn_point_bounds p n
  have hx := nearFramePoint_coordinate_bounds p.side f kind hf r hr0 hrlast 0
  have hy := nearFramePoint_coordinate_bounds p.side f kind hf r hr0 hrlast 1
  have hz := nearFramePoint_coordinate_bounds p.side f kind hf r hr0 hrlast 2
  rw [← heq] at hx hy hz
  exact terminalBounds_ne_frame p.side f kind (by have h := p.side_ge; omega) hfhi
    _ _ _ hb hx hy hz

theorem terminalColumn_ne_bulkColumn (p : ConstructionParameters) (C : DanglingColumn p.side)
    (hC : C.owner ∈ bulkInterior p.side) (n r : ℕ) : (terminalColumn p).point n ≠ C.point r := by
  apply Ne.symm
  apply bulkColumn_ne_edgeColumn C (terminalColumn p) hC _ r n
  rw [terminalColumn_owner]
  exact edgeZigzag_mem_deleted (by have h := p.side_ge; omega) entryEdgeFrame _ (by have h := p.side_ge; omega)

end ProteinFolding.Tetrahedral.NearField
