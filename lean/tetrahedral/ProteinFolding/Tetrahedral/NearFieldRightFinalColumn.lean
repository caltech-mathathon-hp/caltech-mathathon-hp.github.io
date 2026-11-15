import ProteinFolding.Tetrahedral.NearFieldTerminalColumn
import ProteinFolding.Tetrahedral.NearFieldFrameFaceColumns
import ProteinFolding.Tetrahedral.NearFieldPPPCanonicalColumns
import ProteinFolding.Tetrahedral.NearFieldFrameFolds

/-! The right filler's actual final B-corner column. It is the first B site
of the exit edge and the last B site of the track edge. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def rightFinalColumn (p : ConstructionParameters) : DanglingColumn p.side :=
  faceDanglingColumn p.side 0 0 (p.side - 2) (by have h := p.side_ge; omega)

theorem rightFinalColumn_exit_owner (p : ConstructionParameters) :
    (rightFinalColumn p).owner = octEdgeZigzag p.side exitEdgeFrame 1 := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  apply Subtype.ext
  rw [exitEdgeZigzag_coordinates hm]
  funext c
  fin_cases c
  all_goals dsimp [rightFinalColumn, faceDanglingColumn, faceSurfaceSite, faceSurfaceCoordinates,
    exitEdgeCoordinates, octRadius]
  all_goals have h := p.side_ge; omega

theorem rightFinalColumn_track_owner (p : ConstructionParameters) :
    (rightFinalColumn p).owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.side - 3) := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  apply Subtype.ext
  rw [trackEdgeZigzag_coordinates hm]
  funext c
  fin_cases c
  all_goals dsimp [rightFinalColumn, faceDanglingColumn, faceSurfaceSite, faceSurfaceCoordinates,
    trackEdgeCoordinates, octRadius]
  all_goals have h := p.side_ge; omega

theorem rightFinalColumn_owner_inB (p : ConstructionParameters) :
    InBSublattice (rightFinalColumn p).owner.val := by
  rw [rightFinalColumn_exit_owner]
  exact (octEdgeZigzag_odd (by have h := p.side_ge; omega) exitEdgeFrame 0).1

theorem rightFinalColumn_point_bounds (p : ConstructionParameters) (n : ℕ) :
    octRadius p.side - 1 ≤ ((rightFinalColumn p).point n).val 0 ∧
      ((rightFinalColumn p).point n).val 0 ≤ octRadius p.side ∧
      octRadius p.side + 2 ≤ ((rightFinalColumn p).point n).val 1 ∧
      ((rightFinalColumn p).point n).val 2 ≤ -2 := by
  have hm := p.side_ge
  have hx := faceDanglingColumn_point_coordinates p.side 0 0 (p.side - 2) (by omega) n 0
  have hy := faceDanglingColumn_point_coordinates p.side 0 0 (p.side - 2) (by omega) n 1
  have hz := faceDanglingColumn_point_coordinates p.side 0 0 (p.side - 2) (by omega) n 2
  dsimp only [rightFinalColumn]
  dsimp [octRadius] at hx hy hz ⊢
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

theorem rightFinalColumn_ne_frameP (p : ConstructionParameters) (f : ℕ) (kind : Fin 6)
    (hf : f % 2 = 1) (hflo : 5 ≤ f) (n : ℕ) (r : Fin (nearFrameLength kind))
    (hr0 : 0 < r.val) (hrlast : r.val + 1 < nearFrameLength kind) :
    (rightFinalColumn p).point n ≠ nearFramePoint p.side f kind hf r := by
  apply faceColumn_ne_frameP p.side 0 0 (p.side - 2) (by have h := p.side_ge; omega)
    (by have h := p.side_ge; omega) f hf kind _ n r hr0 hrlast
  intro _ heq
  have hi := octEdgeZigzag_injective (by have h := p.side_ge; omega : 1 ≤ p.side) exitEdgeFrame
    ((rightFinalColumn_exit_owner p).symm.trans heq)
  omega

theorem rightFinalColumn_ne_framePFold (p : ConstructionParameters) (f : ℕ) (kind : Fin 6)
    (hf : f % 2 = 1) (hflo : 5 ≤ f) (n : ℕ) (r : Fin (nearFrameLength kind - 2)) :
    (rightFinalColumn p).point n ≠ (framePFold p.side f kind hf).pos r :=
  rightFinalColumn_ne_frameP p f kind hf hflo n
    ⟨r.val + 1, by have h := r.isLt; omega⟩
    (by change 0 < r.val + 1; omega)
    (by change r.val + 1 + 1 < _; have h := r.isLt; omega)

theorem rightFinalColumn_ne_bulkColumn (p : ConstructionParameters) (C : DanglingColumn p.side)
    (hC : C.owner ∈ bulkInterior p.side) (n r : ℕ) :
    (rightFinalColumn p).point n ≠ C.point r := by
  apply Ne.symm
  apply bulkColumn_ne_edgeColumn C (rightFinalColumn p) hC _ r n
  rw [rightFinalColumn_exit_owner]
  exact edgeZigzag_mem_deleted (by have h := p.side_ge; omega) exitEdgeFrame 1 (by have h := p.side_ge; omega)

theorem rightFinalColumn_ne_edgePPP (p : ConstructionParameters) (F : OctEdgeFrame) (r : ℕ)
    (hr : r + 2 < 2 * p.side - 1)
    (hp : (rightFinalColumn p).owner ≠ octEdgeZigzag p.side F r)
    (hq : (rightFinalColumn p).owner ≠ octEdgeZigzag p.side F (r + 2)) (n : ℕ) (s : Fin 3) :
    (rightFinalColumn p).point n ≠ (edgePPPFold p.side F r).pos s :=
  (edgePPPFold_ne_Bcorner_column p.side (by have h := p.side_ge; omega) F exitEdgeFrame r hr
    (rightFinalColumn p) (rightFinalColumn_exit_owner p) hp hq s n).symm

theorem faceColumns_ne_of_c_lt (m a b c a' b' c' : ℕ)
    (hs : a + b + c + 2 = m) (ht : a' + b' + c' + 2 = m) (hc : c < c') (n r : ℕ) :
    (faceDanglingColumn m a b c hs).point n ≠ (faceDanglingColumn m a' b' c' ht).point r := by
  intro heq
  have hx := congrArg (fun x : Site => x.val 0) heq
  change ((faceDanglingColumn m a b c hs).point n).val 0 =
    ((faceDanglingColumn m a' b' c' ht).point r).val 0 at hx
  rw [faceDanglingColumn_point_coordinates, faceDanglingColumn_point_coordinates] at hx
  omega

theorem terminalColumn_ne_rightFinalColumn (p : ConstructionParameters) (n r : ℕ) :
    (terminalColumn p).point n ≠ (rightFinalColumn p).point r :=
  faceColumns_ne_of_c_lt p.side 0 (p.side - 2) 0 0 0 (p.side - 2)
    (by have h := p.side_ge; omega) (by have h := p.side_ge; omega)
    (by have h := p.side_ge; omega) n r

end ProteinFolding.Tetrahedral.NearField
