import ProteinFolding.Tetrahedral.NearFieldDimerChainFold
import ProteinFolding.Tetrahedral.NearFieldPPPEdges
import ProteinFolding.Tetrahedral.FrameForcingTrackPath
import ProteinFolding.Tetrahedral.BulkEdgeReversal

/-! Concrete side and corner pieces of the three-side ring units. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def ringNextFrame (F : OctEdgeFrame) : OctEdgeFrame :=
  (bulkReverseEdgeFrame F).smallOtherSide

theorem ringNextFrame_three (F : OctEdgeFrame) :
    ringNextFrame (ringNextFrame (ringNextFrame F)) = F := by
  cases F
  rfl

theorem ringNext_start_corner (m : ℕ) (hm : 1 ≤ m) (F : OctEdgeFrame) :
    octEdgeZigzag m (bulkReverseEdgeFrame F) 1 = octEdgeZigzag m (ringNextFrame F) 1 :=
  start_corner_shared m hm (bulkReverseEdgeFrame F)

theorem ringSide_last_eq_reverse_three (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) :
    octEdgeZigzag m F (2 * m - 5) = octEdgeZigzag m (bulkReverseEdgeFrame F) 3 := by
  have h := bulkEdgeAnchor_odd_reverse (by omega : 1 ≤ m) F (m - 3) (by omega)
  rw [bulkEdgeAnchor_next, bulkEdgeAnchor_next] at h
  have hidx : 2 * (m - 3) + 1 = 2 * m - 5 := by omega
  have hrev : m - 2 - (m - 3) = 1 := by omega
  simpa only [hidx, hrev] using h

def ringCornerFold (m : ℕ) (F : OctEdgeFrame) : Fold tetrahedralLattice 3 :=
  (edgePPPFold m (bulkReverseEdgeFrame F) 1).reverse

theorem ringCornerFold_first_seam (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) :
    tetrahedralLattice.Adj (octEdgeZigzag m F (2 * m - 5)) ((ringCornerFold m F).pos 0) := by
  change tetrahedralLattice.Adj (octEdgeZigzag m F (2 * m - 5))
    ((edgePPPFold m (bulkReverseEdgeFrame F) 1).pos 2)
  rw [ringSide_last_eq_reverse_three m hm F]
  exact (edgePPPFold_last_seam m (bulkReverseEdgeFrame F) 1).symm

theorem ringCornerFold_last_seam (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) :
    tetrahedralLattice.Adj ((ringCornerFold m F).pos 2) (octEdgeZigzag m (ringNextFrame F) 1) := by
  change tetrahedralLattice.Adj ((edgePPPFold m (bulkReverseEdgeFrame F) 1).pos 0)
    (octEdgeZigzag m (ringNextFrame F) 1)
  rw [← ringNext_start_corner m (by omega) F]
  exact (edgePPPFold_first_seam m (bulkReverseEdgeFrame F) 1).symm

theorem ringCornerFold_outside (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (i : Fin 3) :
    (ringCornerFold m F).pos i ∉ octahedron m :=
  edgePPPFold_outside (by omega : 1 ≤ m) (bulkReverseEdgeFrame F) 1 (by omega) i.rev

theorem ringCornerFold_skin (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) (i : Fin 3) :
    (ringCornerFold m F).pos i ∈ skin m 1 :=
  edgePPPFold_mem_skin_one (by omega : 1 ≤ m) (bulkReverseEdgeFrame F) 1 (by omega) i.rev

def ringSideFold (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame) :
    Fold tetrahedralLattice (dimerChain (m - 2)).length :=
  (edgeDimerFold (by omega : 1 ≤ m) F 1 (m - 3) false (by omega)).onLength
    (by rw [show m - 3 + 1 = m - 2 by omega])

theorem ringSideFold_pos (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (i : Fin (dimerChain (m - 2)).length) :
    (ringSideFold m hm F).pos i = edgeDimerCurve m F 1 false i.val := rfl

theorem ringSideFold_first (m : ℕ) (hm : 3 ≤ m) (F : OctEdgeFrame)
    (i : Fin (dimerChain (m - 2)).length) (hi : i.val = 0) :
    (ringSideFold m hm F).pos i = octEdgeZigzag m F 1 := by
  rw [ringSideFold_pos, hi]
  rfl

theorem ringSideFold_last (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0) (F : OctEdgeFrame)
    (i : Fin (dimerChain (m - 2)).length) (hi : i.val + 1 = (dimerChain (m - 2)).length) :
    (ringSideFold m hm F).pos i = octEdgeZigzag m F (2 * m - 5) := by
  have hlen : (dimerChain (m - 2)).length = 5 * (m - 3) + 2 := by
    simpa only [show m - 3 + 1 = m - 2 by omega] using dimerChain_succ_length (m - 3)
  have hidx : i.val = 5 * (m - 3) + 1 := by omega
  rw [ringSideFold_pos, hidx]
  change edgeDimerCurve m F 1 false (5 * (m - 3) + (1 : Fin 2).val) = _
  rw [edgeDimerCurve_H]
  congr 1
  dsimp [dimerHIndex, dimerFlip]
  omega

end ProteinFolding.Tetrahedral.NearField
