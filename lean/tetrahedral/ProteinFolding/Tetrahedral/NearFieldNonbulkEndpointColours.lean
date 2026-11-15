import ProteinFolding.Tetrahedral.NearFieldCanonicalEndpointColours
import ProteinFolding.Tetrahedral.NearFieldSeparatorEndpoints
import ProteinFolding.Tetrahedral.NearFieldFrameVertexCaps
import ProteinFolding.Tetrahedral.FarFieldParity

/-! Physical H-owner colours for every nonbulk unit of the canonical word.
The terminal B, AA units, AB right filler and BB rings use one convention. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096

theorem ownerColour_A {x : Site} (hx : InASublattice x.val) : FarField.colour x = true := by
  simp only [FarField.colour, hx, decide_true]

theorem ownerColour_B {x : Site} (hx : InBSublattice x.val) : FarField.colour x = false := by
  have hn := (inB_iff_not_inA _).mp hx
  simp only [FarField.colour, hn, decide_false]

theorem frameEndpointColumn_owner_colours (p : ConstructionParameters) :
    (FarField.colour (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) true).owner,
      FarField.colour (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) false).owner) = (true, true) := by
  apply Prod.ext
  · exact ownerColour_A (frameEndpointVertex_inA p.side true)
  · exact ownerColour_A (frameEndpointVertex_inA p.side false)

theorem singletonColumn_owner_colours {m : ℕ} (C D : DanglingColumn m)
    (hC : C.owner ∈ octVertices m) (hD : D.owner = C.owner) :
    (FarField.colour C.owner, FarField.colour D.owner) = (true, true) := by
  have hA := octVertices_inA hC
  rw [hD]
  exact Prod.ext (ownerColour_A hA) (ownerColour_A hA)

theorem separatorColumn_owner_colours (p : ConstructionParameters) (k : ℕ) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10)) :
    (FarField.colour C.owner, FarField.colour D.owner) = (true, true) := by
  rw [hC, hD]
  exact Prod.ext (ownerColour_A (separatorFirstH_inA p k)) (ownerColour_A (separatorLastH_inA p k))

theorem leftFillerColumn_owner_colours (p : ConstructionParameters) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2)) :
    (FarField.colour C.owner, FarField.colour D.owner) = (true, true) := by
  rw [hC, hD]
  exact Prod.ext (ownerColour_A (leftFillerFirstH_inA p)) (ownerColour_A (leftFillerLastH_inA p))

theorem itemColumn_owner_colours (p : ConstructionParameters) (base n : ℕ)
    (hb : base % 2 = 0) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side trackEdgeFrame base)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (base + 2 * n - 2)) :
    (FarField.colour C.owner, FarField.colour D.owner) = (true, true) := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  rw [hC, hD]
  apply Prod.ext
  · exact ownerColour_A (edgeZigzag_inA_of_even hm trackEdgeFrame base hb)
  · exact ownerColour_A (edgeZigzag_inA_of_even hm trackEdgeFrame _ (by omega))

theorem rightFillerColumn_owner_colours (p : ConstructionParameters) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side trackEdgeFrame (2 * (p.separatorIndex p.bins + 2)))
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.side - 3)) :
    (FarField.colour C.owner, FarField.colour D.owner) = (true, false) := by
  rw [hC, hD]
  exact Prod.ext (ownerColour_A (rightFillerFirstH_inA p)) (ownerColour_B (rightFillerLastH_inB p))

end ProteinFolding.Tetrahedral.NearField
