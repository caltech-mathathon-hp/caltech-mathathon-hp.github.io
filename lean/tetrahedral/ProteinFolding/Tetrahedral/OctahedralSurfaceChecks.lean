import ProteinFolding.Tetrahedral.OctahedralEdgeParametrization

namespace ProteinFolding.Tetrahedral

-- The small-size exception is explicit: all six coordinate formulas coincide,
-- and their common site has four dangling directions.
example : (octVertices 1).card = 1 := by decide

example : (octDanglingDirections 1 (octVertexSite 1 0 true)).card = 4 := by
  rw [octDanglingDirections_A 1 (octVertexCoordinates_inA 1 0 true)
    (octVertexSite_mem_octahedron (by decide) 0 true)]
  decide

example {m : ℕ} (hm : 2 ≤ m) : (octVertices m).card = 6 := octVertices_card hm

example {m : ℕ} (hm : 2 ≤ m) {p : Site} (hp : p ∈ octahedron m) :
    (externalNeighbours (octahedron m) p).card ≤ 2 := by
  rw [← octDanglingDirections_card_eq_external]
  exact octahedron_dangling_le_two hm hp

example {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) :
    (octEdgeSites m F).card = 2 * m - 1 := octEdgeSites_card hm F

#print axioms octVertices_card
#print axioms two_dangling_iff_vertex
#print axioms octahedron_dangling_le_two
#print axioms bonded_big_small_faces
#print axioms bonded_surface_sites_iff_common_edge
#print axioms octEdgeHeight4_max_iff
#print axioms saturated_path_unique
#print axioms octEdgeZigzag_even
#print axioms octEdgeZigzag_odd
#print axioms octAEdgeSite_iff_param
#print axioms octBEdgeSite_iff_param
#print axioms octEdgeSites_card
#print axioms octEdgeZigzag_adj_iff
#print axioms octEdgeZigzag_unique_geodesic

end ProteinFolding.Tetrahedral
