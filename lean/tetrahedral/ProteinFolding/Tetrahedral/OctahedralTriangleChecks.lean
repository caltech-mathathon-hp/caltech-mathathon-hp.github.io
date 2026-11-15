import ProteinFolding.Tetrahedral.OctahedralTriangleSides

namespace ProteinFolding.Tetrahedral

example {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (hroom : 3 ≤ m) :
    ¬ ExteriorP3Link m (octEdgeZigzag m F (2 * 1))
      (octEdgeZigzag m F.bigOtherSide (2 * 2)) := by
  rw [exterior_P3_big_different_sides hm F (by decide) (by decide) (by omega) (by omega)]
  decide

example {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (hroom : 3 ≤ m) :
    ExteriorP3Link m (octEdgeZigzag m F (2 * 1 + 1))
      (octEdgeZigzag m F.smallOtherSide (2 * 1 + 1)) := by
  rw [exterior_P3_small_different_sides hm F (by decide) (by decide) (by omega) (by omega)]
  decide

#print axioms big_face_same_side_neighbours
#print axioms small_face_same_side_neighbours
#print axioms big_face_different_sides_neighbours
#print axioms small_face_different_sides_neighbours
#print axioms exterior_P3_big_same_side
#print axioms exterior_P3_small_same_side
#print axioms exterior_P3_big_different_sides
#print axioms exterior_P3_small_different_sides

end ProteinFolding.Tetrahedral
