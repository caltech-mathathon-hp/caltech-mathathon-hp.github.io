import ProteinFolding.Cubic.Proofs.PackingInitialDisjoint

/-! The single P between the almost-complete top face and bulk H block.
It lies over the upper omitted hole and is disjoint from all earlier ordinary
components, as well as from the following bulk and approach. -/

namespace ProteinFolding.CubicPackingTopBridge

open CubicPacking CubicCertificates CubicPackingGeometry CubicPackingLift CubicPackingBulk
open CubicPackingAttachments CubicPackingSkeletonAttachments CubicPackingFaceBulkDisjoint
open CubicPackingInitialDisjoint
open CubicPackingTopFace (point)

def bridgePoint (d : ℕ) : Site := point d (d + 2) d
def bridgeWord : Sequence := [.P]
def bridgeFold (d : ℕ) : Fold cubicLattice bridgeWord.length := singleFold (bridgePoint d)

theorem bridgeFold_hydrophobicSites (d : ℕ) : hydrophobicSites bridgeWord (bridgeFold d) = ∅ := by
  ext p
  simp [hydrophobicSites, bridgeWord, List.get_eq_getElem]

theorem bridgePoint_outside_cube (d : ℕ) : bridgePoint d ∉ cube (fun _ => 0) (d + 2) := by
  intro hc
  have hy := (hc 1).2
  change (d : ℤ) + 2 < 0 + ((d + 2 : ℕ) : ℤ) at hy
  omega

theorem bridgePoint_face_disjoint (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (f : CubicPackingFrameFaces.Face) (i : Fin (faceWord (d * d)).length) :
    bridgePoint d ≠ (CubicPackingFrameFaces.faceFold d hd heven f).pos i := by
  have hf := CubicPackingFrameFaces.faceFold_region d hd heven f i
  intro he
  have hy := congrFun he 1
  change (d : ℤ) + 2 = _ at hy
  cases f <;> dsimp [CubicPackingFrameFaces.Region] at hf <;> omega

theorem bridgePoint_top_disjoint (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (i : Fin (faceWord (d * d - 2)).length) :
    bridgePoint d ≠ (CubicPackingTopFace.topFold d hd heven).pos i := by
  have ht := CubicPackingTopFace.topFold_avoids_hole_columns d hd heven i
  intro he
  have hx := congrFun he 0
  have hz := congrFun he 2
  change (d : ℤ) = _ at hx hz
  exact ht ⟨hx.symm, Or.inl hz.symm⟩

theorem bridgePoint_backEdge_disjoint (d : ℕ) (i : Fin (edgeWord d).length) :
    bridgePoint d ≠ (CubicPackingBackEdge.edgeFold d).pos i := by
  have he := CubicPackingBackEdge.edgeFold_region d i
  intro hp
  have hy := congrFun hp 1
  change (d : ℤ) + 2 = _ at hy
  dsimp [CubicPackingBackEdge.Region] at he
  omega

theorem bridgePoint_bulk_disjoint (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (j : Fin (d ^ 3 + 2)) :
    bridgePoint d ≠ (bulkFold d hd heven).pos j := by
  intro he
  exact bridgePoint_outside_cube d (he.symm ▸ bulkFold_in_cube d hd heven j)

theorem bridgePoint_approach_disjoint (d alpha : ℕ) (hd : 2 ≤ d) (j : Fin (alpha + 8)) :
    bridgePoint d ≠ (approachFold d alpha).pos j := by
  intro he
  change bridgePoint d = approachPos d alpha j at he
  unfold approachPos approachPoint at he
  split_ifs at he <;>
    (have hx := congrFun he 0
     have hy := congrFun he 1
     have hz := congrFun he 2
     dsimp [bridgePoint, point, CubicPackingRouting.point] at hx hy hz
     omega)

theorem bridgePoint_bulkApproachWord_disjoint (d alpha : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (j : Fin (bulkApproachWord d alpha).length) :
    bridgePoint d ≠ (bulkApproachWordFold d alpha (by omega) heven).pos j :=
  disjoint_bulkApproachWord_of d alpha (by omega) heven _
    (bridgePoint_bulk_disjoint d (by omega) heven) (bridgePoint_approach_disjoint d alpha hd) j

theorem skeleton_not_adjacent_bridgePoint (d : ℕ) (hd : 2 ≤ d) (p : Site)
    (hp : EdgeSkeleton (fun _ => 0) (d + 2) p) : ¬ cubicLattice.Adj (bridgePoint d) p := by
  intro ha
  have hhole : upperHole d ∈ cube (fun _ => 0) (d + 2) := by
    rw [cube_mem_coordinates]
    dsimp [upperHole, CubicPackingRouting.point]
    omega
  have hstep : cubicLattice.Adj (bridgePoint d) (upperHole d) := by
    change latticeDistance _ _ = 1
    rw [distance_eq]
    simp [bridgePoint, upperHole, point, CubicPackingRouting.point]
  have he := cube_exterior_neighbour_unique (fun _ => 0) (d + 2) (bridgePoint d) p (upperHole d)
    (bridgePoint_outside_cube d) hp.1 hhole ha hstep
  have hnot : ¬ EdgeSkeleton (fun _ => 0) (d + 2) (upperHole d) := by
    apply no_skeleton_xz_interior
    · dsimp [upperHole, CubicPackingRouting.point]; omega
    · dsimp [upperHole, CubicPackingRouting.point]; omega
  exact hnot (he ▸ hp)

theorem bridgePoint_skeleton_E_disjoint (d t : ℕ) (hd : 2 ≤ d)
    (f : Fold cubicLattice (edgeWord t).length)
    (hH : ∀ i, (edgeWord t).get i = .H → EdgeSkeleton (fun _ => 0) (d + 2) (f.pos i))
    (i : Fin (edgeWord t).length) : bridgePoint d ≠ f.pos i := by
  intro he
  cases hi : (edgeWord t).get i with
  | H => exact bridgePoint_outside_cube d (he.symm ▸ (hH i hi).1)
  | P =>
    obtain ⟨k, hk, hik⟩ := edgeWord_P_has_H_neighbour t f i hi
    exact skeleton_not_adjacent_bridgePoint d hd (f.pos k) (hH k hk) (he.symm ▸ hik)

theorem bridgePoint_initial_disjoint (d : ℕ) (hd : 2 ≤ d)
    (initial : Fold cubicLattice (edgeWord (9 * d + 8)).length)
    (hH : hydrophobicSites (edgeWord (9 * d + 8)) initial =
      Set.range (CubicPackingPrefix.skeletonPrefixFold d (by omega)).pos)
    (i : Fin (edgeWord (9 * d + 8)).length) : bridgePoint d ≠ initial.pos i :=
  bridgePoint_skeleton_E_disjoint d (9 * d + 8) hd initial
    (initial_H_skeleton d (by omega) initial hH) i

theorem top_bridge_seam (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (i : Fin (faceWord (d * d - 2)).length) (hi : i.val + 1 = (faceWord (d * d - 2)).length) :
    cubicLattice.Adj ((CubicPackingTopFace.topFold d hd heven).pos i) (bridgePoint d) := by
  rw [CubicPackingTopFace.topFold_last_of_end d hd heven i hi]
  change latticeDistance _ _ = 1
  rw [distance_eq]
  simp [bridgePoint, point]

theorem bridge_bulk_seam (d : ℕ) : cubicLattice.Adj (bridgePoint d) (upperHole d) := by
  change latticeDistance _ _ = 1
  rw [distance_eq]
  simp [bridgePoint, upperHole, point, CubicPackingRouting.point]

end ProteinFolding.CubicPackingTopBridge
