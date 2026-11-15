import ProteinFolding.Cubic.Proofs.PackingSkeletonAttachments

/-! Full-site separation of the initial lifted skeleton word from the four
complete faces, the almost-complete top face, the straight back edge and bulk.
The initial lift is arbitrary subject to the already constructed H support
and exterior P properties; no unproved geometric separation is assumed. -/

namespace ProteinFolding.CubicPackingInitialDisjoint

open CubicPacking CubicCertificates CubicPackingGeometry CubicPackingLift CubicPackingPrefix
open CubicPackingAttachments CubicPackingSkeletonAttachments CubicPackingBulk

theorem face_H_inside (d : ℕ) (f : CubicPackingFrameFaces.Face) (p : Site)
    (hp : CubicPackingFrameFaces.HSupport d f p) : p ∈ cube (fun _ => 0) (d + 2) := by
  rw [cube_mem_coordinates]
  cases f <;> dsimp [CubicPackingFrameFaces.HSupport] at hp <;> omega

theorem top_H_inside (d : ℕ) (p : Site) (hp : CubicPackingTopFace.HSupport d p) :
    p ∈ cube (fun _ => 0) (d + 2) := by
  rw [cube_mem_coordinates]
  dsimp [CubicPackingTopFace.HSupport] at hp
  omega

theorem edge_H_inside (d : ℕ) (p : Site)
    (hp : p 0 = 0 ∧ (1 ≤ p 1 ∧ p 1 ≤ (d : ℤ)) ∧ p 2 = (d : ℤ) + 1) :
    p ∈ cube (fun _ => 0) (d + 2) := by
  rw [cube_mem_coordinates]
  omega

theorem faceFold_near_cube (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (f : CubicPackingFrameFaces.Face) :
    ∀ i, NearCube d ((CubicPackingFrameFaces.faceFold d hd heven f).pos i) := by
  apply faceWord_near_cube _ d (CubicPackingFrameFaces.faceLength_even d heven)
  intro i hi
  apply face_H_inside d f
  exact (CubicPackingFrameFaces.faceFold_hydrophobicSites d hd heven f _).mp ⟨i, hi, rfl⟩

theorem topFold_near_cube (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0) :
    ∀ i, NearCube d ((CubicPackingTopFace.topFold d hd heven).pos i) := by
  apply faceWord_near_cube _ d (CubicPackingTopFace.topLength_even d heven)
  intro i hi
  apply top_H_inside d
  exact (CubicPackingTopFace.topFold_hydrophobicSites d hd heven _).mp ⟨i, hi, rfl⟩

theorem backEdge_near_cube (d : ℕ) : ∀ i, NearCube d ((CubicPackingBackEdge.edgeFold d).pos i) := by
  apply edgeWord_near_cube d d
  intro i hi
  apply edge_H_inside d
  exact (CubicPackingBackEdge.edgeFold_hydrophobicSites d _).mp ⟨i, hi, rfl⟩

section Initial

variable (d : ℕ) (hd : 0 < d)
  (initial : Fold cubicLattice (edgeWord (9 * d + 8)).length)
  (hH : hydrophobicSites (edgeWord (9 * d + 8)) initial = Set.range (skeletonPrefixFold d hd).pos)
  (hP : ∀ i, (edgeWord (9 * d + 8)).get i = .P → initial.pos i ∉ cube (fun _ => 0) (d + 2))

include hH

theorem initial_H_base (i : Fin (edgeWord (9 * d + 8)).length) (hi : (edgeWord (9 * d + 8)).get i = .H) :
    ∃ k, (skeletonPrefixFold d hd).pos k = initial.pos i := by
  have hm : initial.pos i ∈ hydrophobicSites (edgeWord (9 * d + 8)) initial := ⟨i, hi, rfl⟩
  rw [hH] at hm
  exact hm

theorem initial_H_skeleton (i : Fin (edgeWord (9 * d + 8)).length) (hi : (edgeWord (9 * d + 8)).get i = .H) :
    EdgeSkeleton (fun _ => 0) (d + 2) (initial.pos i) := by
  obtain ⟨k, hk⟩ := initial_H_base d hd initial hH i hi
  rw [← hk]
  exact skeletonPrefixFold_skeleton d hd k

include hP

theorem initial_face_disjoint (heven : d % 2 = 0) (f : CubicPackingFrameFaces.Face) :
    ∀ i j, initial.pos i ≠ (CubicPackingFrameFaces.faceFold d hd heven f).pos j := by
  apply folds_disjoint_of_H_disjoint initial (CubicPackingFrameFaces.faceFold d hd heven f) (fun _ => 0) (d + 2)
  · exact fun i hi => (initial_H_skeleton d hd initial hH i hi).1
  · intro j hj
    apply face_H_inside d f
    exact (CubicPackingFrameFaces.faceFold_hydrophobicSites d hd heven f _).mp ⟨j, hj, rfl⟩
  · exact hP
  · exact CubicPackingFrameFaces.faceFold_P_outside_cube d hd heven f
  · exact edgeWord_P_has_H_neighbour _ initial
  · exact faceWord_P_has_H_neighbour _ (CubicPackingFrameFaces.faceLength_even d heven) _
  · intro i j hi hj he
    have hsk := initial_H_skeleton d hd initial hH i hi
    have hface := (CubicPackingFrameFaces.faceFold_hydrophobicSites d hd heven f _).mp ⟨j, hj, rfl⟩
    exact no_skeleton_face d f _ hface (he ▸ hsk)

theorem initial_top_disjoint (hd2 : 2 ≤ d) (heven : d % 2 = 0) :
    ∀ i j, initial.pos i ≠ (CubicPackingTopFace.topFold d hd2 heven).pos j := by
  apply folds_disjoint_of_H_disjoint initial (CubicPackingTopFace.topFold d hd2 heven) (fun _ => 0) (d + 2)
  · exact fun i hi => (initial_H_skeleton d hd initial hH i hi).1
  · intro j hj
    apply top_H_inside d
    exact (CubicPackingTopFace.topFold_hydrophobicSites d hd2 heven _).mp ⟨j, hj, rfl⟩
  · exact hP
  · exact CubicPackingTopFace.topFold_P_outside_cube d hd2 heven
  · exact edgeWord_P_has_H_neighbour _ initial
  · exact faceWord_P_has_H_neighbour _ (CubicPackingTopFace.topLength_even d heven) _
  · intro i j hi hj he
    have hsk := initial_H_skeleton d hd initial hH i hi
    have htop := (CubicPackingTopFace.topFold_hydrophobicSites d hd2 heven _).mp ⟨j, hj, rfl⟩
    exact no_skeleton_xz_interior d _ htop.2.1 htop.2.2.1 (he ▸ hsk)

theorem initial_backEdge_disjoint :
    ∀ i j, initial.pos i ≠ (CubicPackingBackEdge.edgeFold d).pos j := by
  apply folds_disjoint_of_H_disjoint initial (CubicPackingBackEdge.edgeFold d) (fun _ => 0) (d + 2)
  · exact fun i hi => (initial_H_skeleton d hd initial hH i hi).1
  · intro j hj
    apply edge_H_inside d
    exact (CubicPackingBackEdge.edgeFold_hydrophobicSites d _).mp ⟨j, hj, rfl⟩
  · exact hP
  · exact CubicPackingBackEdge.edgeFold_P_outside_cube d
  · exact edgeWord_P_has_H_neighbour _ initial
  · exact edgeWord_P_has_H_neighbour _ _
  · intro i j hi hj he
    obtain ⟨k, hk⟩ := initial_H_base d hd initial hH i hi
    have hedge := (CubicPackingBackEdge.edgeFold_hydrophobicSites d _).mp ⟨j, hj, rfl⟩
    apply skeletonPrefixFold_avoids_back_edge d hd k ((CubicPackingBackEdge.edgeFold d).pos j 1)
      (by omega) hedge.2.1.2
    have hp := hk.trans he
    apply site_ext
    · exact (congrFun hp 0).trans hedge.1
    · exact congrFun hp 1
    · exact (congrFun hp 2).trans hedge.2.2

theorem initial_bulkApproachWord_disjoint (alpha : ℕ) (hd2 : 2 ≤ d) (heven : d % 2 = 0) :
    ∀ i j, initial.pos i ≠ (bulkApproachWordFold d alpha hd heven).pos j :=
  skeleton_E_bulkApproachWord_disjoint d alpha (9 * d + 8) hd2 heven initial
    (initial_H_skeleton d hd initial hH) hP

end Initial

end ProteinFolding.CubicPackingInitialDisjoint
