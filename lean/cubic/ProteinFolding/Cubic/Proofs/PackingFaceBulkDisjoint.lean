import ProteinFolding.Cubic.Proofs.PackingBackEdge
import ProteinFolding.Cubic.Proofs.PackingBulkWord

/-! Cross-component separation for the complete face words, the straight
back edge, and the interior bulk followed by its exterior approach. -/

namespace ProteinFolding.CubicPackingFaceBulkDisjoint

open CubicPacking CubicCertificates CubicPackingBulk

theorem bulk_bounds (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (j : Fin (d ^ 3 + 2)) :
    (1 ≤ (bulkFold d hd heven).pos j 0 ∧ (bulkFold d hd heven).pos j 0 ≤ (d : ℤ)) ∧
    (1 ≤ (bulkFold d hd heven).pos j 1 ∧ (bulkFold d hd heven).pos j 1 ≤ (d : ℤ) + 1) ∧
    (1 ≤ (bulkFold d hd heven).pos j 2 ∧ (bulkFold d hd heven).pos j 2 ≤ (d : ℤ)) := by
  have hb := (bulkFold_sites d hd heven _).mp ⟨j, rfl⟩
  rcases hb with hp | hp | hp
  · rw [hp]
    dsimp [upperHole, CubicPackingRouting.point]
    omega
  · have hx := hp 0
    have hy := hp 1
    have hz := hp 2
    dsimp only at hx hy hz
    omega
  · rw [hp]
    dsimp [lowerHole, CubicPackingRouting.point]
    omega

theorem face_bulk_disjoint (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (f : CubicPackingFrameFaces.Face)
    (i : Fin (faceWord (d * d)).length) (j : Fin (d ^ 3 + 2)) :
    (CubicPackingFrameFaces.faceFold d hd heven f).pos i ≠ (bulkFold d hd heven).pos j := by
  have hf := CubicPackingFrameFaces.faceFold_region d hd heven f i
  have hb := bulk_bounds d hd heven j
  intro he
  have hx := congrFun he 0
  have hy := congrFun he 1
  have hz := congrFun he 2
  cases f <;> dsimp [CubicPackingFrameFaces.Region] at hf <;> omega

theorem face_approach_disjoint (d alpha : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (f : CubicPackingFrameFaces.Face)
    (i : Fin (faceWord (d * d)).length) (j : Fin (alpha + 8)) :
    (CubicPackingFrameFaces.faceFold d hd heven f).pos i ≠ (approachFold d alpha).pos j := by
  have hf := CubicPackingFrameFaces.faceFold_region d hd heven f i
  have ha := approachPos_exterior d alpha j
  intro he
  have hy : (CubicPackingFrameFaces.faceFold d hd heven f).pos i 1 = approachPos d alpha j 1 := congrFun he 1
  have hz : (CubicPackingFrameFaces.faceFold d hd heven f).pos i 2 = approachPos d alpha j 2 := congrFun he 2
  cases f <;> dsimp [CubicPackingFrameFaces.Region] at hf <;> omega

theorem edge_bulk_disjoint (d : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (i : Fin (edgeWord d).length) (j : Fin (d ^ 3 + 2)) :
    (CubicPackingBackEdge.edgeFold d).pos i ≠ (bulkFold d hd heven).pos j := by
  have he := CubicPackingBackEdge.edgeFold_region d i
  have hb := bulk_bounds d hd heven j
  intro hp
  have hx := congrFun hp 0
  dsimp [CubicPackingBackEdge.Region] at he
  omega

theorem edge_approach_disjoint (d alpha : ℕ)
    (i : Fin (edgeWord d).length) (j : Fin (alpha + 8)) :
    (CubicPackingBackEdge.edgeFold d).pos i ≠ (approachFold d alpha).pos j := by
  have he := CubicPackingBackEdge.edgeFold_region d i
  have ha := approachPos_exterior d alpha j
  intro hp
  have hy : (CubicPackingBackEdge.edgeFold d).pos i 1 = approachPos d alpha j 1 := congrFun hp 1
  have hz : (CubicPackingBackEdge.edgeFold d).pos i 2 = approachPos d alpha j 2 := congrFun hp 2
  dsimp [CubicPackingBackEdge.Region] at he
  omega

theorem top_bulk_disjoint (d : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (i : Fin (faceWord (d * d - 2)).length) (j : Fin (d ^ 3 + 2)) :
    (CubicPackingTopFace.topFold d hd heven).pos i ≠ (bulkFold d (by omega) heven).pos j := by
  have ht := CubicPackingTopFace.topFold_bounds d hd heven i
  have hholes := CubicPackingTopFace.topFold_avoids_hole_columns d hd heven i
  have hb := (bulkFold_sites d (by omega) heven _).mp ⟨j, rfl⟩
  intro he
  have hx := congrFun he 0
  have hy := congrFun he 1
  have hz := congrFun he 2
  rcases hb with hb | hb | hb
  · rw [hb] at hx hy hz
    dsimp [upperHole, CubicPackingRouting.point] at hx hy hz
    exact hholes ⟨hx, Or.inl hz⟩
  · have hby := hb 1
    dsimp only at hby
    omega
  · rw [hb] at hx hy hz
    dsimp [lowerHole, CubicPackingRouting.point] at hx hy hz
    exact hholes ⟨hx, Or.inr hz⟩

theorem top_approach_disjoint (d alpha : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (i : Fin (faceWord (d * d - 2)).length) (j : Fin (alpha + 8)) :
    (CubicPackingTopFace.topFold d hd heven).pos i ≠ (approachFold d alpha).pos j := by
  have ht := CubicPackingTopFace.topFold_bounds d hd heven i
  have hholes := CubicPackingTopFace.topFold_avoids_hole_columns d hd heven i
  intro he
  change (CubicPackingTopFace.topFold d hd heven).pos i = approachPos d alpha j at he
  unfold approachPos approachPoint at he
  split_ifs at he <;>
    (have hx := congrFun he 0
     have hy := congrFun he 1
     have hz := congrFun he 2
     dsimp only [CubicPackingRouting.point] at hx hy hz
     first | exact hholes ⟨hx, Or.inr hz⟩ | omega)

theorem disjoint_bulkApproachWord_of (d alpha : ℕ) (hd : 0 < d) (heven : d % 2 = 0) (p : Site)
    (hb : ∀ j, p ≠ (bulkFold d hd heven).pos j)
    (ha : ∀ j, p ≠ (approachFold d alpha).pos j)
    (j : Fin (bulkApproachWord d alpha).length) : p ≠ (bulkApproachWordFold d alpha hd heven).pos j := by
  intro he
  have hp : ∃ k, (bulkWord d ++ approachWord alpha).get k = (bulkApproachWord d alpha).get j ∧
      (Fold.appendWord (bulkWordFold d hd heven) (approachWordFold d alpha) _ _).pos k = p :=
    ⟨j, rfl, he.symm⟩
  obtain ⟨k, _, hk⟩ | ⟨k, _, hk⟩ := (Fold.appendWord_exists_residue _ _ _ _ _ _).mp hp
  · change (bulkFold d hd heven).pos (Fin.cast (by simp [bulkWord]) k) = p at hk
    exact hb _ hk.symm
  · change (approachFold d alpha).pos (Fin.cast (by simp [approachWord]) k) = p at hk
    exact ha _ hk.symm

theorem face_bulkApproachWord_disjoint (d alpha : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (f : CubicPackingFrameFaces.Face) (i : Fin (faceWord (d * d)).length)
    (j : Fin (bulkApproachWord d alpha).length) :
    (CubicPackingFrameFaces.faceFold d hd heven f).pos i ≠ (bulkApproachWordFold d alpha hd heven).pos j :=
  disjoint_bulkApproachWord_of d alpha hd heven _
    (face_bulk_disjoint d hd heven f i) (face_approach_disjoint d alpha hd heven f i) j

theorem edge_bulkApproachWord_disjoint (d alpha : ℕ) (hd : 0 < d) (heven : d % 2 = 0)
    (i : Fin (edgeWord d).length) (j : Fin (bulkApproachWord d alpha).length) :
    (CubicPackingBackEdge.edgeFold d).pos i ≠ (bulkApproachWordFold d alpha hd heven).pos j :=
  disjoint_bulkApproachWord_of d alpha hd heven _
    (edge_bulk_disjoint d hd heven i) (edge_approach_disjoint d alpha i) j

theorem top_bulkApproachWord_disjoint (d alpha : ℕ) (hd : 2 ≤ d) (heven : d % 2 = 0)
    (i : Fin (faceWord (d * d - 2)).length) (j : Fin (bulkApproachWord d alpha).length) :
    (CubicPackingTopFace.topFold d hd heven).pos i ≠ (bulkApproachWordFold d alpha (by omega) heven).pos j :=
  disjoint_bulkApproachWord_of d alpha (by omega) heven _
    (top_bulk_disjoint d hd heven i) (top_approach_disjoint d alpha hd heven i) j

end ProteinFolding.CubicPackingFaceBulkDisjoint
