import ProteinFolding.Tetrahedral.NearFieldRingLocations
import ProteinFolding.Tetrahedral.NearFieldRingFaceGeometry

/-! Complete ring bodies on different small faces are disjoint, including
all six side/corner combinations and the two corner/corner combinations. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem ringTerminalSite_ne_small_faces (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (hj : F.j ≠ G.j) (i j : Fin 3) (e e' : Fin 2) :
    ringTerminalSite m F i e ≠ ringTerminalSite m G j e' := by
  intro heq
  have hmem := ringTerminalSite_mem m hm F i e
  rw [heq] at hmem
  exact Finset.disjoint_left.mp (ringSideHsites_disjoint_small_faces m hm F G hj i j)
    hmem (ringTerminalSite_mem m hm G j e')

theorem ringForeignTerminal_linkOwnerExcluded (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (hj : F.j ≠ G.j) (i j : Fin 3) (e : Fin 2) :
    DimerLinkOwnerExcluded m (ringSideFrame F i) 1 (m - 3) false (ringTerminalSite m G j e) := by
  apply dimerLinkOwnerExcluded_of_not_mem
  intro hmem
  exact Finset.disjoint_left.mp (ringSideHsites_disjoint_small_faces m hm F G hj i j)
    hmem (ringTerminalSite_mem m hm G j e)

theorem ringSideFolds_disjoint_small_faces (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (hj : F.j ≠ G.j) (i j : Fin 3)
    (r s : Fin (dimerChain (m - 2)).length) :
    (ringSideFold m hm (ringSideFrame F i)).pos r ≠ (ringSideFold m hm (ringSideFrame G j)).pos s := by
  let r' : Fin (dimerChain (m - 3 + 1)).length :=
    ⟨r.val, by rw [show m - 3 + 1 = m - 2 by omega]; exact r.isLt⟩
  let s' : Fin (dimerChain (m - 3 + 1)).length :=
    ⟨s.val, by rw [show m - 3 + 1 = m - 2 by omega]; exact s.isLt⟩
  exact edgeDimerFolds_disjoint (by omega : 1 ≤ m) (ringSideFrame F i) (ringSideFrame G j)
    1 (m - 3) 1 (m - 3) false false (by omega) (by omega)
    (ringSideHsites_disjoint_small_faces m hm F G hj i j) r' s'

theorem ringSide_ne_foreign_corner (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (hj : F.j ≠ G.j) (i : Fin 3) (c : Fin 2)
    (r : Fin (dimerChain (m - 2)).length) (s : Fin 3) :
    (ringSideFold m hm (ringSideFrame F i)).pos r ≠
      (ringCornerFold m (ringSideFrame G c.castSucc)).pos s := by
  have hs := ringForeignTerminal_linkOwnerExcluded m hm F G hj i c.succ 0
  have ht := ringForeignTerminal_linkOwnerExcluded m hm F G hj i c.castSucc 1
  rw [← ringCorner_start_owner m hm G c] at hs
  rw [← ringCorner_end_owner m hm G c] at ht
  let r' : Fin (dimerChain (m - 3 + 1)).length :=
    ⟨r.val, by rw [show m - 3 + 1 = m - 2 by omega]; exact r.isLt⟩
  exact edgeDimerFold_ne_edgePPPFold (by omega : 1 ≤ m) (ringSideFrame F i)
    (bulkReverseEdgeFrame (ringSideFrame G c.castSucc)) 1 (m - 3) false (by omega)
    1 (by omega) hs ht r' s.rev

theorem ringCorners_disjoint_small_faces (m : ℕ) (hm : 3 ≤ m) (F G : OctEdgeFrame)
    (hj : F.j ≠ G.j) (c d : Fin 2) (r s : Fin 3) :
    (ringCornerFold m (ringSideFrame F c.castSucc)).pos r ≠
      (ringCornerFold m (ringSideFrame G d.castSucc)).pos s := by
  exact edgePPPFolds_disjoint_of_endpoints_ne (by omega : 1 ≤ m)
    (bulkReverseEdgeFrame (ringSideFrame F c.castSucc)) (bulkReverseEdgeFrame (ringSideFrame G d.castSucc))
    1 1 (by omega) (by omega)
    (by rw [ringCorner_start_owner m hm F c, ringCorner_start_owner m hm G d]
        exact ringTerminalSite_ne_small_faces m hm F G hj c.succ d.succ 0 0)
    (by rw [ringCorner_start_owner m hm F c, ringCorner_end_owner m hm G d]
        exact ringTerminalSite_ne_small_faces m hm F G hj c.succ d.castSucc 0 1)
    (by rw [ringCorner_end_owner m hm F c, ringCorner_start_owner m hm G d]
        exact ringTerminalSite_ne_small_faces m hm F G hj c.castSucc d.succ 1 0)
    (by rw [ringCorner_end_owner m hm F c, ringCorner_end_owner m hm G d]
        exact ringTerminalSite_ne_small_faces m hm F G hj c.castSucc d.castSucc 1 1) r.rev s.rev

theorem ringFolds_disjoint_small_faces (m : ℕ) (hm : 3 ≤ m) (heven : m % 2 = 0)
    (F G : OctEdgeFrame) (hj : F.j ≠ G.j)
    (r s : Fin (dimerChain (3 * (m - 2))).length) :
    (ringFold m hm heven F).pos r ≠ (ringFold m hm heven G).pos s := by
  apply ringFold_property m hm heven F (fun x => x ≠ (ringFold m hm heven G).pos s) _ _ r
  · intro i a
    apply ringFold_property m hm heven G (fun x => (ringSideFold m hm (ringSideFrame F i)).pos a ≠ x) _ _ s
    · intro j b
      exact ringSideFolds_disjoint_small_faces m hm F G hj i j a b
    · intro d b
      exact ringSide_ne_foreign_corner m hm F G hj i d a b
  · intro c a
    apply ringFold_property m hm heven G
      (fun x => (ringCornerFold m (ringSideFrame F c.castSucc)).pos a ≠ x) _ _ s
    · intro j b
      exact (ringSide_ne_foreign_corner m hm G F hj.symm j c b a).symm
    · intro d b
      exact ringCorners_disjoint_small_faces m hm F G hj c d a b

end ProteinFolding.Tetrahedral.NearField
