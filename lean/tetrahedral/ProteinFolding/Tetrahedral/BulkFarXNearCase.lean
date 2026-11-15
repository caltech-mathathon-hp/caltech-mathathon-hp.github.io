import ProteinFolding.Tetrahedral.BulkFarXAlpha
import ProteinFolding.Tetrahedral.BulkSegments

/-! The A4 range belongs to the existing near-candidate table, with
the even/odd reversed parameter stated explicitly. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulkX_joint_large_alpha_near (m : ℕ) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hm : 1 ≤ m) (hX : BulkXEdgeFrame F)
    (hd : bulkEdgeCandidate m F t odd d hm ∈ bulkDamaged m) (p : Site)
    (hp : p = bulkEdgeCandidate m F t odd d hm ∨
      tetrahedralLattice.Adj (bulkEdgeCandidate m F t odd d hm) p)
    (hlarge : octRadius m - 36 < |bulkAlpha m p|) :
    t ≤ 9 ∨ (if odd then m - 2 - t else m - 1 - t) ≤ 9 := by
  by_cases ht : t ≤ 9
  · exact Or.inl ht
  right
  by_contra hr
  have ht' : 10 ≤ t := by omega
  cases odd
  · change ¬m - 1 - t ≤ 9 at hr
    have htm : t + 11 ≤ m := by omega
    have hbound := bulkFarX_joint_alpha_bound m F t false d hm ht'
      (by change t + 11 ≤ m; exact htm) hX hd p hp
    omega
  · change ¬m - 2 - t ≤ 9 at hr
    have htm : t + 12 ≤ m := by omega
    have hbound := bulkFarX_joint_alpha_bound m F t true d hm ht'
      (by change t + 12 ≤ m; exact htm) hX hd p hp
    omega

theorem bulkX_segment_large_alpha_near (m : ℕ) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hm : 1 ≤ m) (hX : BulkXEdgeFrame F)
    (hd : bulkEdgeCandidate m F t odd d hm ∈ bulkDamaged m) (p q : BulkVertex m)
    (hp : p.val = bulkEdgeCandidate m F t odd d hm ∨
      tetrahedralLattice.Adj (bulkEdgeCandidate m F t odd d hm) p.val)
    (hreach : (bulkSegmentGraph m).Reachable q p)
    (hlarge : octRadius m - 36 < |bulkAlpha m q.val|) :
    t ≤ 9 ∨ (if odd then m - 2 - t else m - 1 - t) ≤ 9 := by
  have hα := bulkSegment_alpha m hreach
  apply bulkX_joint_large_alpha_near m F t odd d hm hX hd p.val hp
  rwa [hα]

end ProteinFolding.Tetrahedral
