import ProteinFolding.Tetrahedral.BulkNearJointCoverage
import ProteinFolding.Tetrahedral.BulkEscapeFarCases
import ProteinFolding.Tetrahedral.BulkFarZUniform
import ProteinFolding.Tetrahedral.BulkXJointInvariants
import ProteinFolding.Tetrahedral.BulkXInwardUniform
import ProteinFolding.Tetrahedral.BulkLongXAxes
import ProteinFolding.Tetrahedral.BulkFarXAlpha
import ProteinFolding.Tetrahedral.BulkFarJointGeometry
import ProteinFolding.Tetrahedral.BulkSegmentEnds
import ProteinFolding.Tetrahedral.BulkDamagedParametrization
import ProteinFolding.Tetrahedral.BulkEscapeTypes

/-! Exhaustive actual-joint classification. A near or Z joint already
escapes; every remaining joint supplies the concrete uniform X invariants. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulkNearCandidate_joint_escape (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hOne : 1 ≤ m) (ht : t ≤ 9)
    (hd : bulkEdgeCandidate m F t odd d hOne ∈ bulkDamaged m) (p q : BulkVertex m)
    (hcover : (bulkFiniteGraph m).Adj p q)
    (hmeta : (p.val = bulkEdgeCandidate m F t odd d hOne ∧ bulkMerge m (bulkEdgeCandidate m F t odd d hOne) q.val) ∨
      (q.val = bulkEdgeCandidate m F t odd d hOne ∧ bulkMerge m (bulkEdgeCandidate m F t odd d hOne) p.val)) :
    BulkEscapes m p := by
  rcases hmeta with ⟨hp, _⟩ | ⟨hq, hmerge⟩
  · exact bulkNearEdgeCandidate_escape m hm F ⟨t, by omega⟩ odd d p hp (by rwa [hp])
  · obtain ⟨e, he⟩ := (adj_iff_exists_step _ p.val).mp (bulkMerge_adj m hmerge)
    apply bulkNearJoint_escape m hm F ⟨t, by omega⟩ odd d e p he.symm hd
    · exact (bulkMerge_rho m hmerge).symm
    · rw [← hq]
      exact bulkCoverBond_symm m hcover

theorem bulkCandidate_joint_escape_or_XData (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hOne : 1 ≤ m)
    (hvalid : match odd with | false => t < m | true => t + 2 ≤ m)
    (hd : bulkEdgeCandidate m F t odd d hOne ∈ bulkDamaged m) (p q : BulkVertex m)
    (hcover : (bulkFiniteGraph m).Adj p q)
    (hmeta : (p.val = bulkEdgeCandidate m F t odd d hOne ∧ bulkMerge m (bulkEdgeCandidate m F t odd d hOne) q.val) ∨
      (q.val = bulkEdgeCandidate m F t odd d hOne ∧ bulkMerge m (bulkEdgeCandidate m F t odd d hOne) p.val)) :
    BulkEscapes m p ∨ BulkXJointData m p q :=
  bulkCandidate_joint_escape_or_XData_of_near m hm F t
    (bulkNearCandidate_joint_escape m hm) odd d hOne hvalid hd p q hcover hmeta

theorem bulkJoint_escape_or_XData (m : ℕ) (hm : 50 ≤ m) (p q : BulkVertex m)
    (hcover : (bulkFiniteGraph m).Adj p q) (hnr : ¬(bulkRungGraph m).Adj p.val q.val) :
    BulkEscapes m p ∨ BulkXJointData m p q := by
  have hOne : 1 ≤ m := by omega
  rcases bulkCover_nonrung_joint_cases m hcover hnr with hpatch | hmerge | hmerge
  · exact Or.inl (bulkPatchSupport_escape m hm p (bulkPatchSupport_added m hpatch).1)
  · change bulkMerge m p.val q.val at hmerge
    obtain ⟨F, t, d, heven | hodd⟩ := bulkDamaged_candidate_exists hOne p.val hmerge.1
    · obtain ⟨hvalid, hp⟩ := heven
      rw [hp] at hmerge
      exact bulkCandidate_joint_escape_or_XData m hm F t false d hOne hvalid hmerge.1 p q hcover (Or.inl ⟨hp, hmerge⟩)
    · obtain ⟨hvalid, hp⟩ := hodd
      rw [hp] at hmerge
      exact bulkCandidate_joint_escape_or_XData m hm F t true d hOne hvalid hmerge.1 p q hcover (Or.inl ⟨hp, hmerge⟩)
  · change bulkMerge m q.val p.val at hmerge
    obtain ⟨F, t, d, heven | hodd⟩ := bulkDamaged_candidate_exists hOne q.val hmerge.1
    · obtain ⟨hvalid, hq⟩ := heven
      rw [hq] at hmerge
      exact bulkCandidate_joint_escape_or_XData m hm F t false d hOne hvalid hmerge.1 p q hcover (Or.inr ⟨hq, hmerge⟩)
    · obtain ⟨hvalid, hq⟩ := hodd
      rw [hq] at hmerge
      exact bulkCandidate_joint_escape_or_XData m hm F t true d hOne hvalid hmerge.1 p q hcover (Or.inr ⟨hq, hmerge⟩)

end ProteinFolding.Tetrahedral
