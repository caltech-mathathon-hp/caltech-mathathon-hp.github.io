import ProteinFolding.Tetrahedral.BulkFarZUniform
import ProteinFolding.Tetrahedral.BulkXJointInvariants
import ProteinFolding.Tetrahedral.BulkXInwardUniform
import ProteinFolding.Tetrahedral.BulkLongXAxes
import ProteinFolding.Tetrahedral.BulkFarXAlpha
import ProteinFolding.Tetrahedral.BulkFarJointGeometry
import ProteinFolding.Tetrahedral.BulkSegmentEnds
import ProteinFolding.Tetrahedral.BulkEscapeTypes

/-! The far candidate classification is independent of the finite near tables.
Its explicit near-escape provider is discharged by BulkEscapeCases. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulkCandidate_joint_escape_or_XData_of_near (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (hnearEscape : ∀ (G : OctEdgeFrame) (s : ℕ) (parity : Bool) (e : Fin 4) (hM : 1 ≤ m),
      s ≤ 9 → bulkEdgeCandidate m G s parity e hM ∈ bulkDamaged m →
      ∀ a b : BulkVertex m, (bulkFiniteGraph m).Adj a b →
        ((a.val = bulkEdgeCandidate m G s parity e hM ∧ bulkMerge m (bulkEdgeCandidate m G s parity e hM) b.val) ∨
          (b.val = bulkEdgeCandidate m G s parity e hM ∧ bulkMerge m (bulkEdgeCandidate m G s parity e hM) a.val)) →
        BulkEscapes m a)
    (odd : Bool) (d : Fin 4) (hOne : 1 ≤ m)
    (hvalid : match odd with | false => t < m | true => t + 2 ≤ m)
    (hd : bulkEdgeCandidate m F t odd d hOne ∈ bulkDamaged m) (p q : BulkVertex m)
    (hcover : (bulkFiniteGraph m).Adj p q)
    (hmeta : (p.val = bulkEdgeCandidate m F t odd d hOne ∧ bulkMerge m (bulkEdgeCandidate m F t odd d hOne) q.val) ∨
      (q.val = bulkEdgeCandidate m F t odd d hOne ∧ bulkMerge m (bulkEdgeCandidate m F t odd d hOne) p.val)) :
    BulkEscapes m p ∨ BulkXJointData m p q := by
  by_cases hnear : t ≤ 9
  · exact Or.inl (hnearEscape F t odd d hOne hnear hd p q hcover hmeta)
  have ht : 10 ≤ t := by omega
  by_cases hreverseNear : (if odd then m - 2 - t else m - 1 - t) ≤ 9
  · left
    cases odd
    · change t < m at hvalid
      change m - 1 - t ≤ 9 at hreverseNear
      have heq := bulkEdgeCandidate_reverse_even hOne F t hvalid d
      rw [heq] at hd hmeta
      exact hnearEscape (bulkReverseEdgeFrame F) _ false d hOne hreverseNear hd p q hcover hmeta
    · change t + 2 ≤ m at hvalid
      change m - 2 - t ≤ 9 at hreverseNear
      have heq := bulkEdgeCandidate_reverse_odd hOne F t hvalid d
      rw [heq] at hd hmeta
      exact hnearEscape (bulkReverseEdgeFrame F) _ true d hOne hreverseNear hd p q hcover hmeta
  have hrev : 10 ≤ if odd then m - 2 - t else m - 1 - t := by omega
  have hmargin : t + 11 ≤ m := by cases odd <;> simp at hrev <;> omega
  have hmargin' : t + (if odd then 12 else 11) ≤ m := by cases odd <;> simp at hrev ⊢ <;> omega
  have hpEnd : p.val = bulkEdgeCandidate m F t odd d hOne ∨ bulkMerge m (bulkEdgeCandidate m F t odd d hOne) p.val := by
    rcases hmeta with ⟨hp, _⟩ | ⟨_, hmerge⟩
    · exact Or.inl hp
    · exact Or.inr hmerge
  rcases bulkFarEdge_damaged_plane m F t odd d hOne ht hmargin hd with hX | hZ
  · right
    have hpAdj := hpEnd.imp id (bulkMerge_adj m)
    have hbox := bulkEdgeCandidate_joint_in_anchor_box hOne F t odd d p.val hpAdj
    have hx := bulkEdgeCandidate_joint_x_bound hOne F t odd d hX p.val hpAdj
    have hα := bulkFarX_joint_alpha_bound m F t odd d hOne ht hmargin' hX hd p.val hpAdj
    have hin := bulkX_joint_inward_all_far m hm F t odd d hOne ht hrev hX hd p.val hpEnd
    have haxes := bulkFarXEdgeBox_axes_separated m F t p.val hOne hX ht hmargin hbox
    have hsigns := bulkFarXEdgeBox_adj_signs m F t p.val q.val hOne hX ht hmargin hbox (bulkCoverBond_adj m hcover)
    rcases hmeta with ⟨hp, hmerge⟩ | ⟨hq, hmerge⟩
    · have hi := bulkXJoint_uniform_invariants m F t odd d hOne ht hmargin hX q.val hmerge
      rw [← hp] at hi hmerge
      exact ⟨hcover, hi.1, hi.2.1, hin, hx, hα, haxes, hsigns, Or.inl hmerge⟩
    · have hi := bulkXJoint_uniform_invariants m F t odd d hOne ht hmargin hX p.val hmerge
      rw [← hq] at hi hmerge
      exact ⟨hcover, hi.2.2.1, hi.2.2.2, hin, hx, hα, haxes, hsigns, Or.inr hmerge⟩
  · obtain ⟨r, hpr, hlt⟩ := bulkZ_endpoint_escape_all_far m hm F t odd d hOne ht hrev hZ hd p hpEnd
    exact Or.inl ⟨r, hpr, Or.inr hlt⟩

end ProteinFolding.Tetrahedral
