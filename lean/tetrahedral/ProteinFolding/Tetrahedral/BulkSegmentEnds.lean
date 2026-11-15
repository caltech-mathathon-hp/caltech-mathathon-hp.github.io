import ProteinFolding.Tetrahedral.BulkSegments
import ProteinFolding.Tetrahedral.FinitePathCoverEnds

/-! Every actual rung segment has a spanning path. Its endpoints either
are leaves of the full cover or carry a genuine non-rung cover joint. -/

namespace ProteinFolding.Tetrahedral

theorem bulkSegment_spanning_path (m : ℕ) (p : BulkVertex m) :
    ∃ a b : BulkVertex m, ∃ w : (bulkSegmentGraph m).Walk a b,
      w.IsPath ∧ (∀ q, q ∈ w.support ↔ (bulkSegmentGraph m).Reachable p q) ∧
      (bulkSegmentGraph m).degree a ≤ 1 ∧ (bulkSegmentGraph m).degree b ≤ 1 := by
  obtain ⟨w⟩ := exists_maximalComponentPath (bulkSegmentGraph m) p
  exact ⟨w.start, w.finish, w.walk, w.isPath,
    w.support_iff_reachable (bulkSegmentGraph m) (bulkSegmentGraph_degree_le_two m),
    w.start_degree_le_one (bulkSegmentGraph m) (bulkSegmentGraph_degree_le_two m)
      (bulkSegmentGraph_acyclic m),
    w.finish_degree_le_one (bulkSegmentGraph m) (bulkSegmentGraph_degree_le_two m)
      (bulkSegmentGraph_acyclic m)⟩

theorem finite_graph_joint_of_degree_lt {V : Type} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (p : V)
    (hlt : H.degree p < G.degree p) : ∃ q : V, G.Adj p q ∧ ¬H.Adj p q := by
  classical
  by_contra hnone
  have hsub : G.neighborFinset p ⊆ H.neighborFinset p := by
    intro q hq
    have hadj := (G.mem_neighborFinset p q).mp hq
    apply (H.mem_neighborFinset p q).mpr
    by_contra hnot
    exact hnone ⟨q, hadj, hnot⟩
  have hcard := Finset.card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at hcard
  omega

theorem bulkSegment_endpoint_joint (m : ℕ) (p : BulkVertex m)
    (hcover : 2 ≤ (bulkFiniteGraph m).degree p) (hsegment : (bulkSegmentGraph m).degree p ≤ 1) :
    ∃ q : BulkVertex m, (bulkFiniteGraph m).Adj p q ∧ ¬(bulkRungGraph m).Adj p.val q.val := by
  obtain ⟨q, hq, hnot⟩ := finite_graph_joint_of_degree_lt (bulkFiniteGraph m) (bulkSegmentGraph m) p (by omega)
  exact ⟨q, hq, fun hRung => hnot ⟨hq, hRung⟩⟩

theorem bulkCover_nonrung_joint_cases (m : ℕ) {p q : Site}
    (h : (bulkCoverGraph m).Adj p q) (hnr : ¬(bulkRungGraph m).Adj p q) :
    bulkPatchAdded m p q ∨ bulkMerge m p q ∨ bulkMerge m q p := by
  rcases h.2.2 with hpatch | ⟨hrung | hmerge | hmerge, _⟩
  · exact Or.inl hpatch
  · exact (hnr hrung).elim
  · exact Or.inr (Or.inl hmerge)
  · exact Or.inr (Or.inr hmerge)

end ProteinFolding.Tetrahedral
