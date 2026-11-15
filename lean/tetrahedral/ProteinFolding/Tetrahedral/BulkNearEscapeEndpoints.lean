import ProteinFolding.Tetrahedral.BulkNearEscapeData

/-! Eight near-vertex exceptional segments have explicit walks to actual ends,
uniformly in every size needed by the construction. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem bulkNearEscape_start_mem (i : Fin 10) :
    bulkNearEscapeStart i ∈ bulkNearEscapePath i := by
  revert i
  decide

theorem bulkNearEscape_finish_mem (i : Fin 10) :
    bulkNearEscapeFinish i ∈ bulkNearEscapePath i := by
  revert i
  decide

theorem bulkNearEscape_uniform_reachable (m : ℕ) (hm : 21 ≤ m) (i : Fin 10) :
    (bulkCoverGraph m).Reachable
      (bulkReanchorSite 50 m (bulkNearEscapeVertex i) (bulkNearEscapeStart i))
      (bulkReanchorSite 50 m (bulkNearEscapeVertex i) (bulkNearEscapeFinish i)) :=
  bulkFastCoverChain_vertex_reachable 50 m (bulkNearEscapeVertex i) 14
    (bulkNearEscapePath i) (by decide) (by omega) (bulkNearEscape_reference_box i)
    (bulkNearEscape_reference_chain i) _ _ (bulkNearEscape_start_mem i) (bulkNearEscape_finish_mem i)

theorem bulkNearEscape_uniform_end (m : ℕ) (hm : 21 ≤ m) (i : Fin 10)
    (hi : bulkNearEscapeHasEnd i = true) :
    (bulkCoverNeighbours m
      (bulkReanchorSite 50 m (bulkNearEscapeVertex i) (bulkNearEscapeFinish i))).card ≤ 1 := by
  have hcard := bulkReanchor_coverNeighbours_card 50 m (bulkNearEscapeVertex i) 14
    (bulkNearEscapeFinish i) (by decide) hm
    (bulkNearEscape_reference_box i _ (bulkNearEscape_finish_mem i))
  rw [hcard, bulkCoverNeighbours_fast_card]
  exact bulkNearEscape_reference_end i hi

theorem bulkNearEscape_eight_escape_to_end (m : ℕ) (hm : 21 ≤ m) (i : Fin 10)
    (hi : bulkNearEscapeHasEnd i = true) :
    ∃ q, (bulkCoverGraph m).Reachable
      (bulkReanchorSite 50 m (bulkNearEscapeVertex i) (bulkNearEscapeStart i)) q ∧
      (bulkCoverNeighbours m q).card ≤ 1 :=
  ⟨_, bulkNearEscape_uniform_reachable m hm i, bulkNearEscape_uniform_end m hm i hi⟩

end ProteinFolding.Tetrahedral
