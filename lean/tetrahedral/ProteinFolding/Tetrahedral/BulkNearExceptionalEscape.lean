import ProteinFolding.Tetrahedral.BulkNearEscapeEndpoints
import ProteinFolding.Tetrahedral.BulkNearAscending
import ProteinFolding.Tetrahedral.BulkGraphReachability

/-! Each of the ten explicitly listed near-vertex exceptions has an actual
cover route to an end or to a segment with larger potential. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem bulkNearEscape_reference_inside (i : Fin 10) :
    bulkFastInterior 50 (bulkNearEscapeStart i) ∧ bulkFastInterior 50 (bulkNearEscapeFinish i) := by
  revert i
  decide

def bulkNearEscapeStartView (m : ℕ) (hm : 21 ≤ m) (i : Fin 10) : BulkVertex m :=
  ⟨bulkReanchorSite 50 m (bulkNearEscapeVertex i) (bulkNearEscapeStart i),
    (bulkReanchor_interior_iff 50 m (bulkNearEscapeVertex i) 14 _ (by decide) (by omega)
      (bulkNearEscape_reference_box i _ (bulkNearEscape_start_mem i))).mpr
        ((bulkInterior_fast_iff 50 _).mpr (bulkNearEscape_reference_inside i).1)⟩

def bulkNearEscapeFinishView (m : ℕ) (hm : 21 ≤ m) (i : Fin 10) : BulkVertex m :=
  ⟨bulkReanchorSite 50 m (bulkNearEscapeVertex i) (bulkNearEscapeFinish i),
    (bulkReanchor_interior_iff 50 m (bulkNearEscapeVertex i) 14 _ (by decide) (by omega)
      (bulkNearEscape_reference_box i _ (bulkNearEscape_finish_mem i))).mpr
        ((bulkInterior_fast_iff 50 _).mpr (bulkNearEscape_reference_inside i).2)⟩

theorem bulkNearEscape_finite_reachable (m : ℕ) (hm : 21 ≤ m) (i : Fin 10) :
    (bulkFiniteGraph m).Reachable (bulkNearEscapeStartView m hm i) (bulkNearEscapeFinishView m hm i) :=
  (bulkFinite_reachable_iff m _ _).mpr (bulkNearEscape_uniform_reachable m hm i)

theorem bulkNearExceptional_escape (m : ℕ) (hm : 21 ≤ m) (i : Fin 10) :
    ∃ q : BulkVertex m,
      (bulkFiniteGraph m).Reachable (bulkNearEscapeStartView m hm i) q ∧
      ((bulkFiniteGraph m).degree q ≤ 1 ∨
        bulkSegmentPotential m (bulkNearEscapeStartView m hm i) < bulkSegmentPotential m q) := by
  refine ⟨bulkNearEscapeFinishView m hm i, bulkNearEscape_finite_reachable m hm i, ?_⟩
  have hcases : bulkNearEscapeHasEnd i = true ∨ i = 1 ∨ i = 7 := by
    revert i
    decide
  rcases hcases with hi | rfl | rfl
  · left
    rw [bulkFinite_degree]
    exact bulkNearEscape_uniform_end m hm i hi
  · right
    change bulkSegmentPotential m (bulkNearAscendingView m (by omega) 0) <
      bulkSegmentPotential m (bulkNearAscendingView m (by omega) 1)
    exact bulkNearAscending_pair_strict m (by omega) 0
  · right
    change bulkSegmentPotential m (bulkNearAscendingView m (by omega) 2) <
      bulkSegmentPotential m (bulkNearAscendingView m (by omega) 3)
    exact bulkNearAscending_pair_strict m (by omega) 1

end ProteinFolding.Tetrahedral
