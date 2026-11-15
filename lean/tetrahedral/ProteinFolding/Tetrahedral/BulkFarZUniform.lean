import ProteinFolding.Tetrahedral.BulkFarZEscape
import ProteinFolding.Tetrahedral.BulkFarZNearEscape
import ProteinFolding.Tetrahedral.BulkEdgeReversal

/-! Class-Z joint escape covers every index whose two orientations
are outside the original near range0..9. -/

namespace ProteinFolding.Tetrahedral

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem bulkZ_endpoint_escape_transition (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hOne : 1 ≤ m) (ht : 10 ≤ t) (ht' : t ≤ 12) (hZ : BulkZEdgeFrame F)
    (hd : bulkEdgeCandidate m F t odd d hOne ∈ bulkDamaged m) (p : BulkVertex m)
    (hp : p.val = bulkEdgeCandidate m F t odd d hOne ∨ bulkMerge m (bulkEdgeCandidate m F t odd d hOne) p.val) :
    ∃ q : BulkVertex m, (bulkFiniteGraph m).Reachable p q ∧
      bulkSegmentPotential m p < bulkSegmentPotential m q := by
  let j : Fin 3 := ⟨t - 10, by omega⟩
  have heq : t = bulkFarZNearT j := by dsimp [bulkFarZNearT, j]; omega
  rw [heq] at hd hp
  exact bulkFarZNear_endpoint_escape m hm F j odd d hOne hZ hd p hp

theorem bulkZ_endpoint_escape_all_far (m : ℕ) (hm : 50 ≤ m) (F : OctEdgeFrame) (t : ℕ)
    (odd : Bool) (d : Fin 4) (hOne : 1 ≤ m) (ht : 10 ≤ t)
    (hrev : 10 ≤ if odd then m - 2 - t else m - 1 - t) (hZ : BulkZEdgeFrame F)
    (hd : bulkEdgeCandidate m F t odd d hOne ∈ bulkDamaged m) (p : BulkVertex m)
    (hp : p.val = bulkEdgeCandidate m F t odd d hOne ∨ bulkMerge m (bulkEdgeCandidate m F t odd d hOne) p.val) :
    ∃ q : BulkVertex m, (bulkFiniteGraph m).Reachable p q ∧
      bulkSegmentPotential m p < bulkSegmentPotential m q := by
  by_cases hnear : t ≤ 12
  · exact bulkZ_endpoint_escape_transition m hm F t odd d hOne ht hnear hZ hd p hp
  have ht13 : 13 ≤ t := by omega
  by_cases hfar : t + 14 ≤ m
  · exact bulkFarZ_endpoint_escape m t F odd d hOne ht13 hfar hZ hd p hp
  have hZrev : BulkZEdgeFrame (bulkReverseEdgeFrame F) := by
    simpa only [BulkZEdgeFrame, bulkReverseEdgeFrame] using hZ
  cases odd
  · change 10 ≤ m - 1 - t at hrev
    have heq := bulkEdgeCandidate_reverse_even hOne F t (by omega) d
    rw [heq] at hd hp
    exact bulkZ_endpoint_escape_transition m hm (bulkReverseEdgeFrame F) (m - 1 - t) false d hOne
      hrev (by omega) hZrev hd p hp
  · change 10 ≤ m - 2 - t at hrev
    have heq := bulkEdgeCandidate_reverse_odd hOne F t (by omega) d
    rw [heq] at hd hp
    exact bulkZ_endpoint_escape_transition m hm (bulkReverseEdgeFrame F) (m - 2 - t) true d hOne
      hrev (by omega) hZrev hd p hp

end ProteinFolding.Tetrahedral
