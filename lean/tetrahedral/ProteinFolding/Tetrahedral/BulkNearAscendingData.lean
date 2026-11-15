import ProteinFolding.Tetrahedral.BulkSegmentWitnessValues

namespace ProteinFolding.Tetrahedral

def bulkNearAscendingPoints (j : Fin 4) : List Site :=
  match j.val with
  | 0 => [⟨![-2, 4, -2], by decide⟩,
      ⟨![-1, 5, -1], by decide⟩,
      ⟨![-2, 6, 0], by decide⟩,
      ⟨![-1, 7, 1], by decide⟩]
  | 1 => [⟨![-1, 5, 3], by decide⟩,
      ⟨![0, 6, 2], by decide⟩]
  | 2 => [⟨![-2, 192, 2], by decide⟩,
      ⟨![-1, 191, 1], by decide⟩]
  | _ => [⟨![-1, 193, -1], by decide⟩,
      ⟨![0, 192, 0], by decide⟩]

def bulkNearAscendingSupport (j : Fin 4) : Finset Site := (bulkNearAscendingPoints j).toFinset

def bulkNearAscendingRoot (j : Fin 4) : Site :=
  (bulkNearAscendingPoints j).headD (octVertexSite 50 0 false)

def bulkNearAscendingRank (j : Fin 4) (p : Site) : ℕ := (bulkNearAscendingPoints j).idxOf p

def bulkNearAscendingVertex (j : Fin 4) : Fin 6 := if j.val < 2 then 1 else 4

def bulkNearAscendingXhat (j : Fin 4) : ℤ := if j.val % 2 = 0 then -3 else -1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem bulkNearAscending_reference_certificate (j : Fin 4) :
    BulkSegmentFiniteCheck 50 (bulkNearAscendingSupport j)
      (bulkNearAscendingRoot j) (bulkNearAscendingRank j) := by
  revert j
  decide

theorem bulkNearAscending_reference_box (j : Fin 4) :
    ∀ p ∈ bulkNearAscendingSupport j, InBulkVertexBox 50 (bulkNearAscendingVertex j) 11 p := by
  revert j
  unfold InBulkVertexBox
  decide

theorem bulkNearAscending_reference_no_row (j : Fin 4) :
    ∀ p ∈ bulkNearAscendingSupport j, ¬(bulkFastDamaged 50 p ∧ bulkZ p = 0) := by
  revert j
  decide

theorem bulkNearAscending_reference_alpha (j : Fin 4) :
    bulkAlpha 50 (bulkNearAscendingRoot j) = if j.val < 2 then 91 else 93 := by
  revert j
  decide

end ProteinFolding.Tetrahedral
