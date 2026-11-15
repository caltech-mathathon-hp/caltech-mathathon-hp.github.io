import ProteinFolding.Tetrahedral.ReductionTM2BulkScan
import ProteinFolding.Tetrahedral.ReductionTM2WalkBounds

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkScan

theorem walk_of_path (m L : ℕ) (v : ℕ → ℕ)
    (hp : BoundedWalk.IndexedPath BulkPredicate.predicate m (Grid.count m) L v) :
    walk (m, v 0) = BoundedWalk.pathFinish m (Grid.count m) L v :=
  hp.iterate_bound

theorem record_of_path (m L : ℕ) (v : ℕ → ℕ)
    (hp : BoundedWalk.IndexedPath BulkPredicate.predicate m (Grid.count m) L v) :
    record (m, v 0) = (L, (BulkPredicate.colour (m, (v 0, 0)),
      BulkPredicate.colour (m, (v (L - 1), 0)))) := by
  rw [record, walk_of_path m L v hp]
  rfl

theorem canonical_of_path (m L : ℕ) (v : ℕ → ℕ)
    (hp : BoundedWalk.IndexedPath BulkPredicate.predicate m (Grid.count m) L v) :
    canonical (m, v 0) = (BulkPredicate.endpoint (m, (v 0, 0)) && decide (v 0 < v (L - 1))) := by
  rw [canonical, walk_of_path m L v hp]
  rfl

theorem emit_of_path (m L : ℕ) (v : ℕ → ℕ)
    (hp : BoundedWalk.IndexedPath BulkPredicate.predicate m (Grid.count m) L v)
    (he : BulkPredicate.endpoint (m, (v 0, 0)) = true) (horder : v 0 < v (L - 1)) :
    emit (m, v 0) = [(L, (BulkPredicate.colour (m, (v 0, 0)),
      BulkPredicate.colour (m, (v (L - 1), 0))))] := by
  rw [emit, canonical_of_path m L v hp]
  simp only [he, horder, decide_true, Bool.and_self, ↓reduceIte]
  rw [record_of_path m L v hp]

theorem emit_of_path_reversed_order (m L : ℕ) (v : ℕ → ℕ)
    (hp : BoundedWalk.IndexedPath BulkPredicate.predicate m (Grid.count m) L v)
    (horder : v (L - 1) ≤ v 0) : emit (m, v 0) = [] := by
  rw [emit, canonical_of_path m L v hp]
  have hn : ¬v 0 < v (L - 1) := by omega
  simp only [hn, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

end ProteinFolding.Tetrahedral.ReductionTM2.BulkScan
