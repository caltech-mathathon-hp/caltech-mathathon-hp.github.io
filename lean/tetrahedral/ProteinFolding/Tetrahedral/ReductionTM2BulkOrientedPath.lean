import ProteinFolding.Tetrahedral.ReductionTM2BulkComponentPath
import ProteinFolding.Tetrahedral.ReductionTM2BulkEndpointCorrect
import ProteinFolding.Tetrahedral.ReductionTM2PathOrientation

/-! Canonical orientation of the proof witnesses: the smaller endpoint index
comes first. These folds justify the already defined scan; they are not
computed by or supplied to its finite TM2. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkOrientedPath

set_option maxHeartbeats 2000000

open SimpleGraph

noncomputable def fold (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) : Fold (bulkFiniteGraph m) (bulkComponentLength m c) :=
  PathOrientation.orient (componentFold (bulkFiniteGraph m) c)
    (by have h := BulkComponentPath.length_ge_three m hm ha c; omega) (BulkIndexModel.index m)

theorem sites (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) (w : BulkVertex m) :
    (∃ i, (fold m hm ha c).pos i = w) ↔ (bulkFiniteGraph m).connectedComponentMk w = c := by
  rw [fold, PathOrientation.sites]
  exact componentFold_covers (bulkFiniteGraph m) (BulkComponentPath.degree_le_two m hm) c w

theorem first_degree (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) :
    (bulkFiniteGraph m).degree ((fold m hm ha c).pos (PathOrientation.first
      (by have h := BulkComponentPath.length_ge_three m hm ha c; omega))) = 1 := by
  exact PathOrientation.first_degree_eq (componentFold (bulkFiniteGraph m) c)
    (lt_of_lt_of_le (by decide : 0 < 3) (BulkComponentPath.length_ge_three m hm ha c))
    (BulkIndexModel.index m) (BulkComponentPath.first_degree m hm ha c) (BulkComponentPath.last_degree m hm ha c)

theorem last_degree (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) :
    (bulkFiniteGraph m).degree ((fold m hm ha c).pos (PathOrientation.last
      (by have h := BulkComponentPath.length_ge_three m hm ha c; omega))) = 1 := by
  exact PathOrientation.last_degree_eq (componentFold (bulkFiniteGraph m) c)
    (lt_of_lt_of_le (by decide : 0 < 3) (BulkComponentPath.length_ge_three m hm ha c))
    (BulkIndexModel.index m) (BulkComponentPath.first_degree m hm ha c) (BulkComponentPath.last_degree m hm ha c)

noncomputable def points (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) : ℕ → ℕ :=
  foldIndexPoint (bulkFiniteGraph m) (fold m hm ha c) (BulkIndexModel.index m)

theorem indexedPath (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) :
    BoundedWalk.IndexedPath BulkPredicate.predicate m (Grid.count m) (bulkComponentLength m c) (points m hm ha c) := by
  have hL := BulkComponentPath.length_ge_three m hm ha c
  exact indexedPath_of_fold (bulkFiniteGraph m) (by omega) (fold m hm ha c)
    (BulkComponentPath.degree_le_two m hm) (first_degree m hm ha c).le (last_degree m hm ha c).le
    (BulkIndexModel.index m) (BulkIndexModel.index_bound m) (BulkIndexModel.index_injective m)
    BulkPredicate.predicate m (BulkIndexModel.graph_model m)

theorem points_first (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) : points m hm ha c 0 =
    BulkIndexModel.index m ((fold m hm ha c).pos (PathOrientation.first
      (by have h := BulkComponentPath.length_ge_three m hm ha c; omega))) := by
  have hL : 0 < bulkComponentLength m c := by have h := BulkComponentPath.length_ge_three m hm ha c; omega
  simp only [points, foldIndexPoint, dif_pos hL, PathOrientation.first]

theorem points_last (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) : points m hm ha c (bulkComponentLength m c - 1) =
    BulkIndexModel.index m ((fold m hm ha c).pos (PathOrientation.last
      (by have h := BulkComponentPath.length_ge_three m hm ha c; omega))) := by
  have hL : bulkComponentLength m c - 1 < bulkComponentLength m c := by
    have h := BulkComponentPath.length_ge_three m hm ha c
    omega
  simp only [points, foldIndexPoint, dif_pos hL, PathOrientation.last]

theorem ordered (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) :
    points m hm ha c 0 < points m hm ha c (bulkComponentLength m c - 1) := by
  rw [points_first, points_last]
  exact PathOrientation.ordered (componentFold (bulkFiniteGraph m) c)
    (by change 2 ≤ bulkComponentLength m c; have h := BulkComponentPath.length_ge_three m hm ha c; omega)
    (BulkIndexModel.index m) (BulkIndexModel.index_injective m)

theorem endpoint (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) :
    BulkPredicate.endpoint (m, (points m hm ha c 0, 0)) = true := by
  rw [points_first]
  let u := (fold m hm ha c).pos (PathOrientation.first
    (by have h := BulkComponentPath.length_ge_three m hm ha c; omega))
  apply (BulkPredicate.endpoint_correct m (BulkIndexModel.index m u) 0 u.val (BulkIndexModel.point_index m u)).2
  exact (bulkFinite_degree m u).symm.trans (first_degree m hm ha c)

theorem emitted (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) :
    BulkScan.emit (m, points m hm ha c 0) =
      [(bulkComponentLength m c, (BulkPredicate.colour (m, (points m hm ha c 0, 0)),
        BulkPredicate.colour (m, (points m hm ha c (bulkComponentLength m c - 1), 0))))] :=
  BulkScan.emit_of_path m (bulkComponentLength m c) (points m hm ha c)
    (indexedPath m hm ha c) (endpoint m hm ha c) (ordered m hm ha c)

end ProteinFolding.Tetrahedral.ReductionTM2.BulkOrientedPath
