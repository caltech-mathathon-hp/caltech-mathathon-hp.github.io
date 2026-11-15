import ProteinFolding.Tetrahedral.ReductionTM2BulkIndexModel
import ProteinFolding.Tetrahedral.ReductionTM2IndexPath
import ProteinFolding.Tetrahedral.ReductionTM2BulkScanPath
import ProteinFolding.Tetrahedral.BulkGoodDegreeSplit
import ProteinFolding.Tetrahedral.BulkDegree
import ProteinFolding.Tetrahedral.ReductionTM2ComponentEnds

/-! Actual uniform degree bounds supply the semantic component-path witness
for the explicit index walker. Acyclicity is the remaining graph input here;
no degree certificate or computability premise is accepted. -/

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkComponentPath

set_option maxHeartbeats 2000000

open SimpleGraph

theorem degree_le_two (m : ℕ) (hm : 27 ≤ m) : ∀ u : BulkVertex m, (bulkFiniteGraph m).degree u ≤ 2 := by
  intro u
  rw [bulkFinite_degree]
  exact bulkCoverNeighbours_card_le_two m (by omega) u.val

theorem degree_positive (m : ℕ) (hm : 27 ≤ m) : ∀ u : BulkVertex m, 1 ≤ (bulkFiniteGraph m).degree u := by
  intro u
  rw [bulkFinite_degree]
  exact bulkCover_minimum_degree_split m hm u.val u.property

theorem no_leaf_pair (m : ℕ) (hm : 27 ≤ m) :
    ∀ a b : BulkVertex m, (bulkFiniteGraph m).Adj a b → (bulkFiniteGraph m).degree a = 1 →
      (bulkFiniteGraph m).degree b ≠ 1 := by
  intro a b hab ha hb
  exact bulkCover_no_leaf_pair_split m hm hab (by simpa only [bulkFinite_degree] using ha)
    (by simpa only [bulkFinite_degree] using hb)

theorem length_ge_three (m : ℕ) (hm : 27 ≤ m) (hacyclic : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) : 3 ≤ bulkComponentLength m c :=
  componentPath_vertex_count_ge_three (bulkFiniteGraph m) (degree_le_two m hm) hacyclic
    (degree_positive m hm) (no_leaf_pair m hm) c

theorem first_degree (m : ℕ) (hm : 27 ≤ m) (hacyclic : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) :
    (bulkFiniteGraph m).degree ((componentFold (bulkFiniteGraph m) c).pos
      ⟨0, by have h := length_ge_three m hm hacyclic c; change 0 < bulkComponentLength m c; omega⟩) = 1 := by
  have he := componentFold_end_degrees (bulkFiniteGraph m) (degree_le_two m hm) hacyclic
    (degree_positive m hm) c
  rw [componentFold_first_pos]
  exact he.1

theorem last_degree (m : ℕ) (hm : 27 ≤ m) (hacyclic : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) :
    (bulkFiniteGraph m).degree ((componentFold (bulkFiniteGraph m) c).pos
      ⟨bulkComponentLength m c - 1, by have h := length_ge_three m hm hacyclic c; change _ < bulkComponentLength m c; omega⟩) = 1 := by
  have he := componentFold_end_degrees (bulkFiniteGraph m) (degree_le_two m hm) hacyclic
    (degree_positive m hm) c
  simp only [bulkComponentLength]
  rw [componentFold_last_sub_pos]
  exact he.2

noncomputable def points (m : ℕ) (c : (bulkFiniteGraph m).ConnectedComponent) : ℕ → ℕ :=
  foldIndexPoint (bulkFiniteGraph m) (componentFold (bulkFiniteGraph m) c) (BulkIndexModel.index m)

theorem indexedPath (m : ℕ) (hm : 27 ≤ m) (hacyclic : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) :
    BoundedWalk.IndexedPath BulkPredicate.predicate m (Grid.count m) (bulkComponentLength m c) (points m c) := by
  have hL := length_ge_three m hm hacyclic c
  exact indexedPath_of_fold (bulkFiniteGraph m) (by change 2 ≤ bulkComponentLength m c; omega) (componentFold (bulkFiniteGraph m) c)
    (degree_le_two m hm) (first_degree m hm hacyclic c).le (last_degree m hm hacyclic c).le
    (BulkIndexModel.index m) (BulkIndexModel.index_bound m) (BulkIndexModel.index_injective m)
    BulkPredicate.predicate m (BulkIndexModel.graph_model m)

theorem computed_length (m : ℕ) (hm : 27 ≤ m) (hacyclic : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) :
    (BulkScan.record (m, points m c 0)).1 = bulkComponentLength m c := by
  rw [BulkScan.record_of_path m (bulkComponentLength m c) (points m c) (indexedPath m hm hacyclic c)]

end ProteinFolding.Tetrahedral.ReductionTM2.BulkComponentPath
