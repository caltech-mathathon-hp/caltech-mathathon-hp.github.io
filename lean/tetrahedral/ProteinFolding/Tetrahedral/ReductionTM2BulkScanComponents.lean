import ProteinFolding.Tetrahedral.ReductionTM2BulkOrientedPath
import ProteinFolding.Tetrahedral.ReductionTM2PathLeaves

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkOrientedPath

set_option maxHeartbeats 2000000

noncomputable def reversePoints (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) : ℕ → ℕ :=
  foldIndexPoint (bulkFiniteGraph m) (fold m hm ha c).reverse (BulkIndexModel.index m)

theorem reverse_indexedPath (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) :
    BoundedWalk.IndexedPath BulkPredicate.predicate m (Grid.count m) (bulkComponentLength m c) (reversePoints m hm ha c) := by
  have hL := BulkComponentPath.length_ge_three m hm ha c
  refine indexedPath_of_fold (bulkFiniteGraph m) (by change 2 ≤ bulkComponentLength m c; omega)
    (fold m hm ha c).reverse (BulkComponentPath.degree_le_two m hm) ?_ ?_
    (BulkIndexModel.index m) (BulkIndexModel.index_bound m) (BulkIndexModel.index_injective m)
    BulkPredicate.predicate m (BulkIndexModel.graph_model m)
  · change (bulkFiniteGraph m).degree ((fold m hm ha c).reverse.pos (PathOrientation.first (by omega))) ≤ 1
    rw [PathOrientation.reverse_first]
    exact (last_degree m hm ha c).le
  · change (bulkFiniteGraph m).degree ((fold m hm ha c).reverse.pos (PathOrientation.last (by omega))) ≤ 1
    rw [PathOrientation.reverse_last]
    exact (first_degree m hm ha c).le

theorem reverse_points_first (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) :
    reversePoints m hm ha c 0 = points m hm ha c (bulkComponentLength m c - 1) := by
  have h0 : 0 < bulkComponentLength m c := by have h := BulkComponentPath.length_ge_three m hm ha c; omega
  rw [reversePoints, foldIndexPoint, dif_pos h0, points_last]
  exact congrArg (BulkIndexModel.index m) (PathOrientation.reverse_first (fold m hm ha c) h0)

theorem reverse_points_last (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) :
    reversePoints m hm ha c (bulkComponentLength m c - 1) = points m hm ha c 0 := by
  have h0 : 0 < bulkComponentLength m c := by have h := BulkComponentPath.length_ge_three m hm ha c; omega
  have hlast : bulkComponentLength m c - 1 < bulkComponentLength m c := by omega
  rw [reversePoints, foldIndexPoint, dif_pos hlast, points_first]
  exact congrArg (BulkIndexModel.index m) (PathOrientation.reverse_last (fold m hm ha c) h0)

theorem emit_last_empty (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) :
    BulkScan.emit (m, points m hm ha c (bulkComponentLength m c - 1)) = [] := by
  have horder : reversePoints m hm ha c (bulkComponentLength m c - 1) ≤ reversePoints m hm ha c 0 := by
    rw [reverse_points_last, reverse_points_first]
    exact (ordered m hm ha c).le
  have he := BulkScan.emit_of_path_reversed_order m (bulkComponentLength m c) (reversePoints m hm ha c)
    (reverse_indexedPath m hm ha c) horder
  rwa [reverse_points_first] at he

theorem endpoint_is_component_end (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (k : ℕ) (hk : BulkPredicate.endpoint (m, (k, 0)) = true) :
    ∃ c : (bulkFiniteGraph m).ConnectedComponent,
      k = points m hm ha c 0 ∨ k = points m hm ha c (bulkComponentLength m c - 1) := by
  obtain ⟨hs, hinside⟩ := BulkPredicate.endpoint_inside hk
  let u : BulkVertex m := ⟨⟨Grid.point m k, hs⟩, hinside⟩
  let c := (bulkFiniteGraph m).connectedComponentMk u
  obtain ⟨i, hi⟩ := (sites m hm ha c u).2 rfl
  have hindex : BulkIndexModel.index m u = k := by
    apply Grid.point_injective m
    exact BulkIndexModel.point_index m u
  have hdegree : (bulkFiniteGraph m).degree u = 1 :=
    (bulkFinite_degree m u).trans ((BulkPredicate.endpoint_correct m k 0 u.val rfl).1 hk)
  have hleaf : (bulkFiniteGraph m).degree ((fold m hm ha c).pos i) ≤ 1 := by rw [hi]; exact hdegree.le
  have hL := BulkComponentPath.length_ge_three m hm ha c
  refine ⟨c, ?_⟩
  rcases fold_leaf_index_end (bulkFiniteGraph m) (fold m hm ha c) i hleaf with hi0 | hilast
  · left
    have he : i = PathOrientation.first (by omega) := by apply Fin.ext; change i.val = 0; exact hi0
    rw [← hi, he] at hindex
    rw [points_first]
    exact hindex.symm
  · right
    have he : i = PathOrientation.last (by omega) := by apply Fin.ext; change i.val = bulkComponentLength m c - 1; omega
    rw [← hi, he] at hindex
    rw [points_last]
    exact hindex.symm

theorem emit_nonempty_iff (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) (k : ℕ) :
    BulkScan.emit (m, k) ≠ [] ↔ ∃ c : (bulkFiniteGraph m).ConnectedComponent, k = points m hm ha c 0 := by
  constructor
  · intro hne
    have hcan : BulkScan.canonical (m, k) = true := by
      cases hc : BulkScan.canonical (m, k)
      · simp [BulkScan.emit, hc] at hne
      · rfl
    change (BulkPredicate.endpoint (m, (k, 0)) && decide (k < (BulkScan.walk (m, k)).2.1.2)) = true at hcan
    rw [Bool.and_eq_true] at hcan
    obtain ⟨c, hc | hc⟩ := endpoint_is_component_end m hm ha k hcan.1
    · exact ⟨c, hc⟩
    · rw [hc, emit_last_empty m hm ha c] at hne
      exact False.elim (hne rfl)
  · rintro ⟨c, rfl⟩
    rw [emitted m hm ha c]
    simp

theorem first_bound (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic)
    (c : (bulkFiniteGraph m).ConnectedComponent) : points m hm ha c 0 < Grid.count m :=
  (indexedPath m hm ha c).bound 0 (by have h := BulkComponentPath.length_ge_three m hm ha c; omega)

theorem first_injective (m : ℕ) (hm : 27 ≤ m) (ha : (bulkFiniteGraph m).IsAcyclic) :
    Function.Injective (fun c : (bulkFiniteGraph m).ConnectedComponent => points m hm ha c 0) := by
  intro c d he
  change points m hm ha c 0 = points m hm ha d 0 at he
  rw [points_first, points_first] at he
  have hv := BulkIndexModel.index_injective m he
  have hc0 : 0 < bulkComponentLength m c := by have h := BulkComponentPath.length_ge_three m hm ha c; omega
  have hd0 : 0 < bulkComponentLength m d := by have h := BulkComponentPath.length_ge_three m hm ha d; omega
  have hc := (sites m hm ha c ((fold m hm ha c).pos (PathOrientation.first hc0))).1 ⟨PathOrientation.first hc0, rfl⟩
  have hd := (sites m hm ha d ((fold m hm ha d).pos (PathOrientation.first hd0))).1 ⟨PathOrientation.first hd0, rfl⟩
  rw [hv] at hc
  exact hc.symm.trans hd

end ProteinFolding.Tetrahedral.ReductionTM2.BulkOrientedPath
