import ProteinFolding.Tetrahedral.ReductionTM2BulkPredicate
import ProteinFolding.Tetrahedral.ReductionTM2BulkCoverSemantics

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkPredicate

open Arithmetic BulkArithmetic

theorem correct (m i j : ℕ) (s t : Site)
    (hs : Grid.point m i = s.val) (ht : Grid.point m j = t.val) :
    predicate (m, (i, j)) = true ↔ (bulkCoverGraph m).Adj s t := by
  have hleft : evalPoint (fields (m, (i, j))) leftPoint = s.val := (eval_leftPoint _).trans hs
  have hright : evalPoint (fields (m, (i, j))) rightPoint = t.val := (eval_rightPoint _).trans ht
  exact eval_guardedCover (fields (m, (i, j))) (.field 0) leftPoint rightPoint s t hleft hright

theorem predicate_true_sites {m i j : ℕ} (h : predicate (m, (i, j)) = true) :
    IsLatticeSite (Grid.point m i) ∧ IsLatticeSite (Grid.point m j) := by
  change Arithmetic.eval (fields (m, (i, j))) (guardedCover (.field 0) leftPoint rightPoint) = true at h
  rw [guardedCover, Arithmetic.eval_and_true, Arithmetic.eval_and_true,
    eval_site, eval_site, eval_leftPoint, eval_rightPoint] at h
  exact ⟨h.1, h.2.1⟩

/-- The closed arithmetic predicate agrees with the exact canonical graph on
every raw index pair, including indices that do not represent lattice sites. -/
theorem guarded_correct (m i j : ℕ) : predicate (m, (i, j)) = true ↔
    ∃ hs : IsLatticeSite (Grid.point m i), ∃ ht : IsLatticeSite (Grid.point m j),
      (bulkCoverGraph m).Adj ⟨Grid.point m i, hs⟩ ⟨Grid.point m j, ht⟩ := by
  constructor
  · intro h
    have hv := predicate_true_sites h
    exact ⟨hv.1, hv.2, (correct m i j _ _ rfl rfl).1 h⟩
  · rintro ⟨hs, ht, h⟩
    exact (correct m i j _ _ rfl rfl).2 h

theorem predicate_indices_bound {m i j : ℕ} (h : predicate (m, (i, j)) = true) :
    i < Grid.count m ∧ j < Grid.count m := by
  obtain ⟨hs, ht, hadj⟩ := (guarded_correct m i j).1 h
  have hsupp := bulkCoverGraph_support m hadj
  have hsi : InOctahedron m ⟨Grid.point m i, hs⟩ :=
    (mem_octahedron m _).1 (Finset.mem_sdiff.mp hsupp.1).1
  have hti : InOctahedron m ⟨Grid.point m j, ht⟩ :=
    (mem_octahedron m _).1 (Finset.mem_sdiff.mp hsupp.2).1
  obtain ⟨ki, hki, hei⟩ := Grid.octahedron_has_index hsi
  obtain ⟨kj, hkj, hej⟩ := Grid.octahedron_has_index hti
  have hi : ki = i := Grid.point_injective m hei
  have hj : kj = j := Grid.point_injective m hej
  exact ⟨hi ▸ hki, hj ▸ hkj⟩

theorem colour_correct (m i j : ℕ) :
    colour (m, (i, j)) = true ↔ InASublattice (Grid.point m i) := by
  change Arithmetic.eval (fields (m, (i, j))) (inA leftPoint) = true ↔ _
  rw [eval_inA, eval_leftPoint]

end ProteinFolding.Tetrahedral.ReductionTM2.BulkPredicate
