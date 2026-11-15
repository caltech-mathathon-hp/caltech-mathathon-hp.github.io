import ProteinFolding.Tetrahedral.ReductionTM2BulkIndexModel
import ProteinFolding.Tetrahedral.FarFieldParity

namespace ProteinFolding.Tetrahedral.ReductionTM2.BulkIndexModel

theorem colour_index (m : ℕ) (u : BulkVertex m) :
    BulkPredicate.colour (m, (index m u, 0)) = FarField.colour u.val := by
  have hc := BulkPredicate.colour_correct m (index m u) 0
  rw [point_index m u] at hc
  by_cases ha : InASublattice u.val.val
  · rw [hc.2 ha]
    simp only [FarField.colour, ha, decide_true]
  · have hf : BulkPredicate.colour (m, (index m u, 0)) = false := by
      cases hb : BulkPredicate.colour (m, (index m u, 0))
      · rfl
      · exact False.elim (ha (hc.1 hb))
    rw [hf]
    simp only [FarField.colour, ha, decide_false]

end ProteinFolding.Tetrahedral.ReductionTM2.BulkIndexModel
