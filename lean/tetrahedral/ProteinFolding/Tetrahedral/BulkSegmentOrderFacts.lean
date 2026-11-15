import ProteinFolding.Tetrahedral.BulkSegments
import Mathlib.Tactic.Linarith

/-! The lexicographic comparison uses only row status, alpha sign and the
differences of alpha, Xhat, and (for rows) absolute Xhat. -/

namespace ProteinFolding.Tetrahedral

theorem bulkSegmentPotential_lt_iff_of_statistics (m n : ℕ)
    (p p' : BulkVertex m) (q q' : BulkVertex n) (aShift xShift : ℤ)
    (hrow : BulkRowSegment n q ↔ BulkRowSegment m p)
    (hrow' : BulkRowSegment n q' ↔ BulkRowSegment m p')
    (hsign : 0 < bulkAlpha n q.val ↔ 0 < bulkAlpha m p.val)
    (hsign' : 0 < bulkAlpha n q'.val ↔ 0 < bulkAlpha m p'.val)
    (ha : bulkAlpha n q.val = bulkAlpha m p.val + aShift)
    (ha' : bulkAlpha n q'.val = bulkAlpha m p'.val + aShift)
    (hx : bulkSegmentXhat n q = bulkSegmentXhat m p + xShift)
    (hx' : bulkSegmentXhat n q' = bulkSegmentXhat m p' + xShift)
    (habs : |bulkSegmentXhat n q| - |bulkSegmentXhat n q'| =
      |bulkSegmentXhat m p| - |bulkSegmentXhat m p'|) :
    (bulkSegmentPotential n q < bulkSegmentPotential n q' ↔
      bulkSegmentPotential m p < bulkSegmentPotential m p') := by
  classical
  unfold bulkSegmentPotential
  simp only [hrow, hrow', hsign, hsign']
  rw [hx, hx'] at habs
  simp only [ha, ha', hx, hx']
  by_cases hR : BulkRowSegment m p <;> by_cases hR' : BulkRowSegment m p' <;>
    by_cases hA : 0 < bulkAlpha m p.val <;> by_cases hA' : 0 < bulkAlpha m p'.val
  all_goals simp only [hR, hR', hA, hA', ↓reduceIte, Prod.Lex.toLex_lt_toLex]
  all_goals simp only [Nat.reduceLT, Nat.reduceEqDiff, lt_self_iff_false, true_and,
    false_or, false_and, and_false, or_false, true_or, add_lt_add_iff_right, add_left_inj]
  all_goals constructor <;> intro hlt <;> linarith only [habs, hlt]

end ProteinFolding.Tetrahedral
