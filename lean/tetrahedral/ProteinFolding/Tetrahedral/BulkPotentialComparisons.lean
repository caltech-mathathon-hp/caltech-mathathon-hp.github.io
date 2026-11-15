import ProteinFolding.Tetrahedral.BulkSegments

/-! Direct sufficient comparisons for the exact lexicographic potential. -/

namespace ProteinFolding.Tetrahedral

theorem bulkSegmentPotential_lt_of_alpha_up (m : ℕ) (p q : BulkVertex m)
    (hpR : ¬BulkRowSegment m p) (hpA : 0 < bulkAlpha m p.val)
    (hA : bulkAlpha m p.val < bulkAlpha m q.val) :
    bulkSegmentPotential m p < bulkSegmentPotential m q := by
  classical
  have hqA : 0 < bulkAlpha m q.val := lt_trans hpA hA
  unfold bulkSegmentPotential
  simp only [if_neg hpR, if_pos hpA]
  by_cases hqR : BulkRowSegment m q
  · simp only [if_pos hqR]
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (show (1 : ℕ) < 2 by decide))
  · simp only [if_neg hqR, if_pos hqA]
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl hA)⟩)

theorem bulkSegmentPotential_lt_of_negative_x_up (m : ℕ) (p q : BulkVertex m)
    (hpR : ¬BulkRowSegment m p) (hpA : bulkAlpha m p.val < 0)
    (hX : bulkSegmentXhat m p < bulkSegmentXhat m q) :
    bulkSegmentPotential m p < bulkSegmentPotential m q := by
  classical
  have hpNA : ¬0 < bulkAlpha m p.val := by omega
  unfold bulkSegmentPotential
  simp only [if_neg hpR, if_neg hpNA]
  by_cases hqR : BulkRowSegment m q
  · simp only [if_pos hqR]
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (show (0 : ℕ) < 2 by decide))
  · simp only [if_neg hqR]
    by_cases hqA : 0 < bulkAlpha m q.val
    · simp only [if_pos hqA]
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (show (0 : ℕ) < 1 by decide))
    · simp only [if_neg hqA]
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,
        Prod.Lex.toLex_lt_toLex.mpr (Or.inl hX)⟩)

theorem bulkSegmentPotential_lt_of_row_abs_up (m : ℕ) (p q : BulkVertex m)
    (hpR : BulkRowSegment m p) (hqR : BulkRowSegment m q)
    (hX : |bulkSegmentXhat m p| < |bulkSegmentXhat m q|) :
    bulkSegmentPotential m p < bulkSegmentPotential m q := by
  classical
  unfold bulkSegmentPotential
  simp only [if_pos hpR, if_pos hqR]
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,
    Prod.Lex.toLex_lt_toLex.mpr (Or.inl hX)⟩)

end ProteinFolding.Tetrahedral
