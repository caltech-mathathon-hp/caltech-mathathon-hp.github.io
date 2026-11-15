import ProteinFolding.Tetrahedral.NearFieldHRunFolds

/-! Reversing a literal all-H edge run preserves its support and exchanges its endpoints. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem foldSites_reverse {n : ℕ} (f : Fold tetrahedralLattice n) : foldSites f.reverse = foldSites f := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := (mem_foldSites _ _).mp hx
    exact (mem_foldSites _ _).mpr ⟨i.rev, hi⟩
  · intro hx
    obtain ⟨i, hi⟩ := (mem_foldSites _ _).mp hx
    refine (mem_foldSites _ _).mpr ⟨i.rev, ?_⟩
    change f.pos (i.rev.rev) = x
    simpa only [Fin.rev_rev] using hi

theorem edgeHRunFold_reverse_first {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (a n : ℕ)
    (i : Fin (List.replicate n Residue.H).length) (hi : i.val = 0) :
    (edgeHRunFold hm F a n).reverse.pos i = octEdgeZigzag m F (a + (n - 1)) := by
  apply edgeHRunFold_last hm F a n i.rev
  rw [Fin.val_rev]
  have hil := i.isLt
  omega

theorem edgeHRunFold_reverse_last {m : ℕ} (hm : 1 ≤ m) (F : OctEdgeFrame) (a n : ℕ)
    (i : Fin (List.replicate n Residue.H).length) (hi : i.val + 1 = (List.replicate n Residue.H).length) :
    (edgeHRunFold hm F a n).reverse.pos i = octEdgeZigzag m F a := by
  apply edgeHRunFold_first hm F a n i.rev
  rw [Fin.val_rev]
  omega

end ProteinFolding.Tetrahedral.NearField
