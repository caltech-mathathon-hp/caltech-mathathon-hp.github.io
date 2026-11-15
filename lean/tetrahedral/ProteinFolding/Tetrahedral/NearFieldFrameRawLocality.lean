import ProteinFolding.Tetrahedral.NearFieldFrameFolds

/-! Scalar locality is proved before substituting computed construction data. -/

namespace ProteinFolding.Tetrahedral.NearField

private theorem raw_skin_positions_in_solid {m n : ℕ} (f : Fold tetrahedralLattice n)
    (h : ∀ i, f.pos i ∈ skin m 1) : ∀ i, InSkinSolid m 1 (f.pos i) := by
  intro i
  exact (mem_skinSolid m 1 _).mp (skin_subset_solid m 1 (h i))

theorem framePFold_inSkinSolid_one (m q : ℕ) (kind : Fin 6) (hq : q % 2 = 1)
    (hqlo : 5 ≤ q) (hqhi : (q : ℤ) + 10 ≤ octRadius m) :
    ∀ i : Fin (nearFrameLength kind - 2), InSkinSolid m 1 ((framePFold m q kind hq).pos i) :=
  raw_skin_positions_in_solid (m := m) (framePFold m q kind hq)
    (framePFold_mem_skin_one m q kind hq hqlo hqhi)

end ProteinFolding.Tetrahedral.NearField
