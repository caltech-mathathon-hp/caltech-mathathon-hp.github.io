import ProteinFolding.Tetrahedral.NearFieldWordPieceAssembly
import ProteinFolding.Tetrahedral.Columns
import ProteinFolding.Tetrahedral.Skins

/-! Property transport proved once with abstract words, folds and sites. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem hSupport_subset_of_positions {S : Sequence} (f : Fold tetrahedralLattice S.length)
    (A : Finset Site) (hf : ∀ i, f.pos i ∈ A) : hSupport S f ⊆ A := by
  intro x hx
  obtain ⟨i, _, hi⟩ := (mem_hSupport S f x).mp hx
  rw [← hi]
  exact hf i

theorem PieceAssembly.position_property {ps : List PositionedWord} (a : PieceAssembly ps)
    (P : Site → Prop) (hpieces : ∀ p ∈ ps, ∀ r, P (p.fold.pos r))
    (i : Fin a.piece.word.length) : P (a.piece.fold.pos i) := by
  have hm := (mem_foldSites a.piece.fold (a.piece.fold.pos i)).mpr ⟨i, rfl⟩
  rw [a.sites_eq] at hm
  obtain ⟨p, hp, hmem⟩ := (mem_pieceSites ps _).mp hm
  obtain ⟨r, hr⟩ := (mem_foldSites p.fold _).mp hmem
  rw [← hr]
  exact hpieces p hp r

theorem fold_ne_column_of_inside {S : Sequence} {m : ℕ} (f : Fold tetrahedralLattice S.length)
    (C : DanglingColumn m) (hf : ∀ i, f.pos i ∈ octahedron m) (i : Fin S.length) (n : ℕ) :
    f.pos i ≠ C.point n := by
  intro heq
  have hi := hf i
  rw [heq] at hi
  exact C.point_outside n hi

theorem fold_inOct_to_inSkinSolid_one {S : Sequence} {m : ℕ} (f : Fold tetrahedralLattice S.length)
    (hf : ∀ i, f.pos i ∈ octahedron m) (i : Fin S.length) : InSkinSolid m 1 (f.pos i) := by
  have hz : f.pos i ∈ skinSolid m 0 := by rw [skinSolid_zero]; exact hf i
  exact (mem_skinSolid m 1 _).mp (skinSolid_mono m (by omega : 0 ≤ 1) hz)

theorem fold_inSkin_to_inSkinSolid_one {S : Sequence} {m : ℕ} (f : Fold tetrahedralLattice S.length)
    (hf : ∀ i, f.pos i ∈ skin m 1) (i : Fin S.length) : InSkinSolid m 1 (f.pos i) :=
  (mem_skinSolid m 1 _).mp (skin_subset_solid m 1 (hf i))

end ProteinFolding.Tetrahedral.NearField
