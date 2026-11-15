import ProteinFolding.Tetrahedral.NearFieldWordPieceAssembly
import ProteinFolding.Tetrahedral.OctahedralCount

/-! Actual residue support survives finite assembly; injectivity and the
already proved builder H count upgrade containment to exact coverage. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem pieceHsupport_subset (ps : List PositionedWord) (T : Finset Site)
    (hpieces : ∀ p ∈ ps, hSupport p.word p.fold ⊆ T) : pieceHsupport ps ⊆ T := by
  induction ps with
  | nil => simp [pieceHsupport]
  | cons p ps ih =>
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hpieces p (List.mem_cons_self ..) hx
    · exact ih (fun q hq => hpieces q (List.mem_cons_of_mem _ hq)) hx

theorem PieceAssembly.hSupport_subset {ps : List PositionedWord} (a : PieceAssembly ps)
    (T : Finset Site) (hpieces : ∀ p ∈ ps, hSupport p.word p.fold ⊆ T) :
    hSupport a.piece.word a.piece.fold ⊆ T := by
  rw [a.hSupport_eq]
  exact pieceHsupport_subset ps T hpieces

theorem hSupport_eq_oct_of_subset_count {S : Sequence} (f : Fold tetrahedralLattice S.length)
    (m : ℕ) (hsub : hSupport S f ⊆ octahedron m)
    (hcount : hydrophobicCount S = octahedralNumber m) : hSupport S f = octahedron m := by
  apply Finset.eq_of_subset_of_card_le hsub
  rw [octahedron_card, hSupport_card, hcount]

theorem assembled_hSupport_eq_oct {ps : List PositionedWord} (a : PieceAssembly ps)
    (m : ℕ) (hpieces : ∀ p ∈ ps, hSupport p.word p.fold ⊆ octahedron m)
    (hcount : hydrophobicCount a.piece.word = octahedralNumber m) :
    hSupport a.piece.word a.piece.fold = octahedron m :=
  hSupport_eq_oct_of_subset_count a.piece.fold m (a.hSupport_subset _ hpieces) hcount

end ProteinFolding.Tetrahedral.NearField
