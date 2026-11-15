import ProteinFolding.Tetrahedral.NearFieldUnitSupport
import ProteinFolding.Tetrahedral.NearFieldSeparatorCapSupport

/-! Hydrophobic containment for the actual capped separator word. -/

namespace ProteinFolding.Tetrahedral.NearField

private theorem subset_transport {A B T : Finset Site} (h : A = B) (hB : B ⊆ T) : A ⊆ T := by
  rw [h]
  exact hB

theorem separatorWordPiece_hSupport_subset_oct (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10)) :
    hSupport (separatorWordPiece p k hk C D hC hD).word
      (separatorWordPiece p k hk C D hC hD).fold ⊆ octahedron p.side := by
  dsimp only [separatorWordPiece]
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  with_reducible
    exact subset_transport
      (A := hSupport (capWord (p.separatorWord k)) (cappedSeparatorFold p k hk C D hC hD))
      (B := (edgeDimerHsites p.side entryEdgeFrame (6 * (k + 1)) 0 ∪
        edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex k) 1) ∪
        edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot k + 6) 2)
      (T := octahedron p.side)
      ((cappedSeparatorFold_hSupport p k hk C D hC hD).trans (separatorFold_hSupport p k hk))
      (Finset.union_subset
        (Finset.union_subset
          (edgeDimerHsites_subset_oct hm entryEdgeFrame (6 * (k + 1)) 0 (separatorEntry_room p k hk))
          (edgeDimerHsites_subset_oct hm trackEdgeFrame (2 * p.separatorIndex k) 1 (separatorCenter_room p k hk)))
        (edgeDimerHsites_subset_oct hm exitEdgeFrame (10 * p.exitSlot k + 6) 2 (separatorExit_room p k)))

end ProteinFolding.Tetrahedral.NearField
