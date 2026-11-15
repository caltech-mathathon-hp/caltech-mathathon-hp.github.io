import ProteinFolding.Tetrahedral.NearFieldLinkerAssembly
import ProteinFolding.Tetrahedral.NearFieldSeparatorObstacleOwners
import ProteinFolding.Tetrahedral.NearFieldFrameSeparatorHSupport
import ProteinFolding.Tetrahedral.NearFieldSeparatorFrameClearance
import ProteinFolding.Tetrahedral.NearFieldCanonicalSeparatorPieces
import ProteinFolding.Tetrahedral.NearFieldActualFrameFold

/-! The complete actual separator avoids the complete actual frame, including
both caps of each word. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096

attribute [local irreducible] ConstructionParameters.side

theorem separator_hSupport_excludes_frameH (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (f : ℕ) (kind : Fin 6) (hfhi : (f : ℤ) + 10 ≤ octRadius p.side)
    (hentry : kind = 1 → f % 6 = 5) (hexit : kind = 4 → f % 10 = 5) (last : Bool) :
    (if last then frameEndH p.side f kind else frameStartH p.side f kind) ∉
      hSupport (p.separatorWord k) (separatorFold p k hk) := by
  rw [separatorFold_hSupport]
  intro h
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact separatorEntry_excludes_frameH p k hk f kind hfhi hentry last h
    · exact separatorCenter_excludes_frameH p k hk f kind hfhi last h
  · exact separatorExit_excludes_frameH p k f kind hfhi hexit last h

theorem frameEndpointColumn_not_separator_hSupport (p : ConstructionParameters) (k : ℕ)
    (hk : k ≤ p.bins) (b : Bool) :
    (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) b).owner ∉
      hSupport (p.separatorWord k) (separatorFold p k hk) := by
  have hroom : (5 : ℤ) + 10 ≤ octRadius p.side := by
    have h := p.side_ge
    dsimp [octRadius]
    omega
  change frameEndpointVertex p.side b ∉ _
  rw [frameEndpointVertex_eq_edge p b]
  cases b
  · have h := separator_hSupport_excludes_frameH p k hk 5 5 hroom
      (by decide) (by decide) true
    simpa only [ite_true, frameEndH_5] using h
  · have h := separator_hSupport_excludes_frameH p k hk 5 0 hroom
      (by decide) (by decide) false
    simpa only [Bool.false_eq_true, if_false, frameStartH_0] using h

theorem cappedSeparatorFold_ne_frameCoreFold (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10))
    (i : Fin (capWord (p.separatorWord k)).length)
    (r : Fin (p.framePart1 ++ p.framePart2).length) :
    (cappedSeparatorFold p k hk C D hC hD).pos i ≠ (frameCoreFold p).pos r := by
  apply frameCoreFold_property p (fun x => (cappedSeparatorFold p k hk C D hC hD).pos i ≠ x) _ r
  intro j s
  rcases j with j | j
  · dsimp only [frameCorePiece, frameHRunPiece] at s ⊢
    exact cappedSeparatorFold_ne_octSite_of_not_mem_hSupport p k hk C D hC hD
      _ (frameHRunFold_mem_oct p j s)
      (fun h => Finset.disjoint_left.mp (frameHRunFold_disjoint_separator_hSupport p k hk j)
        ((mem_foldSites _ _).mpr ⟨s, rfl⟩) h) i
  · dsimp only [frameCorePiece, frameLinkPiece] at s ⊢
    rw [frameLinkWordFold_pos]
    exact cappedSeparatorFold_ne_framePFold p k hk C D hC hD
      (frameLinkParameter j) (frameLinkKind j) (frameLinkParameter_odd p j)
      (frameLinkParameter_ge p j) (frameLinkParameter_room p j)
      (frameLink_entry_residue p j) (frameLink_exit_residue p j) i _

theorem cappedSeparatorFold_ne_frameFold (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)))
    (hD : D.owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10))
    (i : Fin (capWord (p.separatorWord k)).length) (r : Fin p.frameWord.length) :
    (cappedSeparatorFold p k hk C D hC hD).pos i ≠ (frameFold p).pos r := by
  have hcaps (b : Bool) : (cappedSeparatorFold p k hk C D hC hD).pos i ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) b).seed :=
    cappedSeparatorFold_ne_cap_of_owner_not_mem_all p k hk C D hC hD _
      (frameEndpointColumn_not_separator_hSupport p k hk b) i
  exact frameTrack_property_of_capped_sites (frameFold p) (frameCoreFold p)
    (frameFirstColumn p).seed (frameLastColumn p).seed (frameFold_sites p)
    (fun x => (cappedSeparatorFold p k hk C D hC hD).pos i ≠ x)
    (hcaps true) (cappedSeparatorFold_ne_frameCoreFold p k hk C D hC hD i) (hcaps false) r

theorem canonicalSeparatorPiece_ne_frameFold (p : ConstructionParameters) (k : Fin (p.bins + 1))
    (i : Fin (canonicalSeparatorPiece p k).word.length) (r : Fin p.frameWord.length) :
    (canonicalSeparatorPiece p k).fold.pos i ≠ (frameFold p).pos r :=
  cappedSeparatorFold_ne_frameFold p k.val (by have h := k.isLt; omega)
    (entryLocalColumn p (some k)) (exitCapColumn p k.val (by have h := k.isLt; omega))
    rfl (exitCapColumn_owner p k.val (by have h := k.isLt; omega)) i r

theorem frameWordPiece_canonicalSeparatorPiece_disjoint (p : ConstructionParameters)
    (k : Fin (p.bins + 1)) : WordsDisjoint (frameWordPiece p) (canonicalSeparatorPiece p k) :=
  ((foldSites_disjoint_iff _ _).mpr (canonicalSeparatorPiece_ne_frameFold p k)).symm

end ProteinFolding.Tetrahedral.NearField
