import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonReservedSeparation
import ProteinFolding.Tetrahedral.NearFieldLinkerAssembly
import ProteinFolding.Tetrahedral.NearFieldLeftFillerCaps

/-! The special corner-starting left filler avoids each standalone PHP unit.
Its replaced first H site and both local caps are retained explicitly. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem leftFillerFold_property_of_track (p : ConstructionParameters) (P : Site → Prop)
    (hstart : P (octEdgeZigzag p.side entryEdgeFrame 2))
    (htrack : ∀ r : Fin (dimerChain (p.leftFiller - 1 + 1)).length,
      P ((edgeDimerFold (m := p.side) (by have h := p.side_ge; omega) trackEdgeFrame 0
        (p.leftFiller - 1) false (leftFiller_room p)).pos r))
    (i : Fin (dimerChain p.leftFiller).length) : P ((leftFillerFold p).pos i) := by
  rw [leftFillerFold_pos, leftFillerCurve]
  split_ifs
  · exact hstart
  · let r : Fin (dimerChain (p.leftFiller - 1 + 1)).length :=
      ⟨i.val, by
        have h := positive_dimer_word p.leftFiller (by have h := p.leftFiller_ge; omega)
        rw [h]
        exact i.isLt⟩
    have h := htrack r
    rw [edgeDimerFold_pos] at h
    exact h

theorem leftFillerFold_ne_singletonOwner (p : ConstructionParameters) (j : Fin 3)
    (i : Fin (dimerChain p.leftFiller).length) :
    (leftFillerFold p).pos i ≠ canonicalSingletonOwner p.side j :=
  leftFillerFold_property_of_track p (fun x => x ≠ canonicalSingletonOwner p.side j)
    (singletonOwner_ne_reservedEdge p.side (by have h := p.side_ge; omega) j entryEdgeFrame rfl 2).symm
    (edgeDimerFold_ne_octSite_of_not_mem_Hsites (by have h := p.side_ge; omega : 1 ≤ p.side)
      trackEdgeFrame 0 (p.leftFiller - 1) false (leftFiller_room p) _
      (canonicalSingletonOwner_mem p.side (by have h := p.side_ge; omega) j)
      (singletonOwner_not_mem_reservedHsites p.side (by have h := p.side_ge; omega) j trackEdgeFrame rfl _ _)) i

theorem leftFillerFold_ne_singletonCap (p : ConstructionParameters) (j : Fin 3) (last : Bool)
    (i : Fin (dimerChain p.leftFiller).length) :
    (leftFillerFold p).pos i ≠
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) j last).seed := by
  let E := canonicalSingletonColumn p.side (by have h := p.side_ge; omega) j last
  apply leftFillerFold_property_of_track p (fun x => x ≠ E.seed) _ _ i
  · intro heq
    exact E.seed_dangling.1 (heq ▸ leftFillerStart_mem_oct p)
  · exact edgeDimerFold_ne_cap_of_owner_not_mem (by have h := p.side_ge; omega : 1 ≤ p.side)
      trackEdgeFrame 0 (p.leftFiller - 1) false (leftFiller_room p) E
      (singletonOwner_not_mem_reservedHsites p.side (by have h := p.side_ge; omega) j trackEdgeFrame rfl _ _)

theorem cappedLeftFillerFold_ne_singletonOwner (p : ConstructionParameters) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2))
    (j : Fin 3) (i : Fin (capWord (dimerChain p.leftFiller)).length) :
    (cappedLeftFillerFold p C D hC hD).pos i ≠ canonicalSingletonOwner p.side j := by
  have hin := canonicalSingletonOwner_mem p.side (by have h := p.side_ge; omega) j
  exact frameTrack_property_of_capped_sites (cappedLeftFillerFold p C D hC hD) (leftFillerFold p)
    C.seed D.seed (cappedLeftFillerFold_sites p C D hC hD)
    (fun x => x ≠ canonicalSingletonOwner p.side j)
    (fun heq => C.seed_dangling.1 (heq.symm ▸ hin)) (leftFillerFold_ne_singletonOwner p j)
    (fun heq => D.seed_dangling.1 (heq.symm ▸ hin)) i

theorem cappedLeftFillerFold_ne_singletonCap (p : ConstructionParameters) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2))
    (j : Fin 3) (last : Bool) (i : Fin (capWord (dimerChain p.leftFiller)).length) :
    (cappedLeftFillerFold p C D hC hD).pos i ≠
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) j last).seed := by
  let E := canonicalSingletonColumn p.side (by have h := p.side_ge; omega) j last
  have hCm : C.owner ≠ E.owner := by
    rw [hC]
    exact (singletonOwner_ne_reservedEdge p.side (by have h := p.side_ge; omega) j entryEdgeFrame rfl _).symm
  have hDm : D.owner ≠ E.owner := by
    rw [hD]
    exact (singletonOwner_ne_reservedEdge p.side (by have h := p.side_ge; omega) j trackEdgeFrame rfl _).symm
  exact frameTrack_property_of_capped_sites (cappedLeftFillerFold p C D hC hD) (leftFillerFold p)
    C.seed D.seed (cappedLeftFillerFold_sites p C D hC hD) (fun x => x ≠ E.seed)
    (dangling_caps_ne_of_owner_ne p.side C.owner E.owner C.dir E.dir C.owner_mem E.owner_mem C.seed_outside hCm)
    (leftFillerFold_ne_singletonCap p j last)
    (dangling_caps_ne_of_owner_ne p.side D.owner E.owner D.dir E.dir D.owner_mem E.owner_mem D.seed_outside hDm) i

theorem canonicalLeftPiece_ne_singletonPiece (p : ConstructionParameters) (j : Fin 3)
    (i : Fin (canonicalLeftPiece p).word.length)
    (s : Fin (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j).word.length) :
    (canonicalLeftPiece p).fold.pos i ≠
      (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j).fold.pos s := by
  intro heq
  have hmem := (mem_foldSites
    (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j).fold _).mpr ⟨s, heq.symm⟩
  rw [canonicalSingletonPiece_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · exact cappedLeftFillerFold_ne_singletonCap p (entryLocalColumn p none) (leftLastColumn p)
      rfl (leftLastColumn_owner p) j false i h
  · exact cappedLeftFillerFold_ne_singletonOwner p (entryLocalColumn p none) (leftLastColumn p)
      rfl (leftLastColumn_owner p) j i h
  · exact cappedLeftFillerFold_ne_singletonCap p (entryLocalColumn p none) (leftLastColumn p)
      rfl (leftLastColumn_owner p) j true i h

theorem canonicalLeftPiece_singletonPiece_disjoint (p : ConstructionParameters) (j : Fin 3) :
    WordsDisjoint (canonicalLeftPiece p)
      (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j) :=
  (foldSites_disjoint_iff _ _).mpr (canonicalLeftPiece_ne_singletonPiece p j)

end ProteinFolding.Tetrahedral.NearField
