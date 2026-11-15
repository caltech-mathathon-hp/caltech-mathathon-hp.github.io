import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonReservedSeparation
import ProteinFolding.Tetrahedral.NearFieldLinkerAssembly
import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonFamily
import ProteinFolding.Tetrahedral.NearFieldFrameColumnFamily

/-! The actual complete frame avoids every standalone PHP unit. The column
statement includes height zero, which is needed for local cap separation. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem frameHRunFold_ne_singletonOwner (p : ConstructionParameters) (j : FrameHRunIndex p)
    (r : Fin (frameHRunWord p j).length) (s : Fin 3) :
    (frameHRunFold p j).pos r ≠ canonicalSingletonOwner p.side s := by
  have hmem := (mem_foldSites (frameHRunFold p j) _).mpr ⟨r, rfl⟩
  rw [frameHRunFold_sites] at hmem
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hmem
  have hF : (frameHRunData p j).frame.j = 3 := by
    rw [frameHRun_frame]
    split_ifs <;> rfl
  intro heq
  exact singletonOwner_ne_reservedEdge p.side (by have h := p.side_ge; omega) s
    (frameHRunData p j).frame hF _ (ht.trans heq).symm

theorem frameCoreFold_ne_singletonOwner (p : ConstructionParameters) (s : Fin 3)
    (i : Fin (p.framePart1 ++ p.framePart2).length) :
    (frameCoreFold p).pos i ≠ canonicalSingletonOwner p.side s := by
  apply frameCoreFold_property p (fun x => x ≠ canonicalSingletonOwner p.side s) _ i
  intro j r
  rcases j with j | j
  · dsimp only [frameCorePiece, frameHRunPiece] at r ⊢
    exact frameHRunFold_ne_singletonOwner p j r s
  · dsimp only [frameCorePiece, frameLinkPiece] at r ⊢
    rw [frameLinkWordFold_pos]
    intro heq
    have hinside := canonicalSingletonOwner_mem p.side (by have h := p.side_ge; omega) s
    rw [← heq] at hinside
    exact framePFold_outside p.side (frameLinkParameter j) (frameLinkKind j)
      (frameLinkParameter_odd p j) _ hinside

theorem frameFold_ne_singletonOwner (p : ConstructionParameters) (s : Fin 3)
    (i : Fin p.frameWord.length) : (frameFold p).pos i ≠ canonicalSingletonOwner p.side s := by
  have hinside := canonicalSingletonOwner_mem p.side (by have h := p.side_ge; omega) s
  apply frameTrack_property_of_capped_sites (frameFold p) (frameCoreFold p)
    (frameFirstColumn p).seed (frameLastColumn p).seed (frameFold_sites p)
    (fun x => x ≠ canonicalSingletonOwner p.side s) _ _ _ i
  · intro heq
    exact (frameFirstColumn p).seed_dangling.1 (heq.symm ▸ hinside)
  · exact frameCoreFold_ne_singletonOwner p s
  · intro heq
    exact (frameLastColumn p).seed_dangling.1 (heq.symm ▸ hinside)

theorem frameFold_ne_canonicalSingletonColumn (p : ConstructionParameters) (s : Fin 3)
    (last : Bool) (n : ℕ) (i : Fin p.frameWord.length) :
    (frameFold p).pos i ≠
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) s last).point n := by
  let C := canonicalSingletonColumn p.side (by have h := p.side_ge; omega) s last
  have hcore : ∀ j, (frameCoreFold p).pos j ≠ C.point n :=
    frameCoreFold_ne_column_of_links p C n (fun j r =>
      canonicalSingletonColumn_ne_framePFold p.side (by have h := p.side_ge; omega)
        s last n (frameLinkParameter j) (frameLinkKind j) (frameLinkParameter_odd p j)
        (frameLinkParameter_ge p j) (frameLinkParameter_room p j) r)
  exact frameTrack_property_of_capped_sites (frameFold p) (frameCoreFold p)
    (frameFirstColumn p).seed (frameLastColumn p).seed (frameFold_sites p)
    (fun x => x ≠ C.point n)
    (canonicalSingletonColumn_ne_frameEndpointColumn p.side (by have h := p.side_ge; omega)
      s last true n 0).symm hcore
    (canonicalSingletonColumn_ne_frameEndpointColumn p.side (by have h := p.side_ge; omega)
      s last false n 0).symm i

theorem frameFold_ne_singletonPiece (p : ConstructionParameters) (j : Fin 3)
    (i : Fin p.frameWord.length)
    (s : Fin (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j).word.length) :
    (frameFold p).pos i ≠
      (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j).fold.pos s := by
  intro heq
  have hmem := (mem_foldSites
    (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j).fold _).mpr ⟨s, heq.symm⟩
  rw [canonicalSingletonPiece_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · exact frameFold_ne_canonicalSingletonColumn p j false 0 i h
  · exact frameFold_ne_singletonOwner p j i h
  · exact frameFold_ne_canonicalSingletonColumn p j true 0 i h

theorem frameWordPiece_singletonPiece_disjoint (p : ConstructionParameters) (j : Fin 3) :
    WordsDisjoint (frameWordPiece p)
      (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j) :=
  (foldSites_disjoint_iff _ _).mpr (frameFold_ne_singletonPiece p j)

end ProteinFolding.Tetrahedral.NearField
