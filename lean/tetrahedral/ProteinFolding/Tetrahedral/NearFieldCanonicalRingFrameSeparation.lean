import ProteinFolding.Tetrahedral.NearFieldCanonicalRings
import ProteinFolding.Tetrahedral.NearFieldLinkerAssembly
import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletons
import ProteinFolding.Tetrahedral.NearFieldActualFrameFold
import ProteinFolding.Tetrahedral.NearFieldFrameTrackCoreSeparation

/-! Whole-unit ring separation from the actual complete frame and the three
standalone PHP units. Both local caps are included in every statement. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem canonicalRingWordPiece_ne_frameCoreFold (p : ConstructionParameters) (i : Fin 3)
    (r : Fin (canonicalRingWordPiece p i).word.length)
    (s : Fin (p.framePart1 ++ p.framePart2).length) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (frameCoreFold p).pos s :=
  frameCoreFold_property p (fun x => (canonicalRingWordPiece p i).fold.pos r ≠ x)
    (fun j t => canonicalRingWordPiece_ne_frameCorePiece p i j r t) s

theorem canonicalRingWordPiece_ne_frameEndpointCap (p : ConstructionParameters) (i : Fin 3)
    (b : Bool) (r : Fin (canonicalRingWordPiece p i).word.length) :
    (canonicalRingWordPiece p i).fold.pos r ≠
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) b).seed := by
  cases b
  · exact canonicalRingWordPiece_ne_vertexColumn p i
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) false) 0 true rfl r 0
  · exact canonicalRingWordPiece_ne_vertexColumn p i
      (frameEndpointColumn (m := p.side) (by have h := p.side_ge; omega) true) 2 false rfl r 0

theorem canonicalRingWordPiece_ne_frameFold (p : ConstructionParameters) (i : Fin 3)
    (r : Fin (canonicalRingWordPiece p i).word.length) (s : Fin p.frameWord.length) :
    (canonicalRingWordPiece p i).fold.pos r ≠ (frameFold p).pos s :=
  frameTrack_property_of_capped_sites (frameFold p) (frameCoreFold p)
    (frameFirstColumn p).seed (frameLastColumn p).seed (frameFold_sites p)
    (fun x => (canonicalRingWordPiece p i).fold.pos r ≠ x)
    (canonicalRingWordPiece_ne_frameEndpointCap p i true r)
    (canonicalRingWordPiece_ne_frameCoreFold p i r)
    (canonicalRingWordPiece_ne_frameEndpointCap p i false r) s

theorem canonicalRingWordPiece_frameWordPiece_disjoint (p : ConstructionParameters) (i : Fin 3) :
    WordsDisjoint (canonicalRingWordPiece p i) (frameWordPiece p) :=
  (foldSites_disjoint_iff _ _).mpr (canonicalRingWordPiece_ne_frameFold p i)

theorem canonicalRingWordPiece_ne_singletonPiece (p : ConstructionParameters) (i j : Fin 3)
    (r : Fin (canonicalRingWordPiece p i).word.length)
    (s : Fin (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j).word.length) :
    (canonicalRingWordPiece p i).fold.pos r ≠
      (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j).fold.pos s := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  intro heq
  have hmem := (mem_foldSites (canonicalSingletonPiece p.side hm j).fold _).mpr ⟨s, heq.symm⟩
  rw [canonicalSingletonPiece_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · exact canonicalRingWordPiece_ne_vertexForFacesColumn p i
      (canonicalSingletonColumn p.side hm j false) j.castSucc 3 rfl r 0 h
  · exact canonicalRingWordPiece_ne_vertexForFaces p i j.castSucc 3 r h
  · exact canonicalRingWordPiece_ne_vertexForFacesColumn p i
      (canonicalSingletonColumn p.side hm j true) j.castSucc 3 rfl r 0 h

theorem canonicalRingWordPiece_singletonPiece_disjoint (p : ConstructionParameters) (i j : Fin 3) :
    WordsDisjoint (canonicalRingWordPiece p i)
      (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j) :=
  (foldSites_disjoint_iff _ _).mpr (canonicalRingWordPiece_ne_singletonPiece p i j)

end ProteinFolding.Tetrahedral.NearField
