import ProteinFolding.Tetrahedral.NearFieldFrameTrackCoreSeparation
import ProteinFolding.Tetrahedral.NearFieldLinkerAssembly
import ProteinFolding.Tetrahedral.NearFieldRingFaceGeometry
import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletons
import ProteinFolding.Tetrahedral.NearFieldCanonicalRightPiece

/-! Every reserved-edge interval avoids the three standalone vertex units.
The small-face coordinate separates their H owners, including at corners;
the checked capped-chain interfaces include all exterior P sites. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem singletonOwner_ne_reservedEdge (m : ℕ) (hm : 3 ≤ m) (j : Fin 3)
    (F : OctEdgeFrame) (hF : F.j = 3) (r : ℕ) :
    canonicalSingletonOwner m j ≠ octEdgeZigzag m F r := by
  intro heq
  have hlo := ringEdgePoint_small_coordinate m hm F r
  rw [hF, ← heq] at hlo
  have hhi := (canonicalSingletonOwner_faces m j).2
  dsimp [octRadius] at hlo hhi
  omega

theorem singletonOwner_not_mem_reservedHsites (m : ℕ) (hm : 3 ≤ m) (j : Fin 3)
    (F : OctEdgeFrame) (hF : F.j = 3) (base q : ℕ) :
    canonicalSingletonOwner m j ∉ edgeDimerHsites m F base q := by
  intro hmem
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hmem
  exact singletonOwner_ne_reservedEdge m hm j F hF (base + t.val) ht.symm

theorem cappedReservedInterval_ne_singletonOwner (m : ℕ) (hm : 3 ≤ m)
    (F : OctEdgeFrame) (hF : F.j = 3) (base n : ℕ) (hn : 0 < n) (reverse : Bool)
    (hroom : base + 2 * n ≤ 2 * m - 1) (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (n - 1) 1))
    (j : Fin 3) (i : Fin (capWord (dimerChain n)).length) :
    (cappedIntervalDimerFold (by omega) F base n hn reverse hroom C D hC hD).pos i ≠
      canonicalSingletonOwner m j :=
  transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
    (cappedEdgeDimerFold (by omega : 1 ≤ m) F base (n - 1) reverse (by omega) C D hC hD)
    (fun x => x ≠ canonicalSingletonOwner m j)
    (fun r => cappedEdgeDimerFold_ne_octSite_of_not_mem_Hsites (by omega : 1 ≤ m)
      F base (n - 1) reverse (by omega) C D hC hD _
      (canonicalSingletonOwner_mem m (by omega) j)
      (singletonOwner_not_mem_reservedHsites m hm j F hF base (n - 1)) r) i

theorem cappedReservedInterval_ne_singletonCap (m : ℕ) (hm : 3 ≤ m)
    (F : OctEdgeFrame) (hF : F.j = 3) (base n : ℕ) (hn : 0 < n) (reverse : Bool)
    (hroom : base + 2 * n ≤ 2 * m - 1) (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (n - 1) 1))
    (j : Fin 3) (last : Bool) (i : Fin (capWord (dimerChain n)).length) :
    (cappedIntervalDimerFold (by omega) F base n hn reverse hroom C D hC hD).pos i ≠
      (canonicalSingletonColumn m (by omega) j last).seed :=
  transportWordFold_property (congrArg capWord (positive_dimer_word n hn))
    (cappedEdgeDimerFold (by omega : 1 ≤ m) F base (n - 1) reverse (by omega) C D hC hD)
    (fun x => x ≠ (canonicalSingletonColumn m (by omega) j last).seed)
    (fun r => cappedEdgeDimerFold_ne_cap_of_owner_not_mem (by omega : 1 ≤ m)
      F base (n - 1) reverse (by omega) C D hC hD _
      (singletonOwner_not_mem_reservedHsites m hm j F hF base (n - 1)) r) i

theorem cappedReservedInterval_ne_singletonPiece (m : ℕ) (hm : 3 ≤ m)
    (F : OctEdgeFrame) (hF : F.j = 3) (base n : ℕ) (hn : 0 < n) (reverse : Bool)
    (hroom : base + 2 * n ≤ 2 * m - 1) (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (n - 1) 1))
    (j : Fin 3) (i : Fin (capWord (dimerChain n)).length)
    (s : Fin (canonicalSingletonPiece m (by omega) j).word.length) :
    (cappedIntervalDimerFold (by omega) F base n hn reverse hroom C D hC hD).pos i ≠
      (canonicalSingletonPiece m (by omega) j).fold.pos s := by
  intro heq
  have hmem := (mem_foldSites (canonicalSingletonPiece m (by omega) j).fold _).mpr ⟨s, heq.symm⟩
  rw [canonicalSingletonPiece_sites] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with (h | h) | h
  · exact cappedReservedInterval_ne_singletonCap m hm F hF base n hn reverse hroom C D hC hD j false i h
  · exact cappedReservedInterval_ne_singletonOwner m hm F hF base n hn reverse hroom C D hC hD j i h
  · exact cappedReservedInterval_ne_singletonCap m hm F hF base n hn reverse hroom C D hC hD j true i h

theorem canonicalItemPiece_ne_singletonPiece (p : ConstructionParameters) (k before n : ℕ)
    (hk : k < p.bins) (hn : 0 < n) (hload : before + n ≤ p.capacity) (j : Fin 3)
    (i : Fin (canonicalItemPiece p k before n hk hn hload).word.length)
    (s : Fin (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j).word.length) :
    (canonicalItemPiece p k before n hk hn hload).fold.pos i ≠
      (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j).fold.pos s :=
  cappedReservedInterval_ne_singletonPiece p.side (by have h := p.side_ge; omega)
    trackEdgeFrame rfl (itemTrackBase p k before) (p.itemDimers n)
    (by have h := p.itemDimers_ge n hn; omega) false (itemTrackBase_room p k before n hk hload)
    (itemFirstColumn p k before n hk hn hload) (itemLastColumn p k before n hk hn hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before n hk hn hload)
    (by
      rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge n hn; omega) (p.itemDimers_even n)]
      exact itemLastColumn_owner p k before n hk hn hload) j i s

theorem canonicalItemPiece_singletonPiece_disjoint (p : ConstructionParameters) (k before n : ℕ)
    (hk : k < p.bins) (hn : 0 < n) (hload : before + n ≤ p.capacity) (j : Fin 3) :
    WordsDisjoint (canonicalItemPiece p k before n hk hn hload)
      (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j) :=
  (foldSites_disjoint_iff _ _).mpr (canonicalItemPiece_ne_singletonPiece p k before n hk hn hload j)

theorem canonicalRightPiece_ne_singletonPiece (p : ConstructionParameters) (j : Fin 3)
    (i : Fin (canonicalRightPiece p).word.length)
    (s : Fin (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j).word.length) :
    (canonicalRightPiece p).fold.pos i ≠
      (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j).fold.pos s := by
  have hlast : dimerHIndex (rightFillerTrackBase p) false (p.rightFiller - 1) 1 = 2 * p.side - 3 := by
    rw [dimerLastIndex_odd _ _ (by have h := p.rightFiller_ge; omega) p.rightFiller_odd]
    have hm := p.side_ge
    have hside : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := rfl
    dsimp [rightFillerTrackBase]
    omega
  exact cappedReservedInterval_ne_singletonPiece p.side (by have h := p.side_ge; omega)
    trackEdgeFrame rfl (rightFillerTrackBase p) p.rightFiller (by have h := p.rightFiller_ge; omega)
    false (rightFillerTrackBase_room p) (rightFirstColumn p) (rightFinalColumn p)
    rfl (by rw [hlast]; exact rightFinalColumn_track_owner p) j i s

theorem canonicalRightPiece_singletonPiece_disjoint (p : ConstructionParameters) (j : Fin 3) :
    WordsDisjoint (canonicalRightPiece p)
      (canonicalSingletonPiece p.side (by have h := p.side_ge; omega) j) :=
  (foldSites_disjoint_iff _ _).mpr (canonicalRightPiece_ne_singletonPiece p j)

end ProteinFolding.Tetrahedral.NearField
