import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonFrameSeparation
import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonSeparatorSeparation
import ProteinFolding.Tetrahedral.NearFieldCanonicalSingletonLeftSeparation
import ProteinFolding.Tetrahedral.NearFieldCanonicalRingBulkColumns

/-! Positive-height standalone-vertex columns avoid all complete actual
units. Every local cap, every PPP, and both separator tethers are included. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem reservedDimerFold_ne_singletonColumn (m : ℕ) (hm : 3 ≤ m)
    (F : OctEdgeFrame) (hF : F.j = 3) (base q : ℕ) (reverse : Bool)
    (hroom : base + 2 * (q + 1) ≤ 2 * m - 1) (r : Fin 3) (last : Bool)
    (i : Fin (dimerChain (q + 1)).length) (n : ℕ) :
    (edgeDimerFold (by omega) F base q reverse hroom).pos i ≠
      (canonicalSingletonColumn m (by omega) r last).point n := by
  obtain ⟨a, positive, ha⟩ := canonicalSingletonOwner_vertex m r
  apply edgeDimerFold_ne_column_of_PPP_ne (by omega : 1 ≤ m) F base q reverse hroom _ _ i n
  intro j hj s t
  have hb := dimerLinkIndex_bounds base reverse j
  exact edgePPPFold_ne_vertex_column m hm F _ (by omega)
    (canonicalSingletonColumn m (by omega) r last) a positive ha
    (singletonOwner_ne_reservedEdge m hm r F hF _)
    (singletonOwner_ne_reservedEdge m hm r F hF _) s t

theorem cappedReservedInterval_ne_singletonColumn (m : ℕ) (hm : 3 ≤ m)
    (F : OctEdgeFrame) (hF : F.j = 3) (base k : ℕ) (hk : 0 < k) (reverse : Bool)
    (hroom : base + 2 * k ≤ 2 * m - 1) (C D : DanglingColumn m)
    (hC : C.owner = octEdgeZigzag m F (dimerHIndex base reverse 0 0))
    (hD : D.owner = octEdgeZigzag m F (dimerHIndex base reverse (k - 1) 1))
    (r : Fin 3) (last : Bool) (n : ℕ) (hn : 1 ≤ n)
    (i : Fin (capWord (dimerChain k)).length) :
    (cappedIntervalDimerFold (by omega) F base k hk reverse hroom C D hC hD).pos i ≠
      (canonicalSingletonColumn m (by omega) r last).point n := by
  let E := canonicalSingletonColumn m (by omega) r last
  exact transportWordFold_property (congrArg capWord (positive_dimer_word k hk))
    (cappedEdgeDimerFold (by omega : 1 ≤ m) F base (k - 1) reverse (by omega) C D hC hD)
    (fun x => x ≠ E.point n)
    (fun j => cappedEdgeDimerFold_property (by omega : 1 ≤ m) F base (k - 1)
      reverse (by omega) C D hC hD (fun x => x ≠ E.point n)
      (FarField.dangling_ne_positive_column C.seed_dangling E n hn)
      (fun t => reservedDimerFold_ne_singletonColumn m hm F hF base (k - 1)
        reverse (by omega) r last t n)
      (FarField.dangling_ne_positive_column D.seed_dangling E n hn) j) i

theorem canonicalItemPiece_ne_singletonColumn (p : ConstructionParameters) (k before s : ℕ)
    (hk : k < p.bins) (hs : 0 < s) (hload : before + s ≤ p.capacity)
    (r : Fin 3) (last : Bool) (n : ℕ) (hn : 1 ≤ n)
    (i : Fin (canonicalItemPiece p k before s hk hs hload).word.length) :
    (canonicalItemPiece p k before s hk hs hload).fold.pos i ≠
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last).point n :=
  cappedReservedInterval_ne_singletonColumn p.side (by have h := p.side_ge; omega)
    trackEdgeFrame rfl (itemTrackBase p k before) (p.itemDimers s)
    (by have h := p.itemDimers_ge s hs; omega) false (itemTrackBase_room p k before s hk hload)
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by
      rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
      exact itemLastColumn_owner p k before s hk hs hload) r last n hn i

theorem canonicalRightPiece_ne_singletonColumn (p : ConstructionParameters)
    (r : Fin 3) (last : Bool) (n : ℕ) (hn : 1 ≤ n) (i : Fin (canonicalRightPiece p).word.length) :
    (canonicalRightPiece p).fold.pos i ≠
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last).point n := by
  have hlast : dimerHIndex (rightFillerTrackBase p) false (p.rightFiller - 1) 1 = 2 * p.side - 3 := by
    rw [dimerLastIndex_odd _ _ (by have h := p.rightFiller_ge; omega) p.rightFiller_odd]
    have hm := p.side_ge
    have hside : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := rfl
    dsimp [rightFillerTrackBase]
    omega
  exact cappedReservedInterval_ne_singletonColumn p.side (by have h := p.side_ge; omega)
    trackEdgeFrame rfl (rightFillerTrackBase p) p.rightFiller (by have h := p.rightFiller_ge; omega)
    false (rightFillerTrackBase_room p) (rightFirstColumn p) (rightFinalColumn p)
    rfl (by rw [hlast]; exact rightFinalColumn_track_owner p) r last n hn i

theorem leftFillerFold_ne_singletonColumn (p : ConstructionParameters) (r : Fin 3)
    (last : Bool) (n : ℕ) (i : Fin (dimerChain p.leftFiller).length) :
    (leftFillerFold p).pos i ≠
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last).point n := by
  let C := canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last
  apply leftFillerFold_property_of_track p (fun x => x ≠ C.point n) _ _ i
  · intro heq
    exact C.point_outside n (heq ▸ leftFillerStart_mem_oct p)
  · intro j
    exact reservedDimerFold_ne_singletonColumn p.side (by have h := p.side_ge; omega)
      trackEdgeFrame rfl 0 (p.leftFiller - 1) false (leftFiller_room p) r last j n

theorem canonicalLeftPiece_ne_singletonColumn (p : ConstructionParameters) (r : Fin 3)
    (last : Bool) (n : ℕ) (hn : 1 ≤ n) (i : Fin (canonicalLeftPiece p).word.length) :
    (canonicalLeftPiece p).fold.pos i ≠
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last).point n := by
  let E := canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last
  exact frameTrack_property_of_capped_sites
    (cappedLeftFillerFold p (entryLocalColumn p none) (leftLastColumn p) rfl (leftLastColumn_owner p))
    (leftFillerFold p) (entryLocalColumn p none).seed (leftLastColumn p).seed
    (cappedLeftFillerFold_sites p _ _ rfl (leftLastColumn_owner p)) (fun x => x ≠ E.point n)
    (FarField.dangling_ne_positive_column (entryLocalColumn p none).seed_dangling E n hn)
    (fun j => leftFillerFold_ne_singletonColumn p r last n j)
    (FarField.dangling_ne_positive_column (leftLastColumn p).seed_dangling E n hn) i

theorem separatorFold_ne_singletonColumn (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (r : Fin 3) (last : Bool) (n : ℕ) (i : Fin (p.separatorWord k).length) :
    (separatorFold p k hk).pos i ≠
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last).point n := by
  apply separatorFold_property p k hk
    (fun x => x ≠ (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last).point n) _ _ _ _ _ i
  · intro j
    exact reservedDimerFold_ne_singletonColumn p.side (by have h := p.side_ge; omega)
      entryEdgeFrame rfl _ _ false (separatorEntry_room p k hk) r last j n
  · intro j
    rw [entryTetherWordFold_pos]
    exact (canonicalSingletonColumn_ne_entryTether p r last n k hk _).symm
  · intro j
    exact reservedDimerFold_ne_singletonColumn p.side (by have h := p.side_ge; omega)
      trackEdgeFrame rfl _ _ true (separatorCenter_room p k hk) r last j n
  · intro j
    rw [exitTetherWordFold_pos]
    exact (canonicalSingletonColumn_ne_exitTether p r last n k hk _).symm
  · intro j
    exact reservedDimerFold_ne_singletonColumn p.side (by have h := p.side_ge; omega)
      exitEdgeFrame rfl _ _ true (separatorExit_room p k) r last j n

theorem canonicalSeparatorPiece_ne_singletonColumn (p : ConstructionParameters) (k : Fin (p.bins + 1))
    (r : Fin 3) (last : Bool) (n : ℕ) (hn : 1 ≤ n)
    (i : Fin (canonicalSeparatorPiece p k).word.length) :
    (canonicalSeparatorPiece p k).fold.pos i ≠
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last).point n := by
  have hk : k.val ≤ p.bins := by have h := k.isLt; omega
  let E := canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last
  exact frameTrack_property_of_capped_sites
    (cappedSeparatorFold p k.val hk (entryLocalColumn p (some k)) (exitCapColumn p k.val hk)
      rfl (exitCapColumn_owner p k.val hk)) (separatorFold p k.val hk)
    (entryLocalColumn p (some k)).seed (exitCapColumn p k.val hk).seed
    (cappedSeparatorFold_sites p k.val hk _ _ rfl (exitCapColumn_owner p k.val hk))
    (fun x => x ≠ E.point n)
    (FarField.dangling_ne_positive_column (entryLocalColumn p (some k)).seed_dangling E n hn)
    (fun j => separatorFold_ne_singletonColumn p k.val hk r last n j)
    (FarField.dangling_ne_positive_column (exitCapColumn p k.val hk).seed_dangling E n hn) i

theorem canonicalLocal_ne_singletonColumn (p : ConstructionParameters)
    (ha : (bulkFiniteGraph p.side).IsAcyclic) (r : Fin 3) (last : Bool) (n : ℕ) (hn : 1 ≤ n) :
    CanonicalLocalProperty p ha (fun q => ∀ i,
      q.fold.pos i ≠ (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last).point n) where
  singleton s i := canonicalSingletonPiece_ne_positiveColumn p.side (by have h := p.side_ge; omega)
    s (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last) n hn i
  frame i := frameFold_ne_canonicalSingletonColumn p r last n i
  separator k i := canonicalSeparatorPiece_ne_singletonColumn p k r last n hn i
  left i := canonicalLeftPiece_ne_singletonColumn p r last n hn i
  item k before s hk hs hload i := canonicalItemPiece_ne_singletonColumn p k before s hk hs hload r last n hn i
  right i := canonicalRightPiece_ne_singletonColumn p r last n hn i
  ring s i := canonicalRingWordPiece_ne_vertexForFacesColumn p s
    (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last) r.castSucc 3 rfl i n
  bulk j i := canonicalBulkPiece_ne_positiveColumn p ha j
    (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last) n hn i

theorem canonicalUnitPieces_ne_singletonColumn (p : ConstructionParameters) (items : List ℕ)
    (d : PackedBins p items) (ha : (bulkFiniteGraph p.side).IsAcyclic)
    (r : Fin 3) (last : Bool) (n : ℕ) (hn : 1 ≤ n)
    (q : PositionedWord) (hq : q ∈ canonicalUnitPieces p items d ha) (i : Fin q.word.length) :
    q.fold.pos i ≠ (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last).point n :=
  canonicalUnitPieces_property p items d ha _
    (terminalWordPiece_ne_positiveColumn p
      (canonicalSingletonColumn p.side (by have h := p.side_ge; omega) r last) n hn)
    (canonicalLocal_ne_singletonColumn p ha r last n hn) q hq i

end ProteinFolding.Tetrahedral.NearField
