import ProteinFolding.Tetrahedral.NearFieldItemIntervals
import ProteinFolding.Tetrahedral.NearFieldPackedItemPlan
import ProteinFolding.Tetrahedral.NearFieldEntryCapFamily
import ProteinFolding.Tetrahedral.NearFieldUnitSupport

/-! Concrete track and corner-starting filler pieces. Their ordinary A caps
use direction 1; the first left cap is the actual borrowed-routing cap. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

def entryAColumn {m : ℕ} (hm : 1 ≤ m) (i : ℕ) (hi : i % 2 = 0)
    (hlo : 2 ≤ i) (hhi : (i : ℤ) + 2 ≤ octRadius m) : DanglingColumn m where
  owner := octEdgeZigzag m entryEdgeFrame i
  dir := 2
  owner_mem := by
    have hr : i < 2 * m - 1 := by dsimp [octRadius] at hhi; omega
    exact (octEdgeZigzag_mem hm entryEdgeFrame hr).elim (fun h => h.1.1) (fun h => h.1.1)
  seed_outside := (frameLinkerCap_dangling hm i hi hlo hhi).1

def entryLocalColumn (p : ConstructionParameters) (i : EntryCapIndex p) : DanglingColumn p.side :=
  entryAColumn (m := p.side) (by have h := p.side_ge; omega) (entryCapIndex p i)
    (entryCapIndex_even p i) (entryCapIndex_lo p i) (by have h := entryCapIndex_room p i; omega)

theorem entryLocalColumn_seed (p : ConstructionParameters) (i : EntryCapIndex p) :
    (entryLocalColumn p i).seed = entryCapSite p i := rfl

def leftLastColumn (p : ConstructionParameters) : DanglingColumn p.side :=
  trackAColumn (m := p.side) (by have h := p.side_ge; omega) (p.leftFiller - 1) (by
    have hs := p.side_eq_track
    have hl := p.leftFiller_ge
    omega)

theorem leftLastColumn_owner (p : ConstructionParameters) :
    (leftLastColumn p).owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2) := by
  change octEdgeZigzag p.side trackEdgeFrame (2 * (p.leftFiller - 1)) = _
  exact congrArg (octEdgeZigzag p.side trackEdgeFrame) (show 2 * (p.leftFiller - 1) = 2 * p.leftFiller - 2 by omega)

private theorem leftFillerWordPiece_first_seed (p : ConstructionParameters) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2)) :
    (leftFillerWordPiece p C D hC hD).first = C.seed := rfl

private theorem leftFillerWordPiece_last_seed (p : ConstructionParameters) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side entryEdgeFrame 2)
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.leftFiller - 2)) :
    (leftFillerWordPiece p C D hC hD).last = D.seed := rfl

def canonicalLeftPiece (p : ConstructionParameters) : PositionedWord :=
  leftFillerWordPiece p (entryLocalColumn p none) (leftLastColumn p) rfl (leftLastColumn_owner p)

theorem canonicalLeftPiece_word (p : ConstructionParameters) :
    (canonicalLeftPiece p).word = capWord (dimerChain p.leftFiller) := rfl

theorem canonicalLeftPiece_hSupport (p : ConstructionParameters) :
    hSupport (canonicalLeftPiece p).word (canonicalLeftPiece p).fold ⊆ octahedron p.side :=
  cappedLeftFillerFold_hSupport_subset_oct p (entryLocalColumn p none) (leftLastColumn p) rfl (leftLastColumn_owner p)

theorem canonicalLeftPiece_first (p : ConstructionParameters) :
    (canonicalLeftPiece p).first = entryCapSite p none :=
  (leftFillerWordPiece_first_seed p (entryLocalColumn p none) (leftLastColumn p) rfl
    (leftLastColumn_owner p)).trans (entryLocalColumn_seed p none)

theorem canonicalLeftPiece_last (p : ConstructionParameters) :
    (canonicalLeftPiece p).last = (leftLastColumn p).seed :=
  leftFillerWordPiece_last_seed p (entryLocalColumn p none) (leftLastColumn p) rfl (leftLastColumn_owner p)

def itemTrackAStart (p : ConstructionParameters) (k before : ℕ) : ℕ :=
  p.separatorIndex k + 2 + p.scale * before

theorem itemTrackAStart_room (p : ConstructionParameters) (k before s : ℕ) (hk : k < p.bins)
    (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    itemTrackAStart p k before < p.side ∧
      itemTrackAStart p k before + p.itemDimers s - 1 < p.side := by
  have hr := itemTrackBase_room p k before s hk hload
  have hn := p.itemDimers_ge s hs
  change 2 * itemTrackAStart p k before + 2 * p.itemDimers s ≤ 2 * p.side - 1 at hr
  omega

def itemFirstColumn (p : ConstructionParameters) (k before s : ℕ) (hk : k < p.bins)
    (hs : 0 < s) (hload : before + s ≤ p.capacity) : DanglingColumn p.side :=
  trackAColumn (m := p.side) (by have h := p.side_ge; omega)
    (itemTrackAStart p k before) (itemTrackAStart_room p k before s hk hs hload).1

def itemLastColumn (p : ConstructionParameters) (k before s : ℕ) (hk : k < p.bins)
    (hs : 0 < s) (hload : before + s ≤ p.capacity) : DanglingColumn p.side :=
  trackAColumn (m := p.side) (by have h := p.side_ge; omega)
    (itemTrackAStart p k before + p.itemDimers s - 1)
    (itemTrackAStart_room p k before s hk hs hload).2

theorem itemFirstColumn_owner (p : ConstructionParameters) (k before s : ℕ) (hk : k < p.bins)
    (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    (itemFirstColumn p k before s hk hs hload).owner =
      octEdgeZigzag p.side trackEdgeFrame (itemTrackBase p k before) := rfl

theorem itemLastColumn_owner (p : ConstructionParameters) (k before s : ℕ) (hk : k < p.bins)
    (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    (itemLastColumn p k before s hk hs hload).owner =
      octEdgeZigzag p.side trackEdgeFrame (itemTrackBase p k before + 2 * p.itemDimers s - 2) := by
  change octEdgeZigzag p.side trackEdgeFrame
    (2 * (itemTrackAStart p k before + p.itemDimers s - 1)) = _
  congr 1
  change 2 * (itemTrackAStart p k before + p.itemDimers s - 1) =
    2 * itemTrackAStart p k before + 2 * p.itemDimers s - 2
  have hn := p.itemDimers_ge s hs
  omega

def canonicalItemPiece (p : ConstructionParameters) (k before s : ℕ) (hk : k < p.bins)
    (hs : 0 < s) (hload : before + s ≤ p.capacity) : PositionedWord :=
  itemWordPiece p k before s hk hs hload
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (itemFirstColumn_owner p k before s hk hs hload) (itemLastColumn_owner p k before s hk hs hload)

theorem canonicalItemPiece_word (p : ConstructionParameters) (k before s : ℕ) (hk : k < p.bins)
    (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    (canonicalItemPiece p k before s hk hs hload).word = capWord (dimerChain (p.itemDimers s)) := rfl

theorem canonicalItemPiece_hSupport (p : ConstructionParameters) (k before s : ℕ) (hk : k < p.bins)
    (hs : 0 < s) (hload : before + s ≤ p.capacity) :
    hSupport (canonicalItemPiece p k before s hk hs hload).word
      (canonicalItemPiece p k before s hk hs hload).fold ⊆ octahedron p.side :=
  cappedIntervalDimerPiece_hSupport_subset_oct (m := p.side) (by have h := p.side_ge; omega)
    trackEdgeFrame (itemTrackBase p k before) (p.itemDimers s)
    (by have h := p.itemDimers_ge s hs; omega) false (itemTrackBase_room p k before s hk hload)
    (itemFirstColumn p k before s hk hs hload) (itemLastColumn p k before s hk hs hload)
    (by simpa only [dimerHIndex, dimerFlip] using itemFirstColumn_owner p k before s hk hs hload)
    (by
      rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]
      exact itemLastColumn_owner p k before s hk hs hload)

end ProteinFolding.Tetrahedral.NearField
