import ProteinFolding.Tetrahedral.NearFieldIntervalPieces
import ProteinFolding.Tetrahedral.NearFieldSeparatorChains

/-! Exact item and right-filler intervals of a positive-capacity packing.
The item before and load are measured before scaling. -/

namespace ProteinFolding.Tetrahedral.NearField

def itemTrackBase (p : ConstructionParameters) (k before : ℕ) : ℕ :=
  2 * (p.separatorIndex k + 2 + p.scale * before)

def rightFillerTrackBase (p : ConstructionParameters) : ℕ :=
  2 * (p.separatorIndex p.bins + 2)

theorem dimerLastIndex_even (base n : ℕ) (hn : 0 < n) (heven : n % 2 = 0) :
    dimerHIndex base false (n - 1) 1 = base + 2 * n - 2 := by
  dsimp [dimerHIndex, dimerFlip]
  omega

theorem dimerLastIndex_odd (base n : ℕ) (hn : 0 < n) (hodd : n % 2 = 1) :
    dimerHIndex base false (n - 1) 1 = base + 2 * n - 1 := by
  dsimp [dimerHIndex, dimerFlip]
  omega

theorem itemTrackBase_end_le (p : ConstructionParameters) (k before s : ℕ)
    (hload : before + s ≤ p.capacity) :
    itemTrackBase p k before + 2 * p.itemDimers s ≤ 2 * p.separatorIndex (k + 1) := by
  have hscaled : p.scale * before + p.itemDimers s ≤ p.binDimers := by
    change p.scale * before + p.scale * s ≤ p.scale * p.capacity
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left p.scale hload
  have hs : p.separatorIndex (k + 1) = p.separatorIndex k + p.binDimers + 2 := by
    unfold ConstructionParameters.separatorIndex
    ring
  rw [hs]
  dsimp [itemTrackBase]
  omega

theorem itemTrackBase_room (p : ConstructionParameters) (k before s : ℕ) (hk : k < p.bins)
    (hload : before + s ≤ p.capacity) :
    itemTrackBase p k before + 2 * p.itemDimers s ≤ 2 * p.side - 1 := by
  have h := itemTrackBase_end_le p k before s hload
  have hr := separatorCenter_room p (k + 1) (by omega)
  omega

theorem rightFillerTrackBase_room (p : ConstructionParameters) :
    rightFillerTrackBase p + 2 * p.rightFiller ≤ 2 * p.side - 1 := by
  have hm := p.side_ge
  change 2 * (p.separatorIndex p.bins + 2) + 2 * p.rightFiller ≤ 2 * p.side - 1
  have hs : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := rfl
  omega

def itemWordPiece (p : ConstructionParameters) (k before s : ℕ) (hk : k < p.bins)
    (hs : 0 < s) (hload : before + s ≤ p.capacity) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side trackEdgeFrame (itemTrackBase p k before))
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame
      (itemTrackBase p k before + 2 * p.itemDimers s - 2)) : PositionedWord :=
  cappedIntervalDimerPiece (m := p.side) (by have h := p.side_ge; omega) trackEdgeFrame
    (itemTrackBase p k before) (p.itemDimers s) (by have h := p.itemDimers_ge s hs; omega) false
    (itemTrackBase_room p k before s hk hload) C D
    (by simpa only [dimerHIndex, dimerFlip] using hC)
    (by rw [dimerLastIndex_even _ _ (by have h := p.itemDimers_ge s hs; omega) (p.itemDimers_even s)]; exact hD)

def rightFillerWordPiece (p : ConstructionParameters) (C D : DanglingColumn p.side)
    (hC : C.owner = octEdgeZigzag p.side trackEdgeFrame (rightFillerTrackBase p))
    (hD : D.owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.side - 3)) : PositionedWord :=
  cappedIntervalDimerPiece (m := p.side) (by have h := p.side_ge; omega) trackEdgeFrame
    (rightFillerTrackBase p) p.rightFiller (by have h := p.rightFiller_ge; omega) false
    (rightFillerTrackBase_room p) C D
    (by simpa only [dimerHIndex, dimerFlip] using hC)
    (by
      rw [dimerLastIndex_odd _ _ (by have h := p.rightFiller_ge; omega) p.rightFiller_odd]
      have hm := p.side_ge
      have hs : p.side = p.separatorIndex p.bins + p.rightFiller + 3 := rfl
      have hi : rightFillerTrackBase p + 2 * p.rightFiller - 1 = 2 * p.side - 3 := by
        dsimp [rightFillerTrackBase]
        omega
      rw [hi]
      exact hD)

end ProteinFolding.Tetrahedral.NearField
