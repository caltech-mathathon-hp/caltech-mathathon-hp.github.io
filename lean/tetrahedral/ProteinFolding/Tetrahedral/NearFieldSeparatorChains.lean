import ProteinFolding.Tetrahedral.NearFieldDimerChainCaps
import ProteinFolding.Tetrahedral.NearFieldTetherOwners

/-! The three literal H-chain pieces in each actual separator unit. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

theorem separatorEntry_room (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    6 * (k + 1) + 2 * (0 + 1) ≤ 2 * p.side - 1 := by
  have h := p.entry_column_triangle_room k hk
  omega

theorem separatorCenter_room (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    2 * p.separatorIndex k + 2 * (1 + 1) ≤ 2 * p.side - 1 := by
  have h := p.separator_room k hk
  omega

theorem separatorExit_room (p : ConstructionParameters) (k : ℕ) :
    (10 * p.exitSlot k + 6) + 2 * (2 + 1) ≤ 2 * p.side - 1 := by
  have h := p.exit_column_triangle_room k
  omega

def separatorEntryChain (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (dimerChain 1).length :=
  edgeDimerFold (by have h := p.side_ge; omega) entryEdgeFrame (6 * (k + 1)) 0 false (separatorEntry_room p k hk)

def separatorCenterChain (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (dimerChain 2).length :=
  edgeDimerFold (by have h := p.side_ge; omega) trackEdgeFrame (2 * p.separatorIndex k) 1 true (separatorCenter_room p k hk)

def separatorExitChain (p : ConstructionParameters) (k : ℕ) :
    Fold tetrahedralLattice (dimerChain 3).length :=
  edgeDimerFold (by have h := p.side_ge; omega) exitEdgeFrame (10 * p.exitSlot k + 6) 2 true (separatorExit_room p k)

theorem separatorEntryChain_last (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (dimerChain 1).length) (hi : i.val + 1 = (dimerChain 1).length) :
    (separatorEntryChain p k hk).pos i =
      (faceDanglingColumn p.side (entryAnchorA p k) (3 * (k + 1)) 0 (entryAnchor_equation p k hk)).owner := by
  have hiv : i.val = 1 := by
    have hl : (dimerChain 1).length = 2 := by decide
    omega
  change edgeDimerCurve p.side entryEdgeFrame (6 * (k + 1)) false i.val = _
  rw [hiv, entrySource_owner p k hk]
  exact edgeDimerCurve_H p.side entryEdgeFrame (6 * (k + 1)) false 0 1

theorem separatorCenterChain_first (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (dimerChain 2).length) (hi : i.val = 0) :
    (separatorCenterChain p k hk).pos i = (entryTargetColumn p k hk).owner := by
  change edgeDimerCurve p.side trackEdgeFrame (2 * p.separatorIndex k) true i.val = _
  rw [hi, entryTarget_owner p k hk]
  exact edgeDimerCurve_H p.side trackEdgeFrame (2 * p.separatorIndex k) true 0 0

theorem separatorCenterChain_last (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (dimerChain 2).length) (hi : i.val + 1 = (dimerChain 2).length) :
    (separatorCenterChain p k hk).pos i = (exitSourceColumn p k hk).owner := by
  have hiv : i.val = 6 := by
    have hl : (dimerChain 2).length = 7 := by decide
    omega
  change edgeDimerCurve p.side trackEdgeFrame (2 * p.separatorIndex k) true i.val = _
  rw [hiv, exitSource_owner p k hk]
  exact edgeDimerCurve_H p.side trackEdgeFrame (2 * p.separatorIndex k) true 1 1

theorem separatorExitChain_first (p : ConstructionParameters) (k : ℕ)
    (i : Fin (dimerChain 3).length) (hi : i.val = 0) :
    (separatorExitChain p k).pos i = (exitTargetColumn p k).owner := by
  change edgeDimerCurve p.side exitEdgeFrame (10 * p.exitSlot k + 6) true i.val = _
  rw [hi, exitTarget_owner p k]
  exact edgeDimerCurve_H p.side exitEdgeFrame (10 * p.exitSlot k + 6) true 0 0

theorem separatorEntryChain_first (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (dimerChain 1).length) (hi : i.val = 0) :
    (separatorEntryChain p k hk).pos i = octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1)) := by
  change edgeDimerCurve p.side entryEdgeFrame (6 * (k + 1)) false i.val = _
  rw [hi]
  exact edgeDimerCurve_H p.side entryEdgeFrame (6 * (k + 1)) false 0 0

theorem separatorExitChain_last (p : ConstructionParameters) (k : ℕ)
    (i : Fin (dimerChain 3).length) (hi : i.val + 1 = (dimerChain 3).length) :
    (separatorExitChain p k).pos i = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 10) := by
  have hiv : i.val = 11 := by
    have hl : (dimerChain 3).length = 12 := by decide
    omega
  change edgeDimerCurve p.side exitEdgeFrame (10 * p.exitSlot k + 6) true i.val = _
  rw [hiv]
  exact edgeDimerCurve_H p.side exitEdgeFrame (10 * p.exitSlot k + 6) true 2 1

end ProteinFolding.Tetrahedral.NearField
