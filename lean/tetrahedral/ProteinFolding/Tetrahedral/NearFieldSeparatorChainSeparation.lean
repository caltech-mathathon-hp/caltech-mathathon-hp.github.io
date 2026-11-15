import ProteinFolding.Tetrahedral.NearFieldSeparatorChains
import ProteinFolding.Tetrahedral.NearFieldInnerEdgeSeparation

/-! The three actual separator-chain pieces have disjoint physical H intervals. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

theorem separatorEntry_center_Hdisjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) :
    Disjoint (edgeDimerHsites p.side entryEdgeFrame (6 * (k + 1)) 0)
      (edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex l) 1) := by
  apply edgeDimerHsites_disjoint_other_pair (by have h := p.side_ge; omega)
    entryEdgeFrame trackEdgeFrame _ _ _ _ (by omega) _ (separatorCenter_room p l hl) (Or.inl (by decide))
  have h := p.entry_column_triangle_room k hk
  omega

theorem separatorEntry_exit_Hdisjoint (p : ConstructionParameters) (k l : ℕ) (hk : k ≤ p.bins) :
    Disjoint (edgeDimerHsites p.side entryEdgeFrame (6 * (k + 1)) 0)
      (edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot l + 6) 2) := by
  apply edgeDimerHsites_disjoint_other_pair (by have h := p.side_ge; omega)
    entryEdgeFrame exitEdgeFrame _ _ _ _ (by omega) _ (separatorExit_room p l) (Or.inl (by decide))
  have h := p.entry_column_triangle_room k hk
  omega

theorem separatorCenter_exit_Hdisjoint (p : ConstructionParameters) (k l : ℕ) (hk : k ≤ p.bins) :
    Disjoint (edgeDimerHsites p.side trackEdgeFrame (2 * p.separatorIndex k) 1)
      (edgeDimerHsites p.side exitEdgeFrame (10 * p.exitSlot l + 6) 2) := by
  apply edgeDimerHsites_disjoint_other_pair (by have h := p.side_ge; omega)
    trackEdgeFrame exitEdgeFrame _ _ _ _ _ _ (separatorExit_room p l) (Or.inl (by decide))
  · have h := separatorIndex_ge_two p k
    omega
  · have h := p.separator_room k hk
    have hfill := p.rightFiller_ge
    omega

theorem separatorEntry_center_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (i : Fin (dimerChain 1).length) (j : Fin (dimerChain 2).length) :
    (separatorEntryChain p k hk).pos i ≠ (separatorCenterChain p l hl).pos j :=
  edgeDimerFolds_disjoint (by have h := p.side_ge; omega) entryEdgeFrame trackEdgeFrame
    (6 * (k + 1)) 0 (2 * p.separatorIndex l) 1 false true
    (separatorEntry_room p k hk) (separatorCenter_room p l hl) (separatorEntry_center_Hdisjoint p k l hk hl) i j

theorem separatorEntry_exit_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (i : Fin (dimerChain 1).length) (j : Fin (dimerChain 3).length) :
    (separatorEntryChain p k hk).pos i ≠ (separatorExitChain p l).pos j :=
  edgeDimerFolds_disjoint (by have h := p.side_ge; omega) entryEdgeFrame exitEdgeFrame
    (6 * (k + 1)) 0 (10 * p.exitSlot l + 6) 2 false true
    (separatorEntry_room p k hk) (separatorExit_room p l) (separatorEntry_exit_Hdisjoint p k l hk) i j

theorem separatorCenter_exit_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (i : Fin (dimerChain 2).length) (j : Fin (dimerChain 3).length) :
    (separatorCenterChain p k hk).pos i ≠ (separatorExitChain p l).pos j :=
  edgeDimerFolds_disjoint (by have h := p.side_ge; omega) trackEdgeFrame exitEdgeFrame
    (2 * p.separatorIndex k) 1 (10 * p.exitSlot l + 6) 2 true true
    (separatorCenter_room p k hk) (separatorExit_room p l) (separatorCenter_exit_Hdisjoint p k l hk) i j

end ProteinFolding.Tetrahedral.NearField
