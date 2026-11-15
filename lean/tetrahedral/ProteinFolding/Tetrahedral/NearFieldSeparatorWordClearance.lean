import ProteinFolding.Tetrahedral.NearFieldSeparatorTetherClearance
import ProteinFolding.Tetrahedral.NearFieldTetherWordFolds

/-! Separation consumers with exactly the literal word-index types. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

theorem separatorEntry_ne_entryWord (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (i : Fin (dimerChain 1).length)
    (j : Fin (List.replicate (p.entryTether l) Residue.P).length) :
    (separatorEntryChain p k hk).pos i ≠ (entryTetherWordFold p l hl).pos j := by
  rw [entryTetherWordFold_pos]
  simpa only [tetherFold] using separatorEntryChain_ne_tether p k hk (false, ⟨l, by omega⟩) i ⟨j.val, by simpa using j.isLt⟩

theorem separatorEntry_ne_exitWord (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (i : Fin (dimerChain 1).length)
    (j : Fin (List.replicate (p.exitTether l) Residue.P).length) :
    (separatorEntryChain p k hk).pos i ≠ (exitTetherWordFold p l hl).pos j := by
  rw [exitTetherWordFold_pos]
  simpa only [tetherFold] using separatorEntryChain_ne_tether p k hk (true, ⟨l, by omega⟩) i ⟨j.val, by simpa using j.isLt⟩

theorem separatorCenter_ne_entryWord (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (i : Fin (dimerChain 2).length)
    (j : Fin (List.replicate (p.entryTether l) Residue.P).length) :
    (separatorCenterChain p k hk).pos i ≠ (entryTetherWordFold p l hl).pos j := by
  rw [entryTetherWordFold_pos]
  simpa only [tetherFold] using separatorCenterChain_ne_tether p k hk (false, ⟨l, by omega⟩) i ⟨j.val, by simpa using j.isLt⟩

theorem separatorCenter_ne_exitWord (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (i : Fin (dimerChain 2).length)
    (j : Fin (List.replicate (p.exitTether l) Residue.P).length) :
    (separatorCenterChain p k hk).pos i ≠ (exitTetherWordFold p l hl).pos j := by
  rw [exitTetherWordFold_pos]
  simpa only [tetherFold] using separatorCenterChain_ne_tether p k hk (true, ⟨l, by omega⟩) i ⟨j.val, by simpa using j.isLt⟩

theorem separatorExit_ne_entryWord (p : ConstructionParameters) (k l : ℕ)
    (hl : l ≤ p.bins) (i : Fin (dimerChain 3).length)
    (j : Fin (List.replicate (p.entryTether l) Residue.P).length) :
    (separatorExitChain p k).pos i ≠ (entryTetherWordFold p l hl).pos j := by
  rw [entryTetherWordFold_pos]
  simpa only [tetherFold] using separatorExitChain_ne_tether p k (false, ⟨l, by omega⟩) i ⟨j.val, by simpa using j.isLt⟩

theorem separatorExit_ne_exitWord (p : ConstructionParameters) (k l : ℕ)
    (hl : l ≤ p.bins) (i : Fin (dimerChain 3).length)
    (j : Fin (List.replicate (p.exitTether l) Residue.P).length) :
    (separatorExitChain p k).pos i ≠ (exitTetherWordFold p l hl).pos j := by
  rw [exitTetherWordFold_pos]
  simpa only [tetherFold] using separatorExitChain_ne_tether p k (true, ⟨l, by omega⟩) i ⟨j.val, by simpa using j.isLt⟩

theorem entryWord_ne_exitWord (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins)
    (i : Fin (List.replicate (p.entryTether k) Residue.P).length)
    (j : Fin (List.replicate (p.exitTether l) Residue.P).length) :
    (entryTetherWordFold p k hk).pos i ≠ (exitTetherWordFold p l hl).pos j := by
  rw [entryTetherWordFold_pos, exitTetherWordFold_pos]
  exact entry_exit_tethers_disjoint p k l hk hl _ _

end ProteinFolding.Tetrahedral.NearField
