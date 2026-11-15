import ProteinFolding.Tetrahedral.NearFieldSeparatorFold
import ProteinFolding.Tetrahedral.NearFieldSeparatorFamilyChains

/-! Whole separator words at distinct prescribed indices are disjoint. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

inductive SeparatorPiece where
  | entry | entryTether | center | exitTether | exit

def separatorPieceWord (p : ConstructionParameters) (k : ℕ) : SeparatorPiece → Sequence
  | .entry => dimerChain 1
  | .entryTether => List.replicate (p.entryTether k) .P
  | .center => dimerChain 2
  | .exitTether => List.replicate (p.exitTether k) .P
  | .exit => dimerChain 3

def separatorPieceFold (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (a : SeparatorPiece) : Fold tetrahedralLattice (separatorPieceWord p k a).length :=
  match a with
  | .entry => separatorEntryChain p k hk
  | .entryTether => entryTetherWordFold p k hk
  | .center => separatorCenterChain p k hk
  | .exitTether => exitTetherWordFold p k hk
  | .exit => separatorExitChain p k

theorem separatorFold_pos_cases (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (p.separatorWord k).length) :
    ∃ a : SeparatorPiece, ∃ j, (separatorPieceFold p k hk a).pos j = (separatorFold p k hk).pos i := by
  apply separatorFold_property p k hk
    (fun x => ∃ a : SeparatorPiece, ∃ j, (separatorPieceFold p k hk a).pos j = x) _ _ _ _ _ i
  · intro j; exact ⟨.entry, j, rfl⟩
  · intro j; exact ⟨.entryTether, j, rfl⟩
  · intro j; exact ⟨.center, j, rfl⟩
  · intro j; exact ⟨.exitTether, j, rfl⟩
  · intro j; exact ⟨.exit, j, rfl⟩

theorem entryTetherWords_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l)
    (i : Fin (List.replicate (p.entryTether k) Residue.P).length)
    (j : Fin (List.replicate (p.entryTether l) Residue.P).length) :
    (entryTetherWordFold p k hk).pos i ≠ (entryTetherWordFold p l hl).pos j := by
  rw [entryTetherWordFold_pos, entryTetherWordFold_pos]
  exact entryTethers_disjoint p k l hk hl hne _ _

theorem exitTetherWords_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l)
    (i : Fin (List.replicate (p.exitTether k) Residue.P).length)
    (j : Fin (List.replicate (p.exitTether l) Residue.P).length) :
    (exitTetherWordFold p k hk).pos i ≠ (exitTetherWordFold p l hl).pos j := by
  rw [exitTetherWordFold_pos, exitTetherWordFold_pos]
  exact exitTethers_disjoint p k l hk hl hne _ _

theorem separatorPieces_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l) (a b : SeparatorPiece)
    (i : Fin (separatorPieceWord p k a).length) (j : Fin (separatorPieceWord p l b).length) :
    (separatorPieceFold p k hk a).pos i ≠ (separatorPieceFold p l hl b).pos j := by
  cases a <;> cases b
  · exact separatorEntry_entry_disjoint p k l hk hl hne i j
  · exact separatorEntry_ne_entryWord p k l hk hl i j
  · exact separatorEntry_center_disjoint p k l hk hl i j
  · exact separatorEntry_ne_exitWord p k l hk hl i j
  · exact separatorEntry_exit_disjoint p k l hk i j
  · exact (separatorEntry_ne_entryWord p l k hl hk j i).symm
  · exact entryTetherWords_disjoint p k l hk hl hne i j
  · exact (separatorCenter_ne_entryWord p l k hl hk j i).symm
  · exact entryWord_ne_exitWord p k l hk hl i j
  · exact (separatorExit_ne_entryWord p l k hk j i).symm
  · exact (separatorEntry_center_disjoint p l k hl hk j i).symm
  · exact separatorCenter_ne_entryWord p k l hk hl i j
  · exact separatorCenter_center_disjoint p k l hk hl hne i j
  · exact separatorCenter_ne_exitWord p k l hk hl i j
  · exact separatorCenter_exit_disjoint p k l hk i j
  · exact (separatorEntry_ne_exitWord p l k hl hk j i).symm
  · exact (entryWord_ne_exitWord p l k hl hk j i).symm
  · exact (separatorCenter_ne_exitWord p l k hl hk j i).symm
  · exact exitTetherWords_disjoint p k l hk hl hne i j
  · exact (separatorExit_ne_exitWord p l k hk j i).symm
  · exact (separatorEntry_exit_disjoint p l k hl j i).symm
  · exact separatorExit_ne_entryWord p k l hl i j
  · exact (separatorCenter_exit_disjoint p l k hl j i).symm
  · exact separatorExit_ne_exitWord p k l hl i j
  · exact separatorExit_exit_disjoint p k l hk hl hne i j

theorem separatorFolds_disjoint (p : ConstructionParameters) (k l : ℕ)
    (hk : k ≤ p.bins) (hl : l ≤ p.bins) (hne : k ≠ l)
    (i : Fin (p.separatorWord k).length) (j : Fin (p.separatorWord l).length) :
    (separatorFold p k hk).pos i ≠ (separatorFold p l hl).pos j := by
  intro heq
  obtain ⟨a, r, hr⟩ := separatorFold_pos_cases p k hk i
  obtain ⟨b, s, hs⟩ := separatorFold_pos_cases p l hl j
  exact separatorPieces_disjoint p k l hk hl hne a b r s (hr.trans (heq.trans hs.symm))

end ProteinFolding.Tetrahedral.NearField
