import ProteinFolding.Tetrahedral.NearFieldTetherFamily

/-! The checked tether walks, with their actual literal all-P word lengths. -/

namespace ProteinFolding.Tetrahedral.NearField

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

def entryTetherWordFold (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (List.replicate (p.entryTether k) Residue.P).length :=
  (entryTetherFold p k hk).onLength (by simp)

def exitTetherWordFold (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (List.replicate (p.exitTether k) Residue.P).length :=
  (exitTetherFold p k hk).onLength (by simp)

theorem entryTetherWordFold_pos (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (List.replicate (p.entryTether k) Residue.P).length) :
    (entryTetherWordFold p k hk).pos i =
      (entryTetherFold p k hk).pos ⟨i.val, by simpa only [List.length_replicate] using i.isLt⟩ := by
  change (entryTetherFold p k hk).pos (Fin.cast (by simp only [List.length_replicate]) i) = _
  apply congrArg (entryTetherFold p k hk).pos
  exact Fin.ext rfl

theorem exitTetherWordFold_pos (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (List.replicate (p.exitTether k) Residue.P).length) :
    (exitTetherWordFold p k hk).pos i =
      (exitTetherFold p k hk).pos ⟨i.val, by simpa only [List.length_replicate] using i.isLt⟩ := by
  change (exitTetherFold p k hk).pos (Fin.cast (by simp only [List.length_replicate]) i) = _
  apply congrArg (exitTetherFold p k hk).pos
  exact Fin.ext rfl

theorem entryTetherWordFold_first (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (List.replicate (p.entryTether k) Residue.P).length) (hi : i.val = 0) :
    (entryTetherWordFold p k hk).pos i =
      (faceDanglingColumn p.side (entryAnchorA p k) (3 * (k + 1)) 0 (entryAnchor_equation p k hk)).seed :=
  entryTetherFold_first p k hk _ hi

theorem entryTetherWordFold_last (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (List.replicate (p.entryTether k) Residue.P).length)
    (hi : i.val + 1 = (List.replicate (p.entryTether k) Residue.P).length) :
    (entryTetherWordFold p k hk).pos i = (entryTargetColumn p k hk).seed :=
  entryTetherFold_last p k hk _ (by simpa only [List.length_replicate] using hi)

theorem exitTetherWordFold_first (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (List.replicate (p.exitTether k) Residue.P).length) (hi : i.val = 0) :
    (exitTetherWordFold p k hk).pos i = (exitSourceColumn p k hk).seed :=
  exitTetherFold_first p k hk _ hi

theorem exitTetherWordFold_last (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (List.replicate (p.exitTether k) Residue.P).length)
    (hi : i.val + 1 = (List.replicate (p.exitTether k) Residue.P).length) :
    (exitTetherWordFold p k hk).pos i = (exitTargetColumn p k).seed :=
  exitTetherFold_last p k hk _ (by simpa only [List.length_replicate] using hi)

theorem entryTetherWordFold_length_pos (p : ConstructionParameters) (k : ℕ) :
    0 < (List.replicate (p.entryTether k) Residue.P).length := by
  simp only [List.length_replicate]
  unfold ConstructionParameters.entryTether
  omega

theorem exitTetherWordFold_length_pos (p : ConstructionParameters) (k : ℕ) :
    0 < (List.replicate (p.exitTether k) Residue.P).length := by
  simp only [List.length_replicate]
  unfold ConstructionParameters.exitTether
  omega

end ProteinFolding.Tetrahedral.NearField
