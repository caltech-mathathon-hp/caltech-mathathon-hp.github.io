import ProteinFolding.Tetrahedral.NearFieldRowCornerEnds
import ProteinFolding.Tetrahedral.TetherRouteParameters

/-! The two concrete row corners of every entry and exit tether. The
parameters are the reduction's actual parameters, with zero-based k. -/

namespace ProteinFolding.Tetrahedral.NearField

open ConstructionParameters

def entryRowCount (p : ConstructionParameters) (k : ℕ) : ℕ :=
  (2 * (3 * (k + 1) + 1) + 1) + (2 * p.separatorIndex k + 1) - 1

def exitRowCount (p : ConstructionParameters) (k : ℕ) : ℕ :=
  (2 * (p.side - 2 - p.separatorIndex k) + 1) + (2 * (5 * p.exitSlot k + 4) + 1) - 1

theorem entryRow_faceEquation (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    (p.side - 3 - 3 * (k + 1) + p.entrySkin k) + (3 * (k + 1) + p.entrySkin k) + 1 + 2 =
      p.side + 2 * p.entrySkin k := by
  have h := p.entry_column_triangle_room k hk
  omega

theorem exitRow_faceEquation (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    (p.side - 3 - p.separatorIndex k + p.exitSkin k) + (p.exitSkin k - 1) +
      (p.separatorIndex k + 2) + 2 = p.side + 2 * p.exitSkin k := by
  have h := p.separator_room k hk
  have hj := p.tether_skin_bounds k hk
  omega

def entryRowFold (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (entryRowCount p k) :=
  rowCBFold p.side (p.entrySkin k)
    (p.side - 3 - 3 * (k + 1) + p.entrySkin k) (3 * (k + 1) + p.entrySkin k) 1
    (3 * (k + 1) + 1) (p.separatorIndex k) (entryRow_faceEquation p k hk)
    (by have h := p.tether_skin_bounds k hk; omega)

def exitRowFold (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    Fold tetrahedralLattice (exitRowCount p k) :=
  rowBAFold p.side (p.exitSkin k)
    (p.side - 3 - p.separatorIndex k + p.exitSkin k) (p.exitSkin k - 1)
    (p.separatorIndex k + 2) (p.side - 2 - p.separatorIndex k) (5 * p.exitSlot k + 4)
    (exitRow_faceEquation p k hk)
    (by have h := p.separator_room k hk; have hj := p.tether_skin_bounds k hk; omega)

theorem entryRow_mem_skin (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (entryRowCount p k)) : (entryRowFold p k hk).pos i ∈ skin p.side (p.entrySkin k) := by
  apply rowCBFold_mem_skin
  · have h := p.separator_room k hk
    have ht := p.entry_column_triangle_room k hk
    omega
  · have h := p.tether_skin_bounds k hk; omega
  · omega
  · have h := p.tether_skin_bounds k hk; omega

theorem exitRow_mem_skin (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (exitRowCount p k)) : (exitRowFold p k hk).pos i ∈ skin p.side (p.exitSkin k) := by
  apply rowBAFold_mem_skin
  · have h := p.exit_column_triangle_room k
    have hr := p.separator_room k hk
    omega
  · have h := p.tether_skin_bounds k hk; omega
  · have h := p.tether_skin_bounds k hk; omega
  · have h := p.tether_skin_bounds k hk
    have hr := p.separator_room k hk
    omega

theorem entryRow_first (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (entryRowCount p k)) (hi : i.val = 0) :
    (entryRowFold p k hk).pos i = faceSurfaceSite p.side (p.entrySkin k)
      (p.side - 3 - 3 * (k + 1) + p.entrySkin k) (3 * (k + 1) + p.entrySkin k) 1
      (entryRow_faceEquation p k hk) := by
  exact rowCBFold_first _ _ _ _ _ _ _ _ _ i hi

theorem entryRow_last (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (entryRowCount p k)) (hi : i.val + 1 = entryRowCount p k) :
    (entryRowFold p k hk).pos i = faceSurfaceSite p.side (p.entrySkin k)
      (p.side - 2 - p.separatorIndex k + p.entrySkin k) (p.entrySkin k - 1)
      (p.separatorIndex k + 1)
      (by have hr := p.separator_room k hk; have hj := p.tether_skin_bounds k hk; omega) := by
  have hr := p.separator_room k hk
  have ht := p.entry_column_triangle_room k hk
  have hj := p.tether_skin_bounds k hk
  unfold entryRowFold
  rw [rowCBFold_last _ _ _ _ _ _ _ _ _ (by omega) i hi]
  congr 1 <;> omega

theorem exitRow_first (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (exitRowCount p k)) (hi : i.val = 0) :
    (exitRowFold p k hk).pos i = faceSurfaceSite p.side (p.exitSkin k)
      (p.side - 3 - p.separatorIndex k + p.exitSkin k) (p.exitSkin k - 1)
      (p.separatorIndex k + 2) (exitRow_faceEquation p k hk) := by
  exact rowBAFold_first _ _ _ _ _ _ _ _ _ i hi

theorem exitRow_last (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins)
    (i : Fin (exitRowCount p k)) (hi : i.val + 1 = exitRowCount p k) :
    (exitRowFold p k hk).pos i = faceSurfaceSite p.side (p.exitSkin k)
      (p.exitSkin k - 1) (5 * p.exitSlot k + 3 + p.exitSkin k) (p.side - 4 - 5 * p.exitSlot k)
      (by have hr := p.exit_column_triangle_room k; have hj := p.tether_skin_bounds k hk; omega) := by
  have hr := p.separator_room k hk
  have ht := p.exit_column_triangle_room k
  have hj := p.tether_skin_bounds k hk
  unfold exitRowFold
  rw [rowBAFold_last _ _ _ _ _ _ _ _ _ (by omega) i hi]
  congr 1 <;> omega

theorem entryRowCount_add_columnCounts (p : ConstructionParameters) (k : ℕ) :
    entryRowCount p k + 4 * p.entrySkin k - 2 = p.entryTether k := by
  rw [← p.entryRouteSiteCount_eq_tether k]
  unfold entryRowCount entryRouteSiteCount entrySkin
  omega

theorem exitRowCount_add_columnCounts (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    exitRowCount p k + 4 * p.exitSkin k - 2 = p.exitTether k := by
  rw [← p.exitRouteSiteCount_eq_tether k hk]
  unfold exitRowCount exitRouteSiteCount exitSkin
  omega

end ProteinFolding.Tetrahedral.NearField
