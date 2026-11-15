import ProteinFolding.Tetrahedral.NearFieldTetherFamily
import ProteinFolding.Tetrahedral.OctahedralTrackGeometry

/-! The route caps belong to exactly the entry, separator, and exit H-sites
prescribed by the literal reduction layout. -/

namespace ProteinFolding.Tetrahedral.NearField

theorem entrySource_owner (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    (faceDanglingColumn p.side (entryAnchorA p k) (3 * (k + 1)) 0 (entryAnchor_equation p k hk)).owner =
      octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1) + 1) := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have ht := p.entry_column_triangle_room k hk
  apply Subtype.ext
  funext c
  rw [entryEdgeZigzag_coordinates hm]
  fin_cases c <;> dsimp [faceDanglingColumn, faceSurfaceSite, faceSurfaceCoordinates,
    entryEdgeCoordinates, entryAnchorA, octRadius] <;> omega

theorem entryTarget_owner (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    (entryTargetColumn p k hk).owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.separatorIndex k + 1) := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hr := p.separator_room k hk
  apply Subtype.ext
  funext c
  rw [trackEdgeZigzag_coordinates hm]
  fin_cases c <;> dsimp [entryTargetColumn, faceDanglingColumn, faceSurfaceSite,
    faceSurfaceCoordinates, trackEdgeCoordinates, octRadius] <;> omega

theorem exitSource_owner (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    (exitSourceColumn p k hk).owner = octEdgeZigzag p.side trackEdgeFrame (2 * p.separatorIndex k + 3) := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have hr := p.separator_room k hk
  apply Subtype.ext
  funext c
  rw [trackEdgeZigzag_coordinates hm]
  fin_cases c <;> dsimp [exitSourceColumn, faceDanglingColumn, faceSurfaceSite,
    faceSurfaceCoordinates, trackEdgeCoordinates, octRadius] <;> omega

theorem exitTarget_owner (p : ConstructionParameters) (k : ℕ) :
    (exitTargetColumn p k).owner = octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 7) := by
  have hm : 1 ≤ p.side := by have h := p.side_ge; omega
  have ht := p.exit_column_triangle_room k
  apply Subtype.ext
  funext c
  rw [exitEdgeZigzag_coordinates hm]
  fin_cases c <;> dsimp [exitTargetColumn, faceDanglingColumn, faceSurfaceSite,
    faceSurfaceCoordinates, exitEdgeCoordinates, octRadius] <;> omega

theorem entrySource_adj (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    tetrahedralLattice.Adj (octEdgeZigzag p.side entryEdgeFrame (6 * (k + 1) + 1))
      (faceDanglingColumn p.side (entryAnchorA p k) (3 * (k + 1)) 0 (entryAnchor_equation p k hk)).seed := by
  rw [← entrySource_owner p k hk]
  exact step_adj _ _

theorem entryTarget_adj (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    tetrahedralLattice.Adj (entryTargetColumn p k hk).seed
      (octEdgeZigzag p.side trackEdgeFrame (2 * p.separatorIndex k + 1)) := by
  rw [← entryTarget_owner p k hk]
  exact (step_adj _ _).symm

theorem exitSource_adj (p : ConstructionParameters) (k : ℕ) (hk : k ≤ p.bins) :
    tetrahedralLattice.Adj (octEdgeZigzag p.side trackEdgeFrame (2 * p.separatorIndex k + 3))
      (exitSourceColumn p k hk).seed := by
  rw [← exitSource_owner p k hk]
  exact step_adj _ _

theorem exitTarget_adj (p : ConstructionParameters) (k : ℕ) :
    tetrahedralLattice.Adj (exitTargetColumn p k).seed
      (octEdgeZigzag p.side exitEdgeFrame (10 * p.exitSlot k + 7)) := by
  rw [← exitTarget_owner p k]
  exact (step_adj _ _).symm

end ProteinFolding.Tetrahedral.NearField
