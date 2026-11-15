import ProteinFolding.Cubic.Proofs.GeometryRigidity
import ProteinFolding.Cubic.Proofs.GeometryBonds

/-! The geometric equivalence used by Theorem 3.2 and the threshold verifier.
It is separated from the final main-theorem entry point so verifier and
reduction modules can use the geometry without an import cycle. -/

namespace ProteinFolding.CubicGeometry

theorem packsCube_iff_bond_threshold (S : Sequence) (f : Fold cubicLattice S.length)
    (n : ℕ) (hc : hydrophobicCount S = n ^ 3) :
    PacksCube S f n ↔ cubeBondThreshold n ≤ (bondCount S f : ℤ) := by
  constructor
  · intro hp
    obtain ⟨a, ha⟩ := (packsCube_iff_finset S f n).1 hp
    rw [bondCount_eq_positiveEdgeCount, ha, positiveEdgeCount_cubeFinset]
    exact le_rfl
  · intro hb
    have hnat : 3 * n ^ 2 * (n - 1) ≤ bondCount S f := by
      change ((3 * n ^ 2 * (n - 1) : ℕ) : ℤ) ≤ (bondCount S f : ℤ) at hb
      omega
    rw [bondCount_eq_positiveEdgeCount] at hnat
    have hcard : (hSupport S f).card = n ^ 3 := (hSupport_card S f).trans hc
    obtain ⟨a, ha⟩ := eq_cubeFinset_of_maximal_edges (hSupport S f) n hcard hnat
    exact (packsCube_iff_finset S f n).2 ⟨a, ha⟩

end ProteinFolding.CubicGeometry
