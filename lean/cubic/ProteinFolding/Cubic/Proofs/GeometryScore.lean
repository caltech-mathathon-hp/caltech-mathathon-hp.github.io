import ProteinFolding.Cubic.Proofs.GeometryBound
import ProteinFolding.Cubic.Proofs.GeometryBonds

/-! Fact 3.1's score bound and the forward direction of Theorem 3.2. -/

namespace ProteinFolding.CubicGeometry

theorem bondCount_le_cube (S : Sequence) (f : Fold cubicLattice S.length) (n : ℕ)
    (hc : hydrophobicCount S = n ^ 3) : bondCount S f ≤ 3 * n ^ 2 * (n - 1) := by
  rw [bondCount_eq_positiveEdgeCount]
  exact positiveEdgeCount_le_cube _ _ ((hSupport_card S f).trans hc)

theorem packsCube_bondCount (S : Sequence) (f : Fold cubicLattice S.length) (n : ℕ)
    (hp : PacksCube S f n) : bondCount S f = 3 * n ^ 2 * (n - 1) := by
  obtain ⟨a, ha⟩ := (packsCube_iff_finset S f n).mp hp
  rw [bondCount_eq_positiveEdgeCount, ha, positiveEdgeCount_cubeFinset]

theorem perfect_implies_threshold (I : PerfectInstance) :
    I.Accepts → HPStringFold (G := cubicLattice) I.sequence (cubeBondThreshold I.side) := by
  rintro ⟨f, hp⟩
  refine ⟨f, ?_⟩
  rw [packsCube_bondCount I.sequence f I.side hp]
  exact le_rfl

theorem threshold_forces_maximal_bonds (S : Sequence) (f : Fold cubicLattice S.length)
    (n : ℕ) (hc : hydrophobicCount S = n ^ 3)
    (ht : cubeBondThreshold n ≤ (bondCount S f : ℤ)) :
    bondCount S f = 3 * n ^ 2 * (n - 1) := by
  have hupper := bondCount_le_cube S f n hc
  change ((3 * n ^ 2 * (n - 1) : ℕ) : ℤ) ≤ (bondCount S f : ℤ) at ht
  omega

end ProteinFolding.CubicGeometry
