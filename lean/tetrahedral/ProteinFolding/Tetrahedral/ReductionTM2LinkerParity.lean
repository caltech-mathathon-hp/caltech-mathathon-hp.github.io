import ProteinFolding.Tetrahedral.ReductionTM2ColourFlagFacts
import ProteinFolding.Tetrahedral.FarFieldParity
import ProteinFolding.Tetrahedral.ConstructionParameters
import ProteinFolding.Tetrahedral.FarFieldPrescribedLength

namespace ProteinFolding.Tetrahedral.ReductionTM2

theorem longLinkerLength_uniform_bound (p : ConstructionParameters) (w : ℕ) (flag : Bool) :
    FarField.uniformLinkerLength p.side w ≤ p.longLinkerLength w flag := by
  unfold FarField.uniformLinkerLength ConstructionParameters.longLinkerLength ConstructionParameters.baseLinkerLength
  omega

theorem longLinkerLength_capParity (p : ConstructionParameters) (w : ℕ)
    (a b : Site) (flag : Bool) (hflag : flag = (FarField.colour a == FarField.colour b)) :
    FarField.CapParity a b (p.longLinkerLength w flag) := by
  rw [hflag]
  cases ha : FarField.colour a <;> cases hb : FarField.colour b <;>
    simp [FarField.CapParity, ha, hb, ConstructionParameters.longLinkerLength_parity]

theorem adjacent_caps_colours (a b acap bcap : Site)
    (ha : tetrahedralLattice.Adj a acap) (hb : tetrahedralLattice.Adj b bcap) :
    (FarField.colour acap == FarField.colour bcap) = (FarField.colour a == FarField.colour b) := by
  rw [FarField.adj_colour ha, FarField.adj_colour hb]
  cases FarField.colour a <;> cases FarField.colour b <;> rfl

theorem longLinkerLength_caps_parity (p : ConstructionParameters) (w : ℕ)
    (a b acap bcap : Site) (ha : tetrahedralLattice.Adj a acap)
    (hb : tetrahedralLattice.Adj b bcap) (flag : Bool)
    (hflag : flag = (FarField.colour a == FarField.colour b)) :
    FarField.CapParity acap bcap (p.longLinkerLength w flag) := by
  apply longLinkerLength_capParity p w acap bcap flag
  rw [adjacent_caps_colours a b acap bcap ha hb]
  exact hflag

end ProteinFolding.Tetrahedral.ReductionTM2
