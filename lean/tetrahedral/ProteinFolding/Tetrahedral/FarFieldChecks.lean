import ProteinFolding.Tetrahedral.FarFieldAvoidance
import ProteinFolding.Tetrahedral.FarFieldPrescribedLength

namespace ProteinFolding.Tetrahedral.FarField

example : paddingIncrease 2 false false 0 = 6 := by decide
example : paddingIncrease 2 true true 0 = 8 := by decide
example : paddingIncrease 2 false true 0 = 10 := by decide
example : paddingIncrease 2 true false 1 = 12 := by decide
example : paddingIncrease 3 true false 0 = 6 := by decide
example : paddingIncrease 3 false false 0 = 8 := by decide
example : paddingIncrease 3 true true 0 = 10 := by decide
example : paddingIncrease 3 false true 0 = 12 := by decide

-- The minimal even increase is realized in both possible start phases.
example : routeLength 2 50 false false 0 = (50 - 2 + 1) + 6 := by decide
example : routeLength 3 51 true false 0 = (51 - 3 + 1) + 6 := by decide

#print axioms avenue_adj
#print axioms crossing_zero
#print axioms crossing_one
#print axioms paddingFold
#print axioms exists_even_padding_path
#print axioms padding_for_prescribed_length
#print axioms paddingFold_approach_intersection

end ProteinFolding.Tetrahedral.FarField
