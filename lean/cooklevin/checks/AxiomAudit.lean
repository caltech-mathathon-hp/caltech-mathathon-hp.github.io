import CookLevin

/-! Run with `lake env lean checks/AxiomAudit.lean`.
Expected: only `propext`, `Classical.choice`, `Quot.sound`. -/

#check @ProteinFolding.SAT.CookLevin
#print ProteinFolding.SAT.CookLevin
#print ProteinFolding.NPHard
#print ProteinFolding.InNP
#print ProteinFolding.KarpReduces
#print axioms ProteinFolding.SAT.CookLevinUniversal.cookLevin
#print axioms ProteinFolding.SAT.CookLevinUniversalWidthThree.npHard
