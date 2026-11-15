import ProteinFolding.Common.CookLevinProofBoundedVariableCompiler

open ProteinFolding.SAT Computability
open CookLevinSourceQueryCompiler CookLevinBoundedVariableCompiler

example : clauseCodeAt ([[], [⟨3, true⟩]], 0) = [] := by decide
example : clauseLengthAt ([[], [⟨3, true⟩, ⟨3, false⟩]], 1) = 2 := by
  exact clauseLengthAt_correct _ _ (by decide)
example : variableCodeAt (([[], [⟨1000000000, true⟩]], 1), 0) = encodeNat 1000000000 := by
  exact variableCodeAt_correct _ _ _ (by decide) (by decide)
example : positiveAt (([[⟨3, true⟩, ⟨3, false⟩]], 0), 1) = false := by
  exact positiveAt_correct _ _ _ (by decide) (by decide)
example : boundedVariable ((([[⟨3, true⟩]], 0), 0), 4) = 3 := by
  exact boundedVariable_correct _ _ _ _ (by decide) (by decide) (by decide)
example : boundedVariable ((([[⟨1000000000, true⟩]], 0), 0), 4) = 4 := by
  have hc := variableCodeAt_correct [[⟨1000000000, true⟩]] 0 0 (by decide) (by decide)
  simp [boundedVariable, ProteinFolding.TM2BoundedSearch.boundedSearch,
    ProteinFolding.TM2BoundedSearch.searchFrom, variableTest, hc, encodeNat_eq_iff]
