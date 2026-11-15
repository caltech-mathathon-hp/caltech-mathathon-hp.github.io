import ProteinFolding.Tetrahedral.CertificatesTM2Verifier

/-! Kernel-reduced examples for the executable verifier and axiom reports for
the actual TM2 implementation. These are small regression checks; universal
machine execution and complexity are proved in the imported modules. -/

namespace ProteinFolding.Tetrahedral.CertificatesTM2Checks

open CertificatesTM2Verifier

local macro "check_verifier" : tactic =>
  `(tactic| (simp only [verify, records, CertificatesTM2Zip.zipRecords,
    CertificatesTM2Pairs.geometryValid, CertificatesTM2Pairs.bondCountRecords,
    CertificatesTM2Pairs.geometryRun, CertificatesTM2Row.rowRun]; decide))

example : verify (⟨[], 0⟩, []) = true := by check_verifier
example : verify (⟨[], 1⟩, []) = false := by check_verifier
example : verify (⟨[], -10⟩, []) = true := by check_verifier

-- Backbone H-H bonds are included in the frozen scoring convention.
example : verify (⟨[.H, .H], 1⟩, [0, 3]) = true := by check_verifier
example : verify (⟨[.H, .H], 2⟩, [0, 3]) = false := by check_verifier
example : verify (⟨[.H, .H], 1⟩, [0, 0]) = true := by check_verifier

-- Returning to the starting checkpoint is rejected.
example : verify (⟨[.H, .H, .H], -100⟩, [0, 0, 2]) = false := by check_verifier

-- The six-cycle includes the nonbackbone bond between its endpoints.
example : verify (⟨[.H, .H, .H, .H, .H, .H], 6⟩, [0, 1, 2, 0, 1, 3]) = true := by check_verifier
example : verify (⟨[.H, .H, .H, .H, .H, .H], 7⟩, [0, 1, 2, 0, 1, 3]) = false := by check_verifier
example : verify (⟨[.H, .P, .P, .P, .P, .H], 1⟩, [0, 1, 2, 0, 1, 3]) = true := by check_verifier
example : verify (⟨[.H, .P, .P, .P, .P, .H], 2⟩, [0, 1, 2, 0, 1, 3]) = false := by check_verifier

-- Length errors are explicit malformed records, even at negative thresholds.
example : verify (⟨[.H, .H], -100⟩, [0]) = false := by check_verifier
example : verify (⟨[.H, .H], -100⟩, [0, 1, 2]) = false := by check_verifier
example : verify (⟨[], -100⟩, [0]) = false := by check_verifier

#print axioms CertificatesTM2Row.row_run
#print axioms CertificatesTM2Records.suffix_counter_coordinate
#print axioms CertificatesTM2Pairs.GeometryMachine.outer_run
#print axioms CertificatesTM2Pairs.GeometryMachine.geometryComputable
#print axioms CertificatesTM2Zip.zipComputable
#print axioms verifyComputable

end ProteinFolding.Tetrahedral.CertificatesTM2Checks
