import ProteinFolding.Cubic.Proofs.CertificatesPerfect

/-! Kernel-checked examples for scoring, malformed words, overlaps and the
finite perfect-cube verifier. These examples assert no complexity result. -/

namespace ProteinFolding.CubicCertificates

open Residue

example : bitsVerifier (⟨[H, H], 1⟩, [false, false, false, false, false, false]) = true := by
  decide

example : bitsVerifier (⟨[H], 1⟩, [false, false, false]) = false := by decide

example : bitsVerifier (⟨[H], 0⟩, [false]) = false := by decide

-- East followed by west revisits the origin and is rejected.
example : bitsVerifier (⟨[H, H, H], 0⟩,
    [false, false, false, true, false, false, false, false, false]) = false := by decide

example : perfectBitsVerifier (([H], 1), [false, false, false]) = true := by decide

example : perfectBitsVerifier (([H], 2), [false, false, false]) = false := by decide

example : perfectBitsVerifier (([], 0), []) = true := by decide

end ProteinFolding.CubicCertificates
