import ProteinFolding.Cubic.Proofs.VerifierHPSemantics
import ProteinFolding.Cubic.Proofs.VerifierPerfect

/-! Small executable boundary checks for the complete Boolean verifiers.
These check source labels, bond thresholds, self avoidance, malformed record
bits, and the perfect verifier's explicit side frame and H-count guard. They
use the pure verifier functions and require no geometric machine assumption.
-/

namespace ProteinFolding.CubicVerifierChecks

open CubicVerifier CubicCertificates

-- Consecutive H residues contribute a bond, as required by the frozen score.
example : CubicHPVerifier.verify
    ((⟨[.H, .H], 1⟩ : HPInstance), encodeRecords [(.H, 0), (.H, 0)]) = true := by
  decide

example : CubicHPVerifier.verify
    ((⟨[.H, .H], 2⟩ : HPInstance), encodeRecords [(.H, 0), (.H, 0)]) = false := by
  decide

-- The second step returns to the first vertex and must be rejected.
example : CubicHPVerifier.verify
    ((⟨[.H, .P, .H], 0⟩ : HPInstance),
      encodeRecords [(.H, 0), (.P, 0), (.H, 1)]) = false := by
  decide

-- Both a complete invalid direction code (111) and a partial record retain
-- a parser error. Empty source labels ensure geometry itself rejects them.
example :
    CubicHPVerifier.verify ((⟨[], -1⟩ : HPInstance), [true, true, true, true]) = false ∧
    CubicHPVerifier.verify ((⟨[], -1⟩ : HPInstance), [true]) = false := by
  decide

example : CubicHPVerifier.verify ((⟨[], -1⟩ : HPInstance), []) = true := by
  decide

example : PerfectVerifier.verify
    (([.H], 1), frameUnarySide 1 (encodeRecords [(.H, 0)])) = true := by
  decide

-- Side zero permits an arbitrary self-avoiding all-P sequence.
example : PerfectVerifier.verify
    (([.P, .P], 0), frameUnarySide 0 (encodeRecords [(.P, 0), (.P, 0)])) = true := by
  decide

example : PerfectVerifier.verify
    (([.P], 1), frameUnarySide 1 (encodeRecords [(.P, 0)])) = false := by
  decide

-- The geometry and H count fit side one, but the source input requests two.
example : PerfectVerifier.verify
    (([.H], 2), frameUnarySide 1 (encodeRecords [(.H, 0)])) = false := by
  decide

end ProteinFolding.CubicVerifierChecks
