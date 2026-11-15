import ProteinFolding.Cubic.Proofs.VerifierGeometryComputable
import ProteinFolding.Cubic.Proofs.VerifierHPSemantics
import ProteinFolding.Cubic.Proofs.VerifierPerfect

/-! Unconditional NP membership for the two frozen cubic-lattice problems.
These theorems discharge the membership observation in footnote 1 of Berger
and Leighton (RECOMB 1998). They prove the membership parts of the main
NP-completeness targets; they do not establish NP-hardness.

All verifier stages are actual finite TM2 machines. Certificates are arbitrary
Boolean words with the identity encoding; malformed words are rejected. HP
certificates need at most four times the input encoding length. The perfect
verifier uses a unary side prefix and at most five times that length plus one.
The frozen instances themselves retain their original binary encodings. -/

namespace ProteinFolding

open Computability Turing

/-- The complete HP verifier, with no machine or complexity hypothesis. -/
noncomputable def hpVerifierComputable :
    TM2ComputableInPolyTime CubicHPVerifier.inputEncoding finEncodingBoolBool
      CubicHPVerifier.verify :=
  CubicHPVerifier.verifyComputable CubicVerifier.GeometryMachine.geometryComputable

/-- The complete perfect-cube verifier, with no machine or complexity hypothesis. -/
noncomputable def perfectVerifierComputable :
    TM2ComputableInPolyTime PerfectVerifierInputGuards.inputEncoding finEncodingBoolBool
      PerfectVerifier.verify :=
  PerfectVerifier.verifyComputable CubicVerifier.GeometryMachine.geometryComputable

/-- HP STRING-FOLD on the fixed cubic lattice belongs to NP (footnote 1).
The polynomial verifier is implemented and its soundness/completeness proved. -/
theorem hpStringFold_inNP : InNP hpEncoding (fun I : HPInstance => I.Accepts) :=
  CubicHPVerifier.hpStringFold_inNP_of_geometry CubicVerifier.GeometryMachine.geometryComputable

/-- PERFECT HP STRING-FOLD belongs to NP (footnote 1). Raw inputs with the
wrong H count are rejected, exactly as in the frozen problem definition. -/
theorem perfectHPStringFold_inNP :
    InNP perfectEncoding (fun I : PerfectInput => PerfectHPStringFold I.1 I.2) :=
  PerfectVerifier.perfect_inNP_of_geometry_computable CubicVerifier.GeometryMachine.geometryComputable

end ProteinFolding
