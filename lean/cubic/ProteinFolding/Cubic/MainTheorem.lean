import ProteinFolding.Common.Complexity
import ProteinFolding.Cubic.Encodings

/-!
# Main statements of Berger--Leighton (1998)

DOI: 10.1145/279069.279080. These are Prop-valued DEFINITIONS of the claims,
not proofs. No NP membership, hardness, geometric inequality, or reduction
from bin packing is established here.
-/

namespace ProteinFolding

/-- The paper's main result, announced in Section 2 (p. 31) and Section 3:
HP STRING-FOLD on the fixed cubic lattice Z³ is NP-complete. -/
def HPStringFoldNPComplete : Prop :=
  NPComplete hpEncoding (fun I : HPInstance => I.Accepts)

/-- The main hardness step, Section 2 and Section 3.2 (pp. 31-32):
PERFECT HP STRING-FOLD is NP-hard. Raw inputs with the wrong H count are rejected. -/
def PerfectHPStringFoldNPHard : Prop :=
  NPHard perfectEncoding (fun I : PerfectInput => PerfectHPStringFold I.1 I.2)

/-- Section 3.2's NP-completeness claim for PERFECT HP STRING-FOLD.
Footnote 1 (p. 31) distinguishes hardness from the additional NP-membership step.
The raw-input formulation uses the same perfect-packing predicate as Section 2. -/
def PerfectHPStringFoldNPComplete : Prop :=
  NPComplete perfectEncoding (fun I : PerfectInput => PerfectHPStringFold I.1 I.2)

end ProteinFolding
