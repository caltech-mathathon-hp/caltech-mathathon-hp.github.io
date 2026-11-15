import ProteinFolding.Common.Complexity
import ProteinFolding.Tetrahedral.Encodings

/-!
# Tetrahedral HP NP-completeness: statement only

The main theorem claimed in Section 1 of `HP_tetrahedral_proof (2).md`.
As in the existing cubic and square `MainTheorem` modules, this file records
a Prop-valued proof target. It supplies no proof or axiom of the claim.

`ProteinFolding.NPComplete` means membership in NP together with universal
polynomial-time many-one hardness, using the shared mathlib TM2 framework.
Neither membership, hardness, the reduction, nor its geometric ingredients
are proved or assumed in this file.
-/

namespace ProteinFolding.Tetrahedral

/-- The target theorem: single-chain HP folding on the fixed infinite diamond
lattice, with all H-H bonds counted, is NP-complete under the stated encoding. -/
def HPStringFoldNPComplete : Prop :=
  NPComplete hpEncoding (fun I : HPInstance => I.Accepts)

end ProteinFolding.Tetrahedral
