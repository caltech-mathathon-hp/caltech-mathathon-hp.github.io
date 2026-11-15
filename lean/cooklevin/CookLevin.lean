import ProteinFolding.Common.CookLevinProofUniversal
import ProteinFolding.Common.CookLevinProofUniversalWidthThree

/-!
# Cook–Levin in Lean 4

Entry point for this package. The two headline results are:

* `ProteinFolding.SAT.CookLevinUniversal.cookLevin : ProteinFolding.SAT.CookLevin`
  — CNF-SAT (binary variable indices) is NP-hard: every language in NP
  Karp-reduces to it by a polynomial-time Turing machine (mathlib `FinTM2`).
* `ProteinFolding.SAT.CookLevinUniversalWidthThree.npHard`
  — the same for CNF formulas with clause width at most three (3-SAT).
-/
