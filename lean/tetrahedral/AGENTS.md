# Tetrahedral certificate navigation

Read this package's README.md and checks/workspace-proof/README.md. Run Lake
from this directory, not the website root. Follow the repository README.md and
CLAUDE.md for publication: the team works on main, with no branches or pull
requests, and checks the website build before pushing.

The final declaration is
`ProteinFolding.Tetrahedral.tetrahedral_hp_npComplete : HPStringFoldNPComplete`
in ProteinFolding/Tetrahedral/NPCompleteness.lean. It is unconditional. Inspect
the theorem type and final axiom reports together. The sibling cubic package
has its own stated Cook–Levin premise; do not change its proof boundary.

ProteinFolding.lean imports NPCompleteness, FinalAudit and the complete
tetrahedral Audit. The source manifest records all copied proof files and
their complete project-local import closure, including Common, Cubic and
eleven Square dependencies. Do not drop a dependency because of its folder.

Preserve the copied Lean sources byte-for-byte and keep the frozen hashes and
theorem meanings unchanged. Source changes require explicit authorization and
a fresh build, audit and manifest. Do not introduce sorry, admit, custom axioms,
native_decide, unsafe execution, or a weakened final target. Keep the pinned
Lean and mathlib revisions. Never commit build artifacts, compiler/download
caches, credentials, personal settings, or unrelated workspaces.

Validation is lake build, then python3 checks/verify.py. A source-integrity
check alone is not a fresh kernel build. Historical workspace reports live in
checks/workspace-proof; current CI results must be attributed to their actual
commit/run. Do not edit the sibling cubic, cooklevin or shelf packages as part
of tetrahedral package maintenance.
