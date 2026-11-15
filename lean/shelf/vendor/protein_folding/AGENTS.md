# Cubic certificate navigation

Read README.md, docs/model.md, and docs/theorem-index.md first. The Lean package
root is this directory, not the website root. Main proofs are in
ProteinFolding/Cubic/Proofs/Main.lean; statements are in
ProteinFolding/Cubic/MainTheorem.lean. Import ProteinFolding for the distribution.

The main complexity proofs retain an explicit SAT.CookLevin parameter. Do not
report them as unconditional or confuse a Prop-valued definition with its proof.
The source manifest includes all project-local imports, including eleven Square
modules used as dependencies. Do not delete them based on their folder name.

For a requested review, inspect first and report in chat; do not edit or regenerate
files unless the user requests changes. Builds/checks create ignored artifacts.
For authorized development, keep the six frozen statement/encoding/complexity
files and all theorem meanings unchanged. Do not introduce sorry, admit, axiom,
opaque, native_decide, unsafe, extern, implemented_by, or csimp. Alternative proof
methods must prove the same statements. Do not upgrade pinned dependencies as a
routine repair. Do not copy unrelated workspaces, credentials or caches here.

Validation: lake build, then pwsh -NoProfile -File checks/Verify.ps1.
The manifest intentionally detects changed source; an authorized source update
must explicitly refresh its hashes/imports and preserve its frozen-file checks.
Report the exact theorem type, build status, audit output, and any remaining
hypotheses. Preserve this branch's lean/ directory when synchronizing site files;
do not change the website deployment or merge into main without authorization.
