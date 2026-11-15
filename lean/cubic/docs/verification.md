# Reproducing the checks

From `lean/cubic`, with elan and PowerShell 7 installed:

```sh
lake exe cache get
lake build
pwsh -NoProfile -File checks/Verify.ps1
```

The pinned toolchain and Lake manifest determine dependencies. Keep both;
`lake update` is not part of reproduction. The source manifest uses byte-exact
SHA256s, and `.gitattributes` preserves those bytes across Windows and Unix.

`Verify.ps1` checks that every distributed Lean source and the three build
configuration files match the manifest; that every project-local import has
its source; and that there are no unexpected or missing source files. It scans
Lean code with comments and strings removed for forbidden proof/execution
constructs. The scan is a supplementary safeguard, not a replacement for Lean.

The script then executes `checks/CubicHardness.lean`, requiring an axiom report
for every requested name, and generates and executes a fresh audit of the named
public declarations in **all shipped project modules**, including the eleven
Square dependencies. It rejects any axiom outside `propext`, `Classical.choice`,
and `Quot.sound`, including `sorryAx`. Anonymous instances, private declarations
and compiler-generated names are not independently enumerated by that parser;
their contributions to the exported results are covered transitively by the
main-theorem axiom reports. A missing declaration, import or failed Lean command
fails the check. Warnings alone are not a proof of failure or success.

Generated logs are ignored by Git: `checks/local-main-axioms.txt`,
`checks/local-source-axioms.txt`, and `checks/local-source-summary.json`.
The generated `checks/CubicSourceAudit.lean` records source hashes and audited
declarations. CI uploads these as its `cubic-verification` artifact, including
failure output when available. The workflow builds from the committed source;
the standard Lean action may reuse checked dependency/build caches.

To inspect the main certificate without the wrapper:

```sh
lake env lean checks/CubicHardness.lean
```

The expected final signatures retain `(hCL : ProteinFolding.SAT.CookLevin)`
on the three complexity results. Each of the four final results has axiom list
`[propext, Classical.choice, Quot.sound]`. `#print axioms` does **not** erase
explicit theorem parameters: the displayed type is needed to see Cook–Levin.

`checks/publication-validation.txt` records the local publication check and its
cache provenance. It is evidence for that snapshot, not a substitute for rerunning
the build. CI status belongs to the specific Git commit/run. The larger working
project's older audit counts are deliberately not presented as this export's
audit counts.

This repository's website deployment runs only on `main`. The separate
`Cubic Lean certificates` workflow builds the Lean package on this branch and
on pull requests affecting it; it does not deploy the website.
