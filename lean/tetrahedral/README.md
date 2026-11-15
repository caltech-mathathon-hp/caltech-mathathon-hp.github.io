# Tetrahedral HP folding: Lean certificates

Lean **4.24.0** / mathlib **v4.24.0** proof of NP-completeness for a single HP
chain on the fixed infinite diamond lattice.

The unconditional theorem is
[`ProteinFolding.Tetrahedral.tetrahedral_hp_npComplete`](ProteinFolding/Tetrahedral/NPCompleteness.lean#L22):

```lean
theorem tetrahedral_hp_npComplete : HPStringFoldNPComplete
```

It has no Cook–Levin, geometric, routing, or machine-computability premise.
`HPStringFoldNPComplete` is the unchanged
[problem statement](ProteinFolding/Tetrahedral/MainTheorem.lean).
The checked final axiom reports contain only `propext`, `Classical.choice` and
`Quot.sound`.

## Build and verify

Install Lean through elan and Python 3, then run inside **`lean/tetrahedral/`**:

```sh
lake exe cache get
lake build
python3 checks/verify.py
```

Keep `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` pinned. The
manifest fixes mathlib to commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`;
`lake update` is not part of reproduction. Compiler arguments select one Lean
worker thread and a 64 MiB worker stack per module. The package entry point
imports the theorem, its exact-type audit, and the complete tetrahedral
declaration audit.

The source package contains no compiler binaries or build caches. The
[workspace proof records](checks/workspace-proof/README.md) document the
successful original kernel checks and their cache provenance. They do not
claim that a fresh Linux build or GitHub Actions run has occurred. A build and
verification result for a published commit belongs to that commit's CI run.

A [GitHub Actions template](checks/tetrahedral-lean.yml.example) is included.
To enable it, a maintainer with workflow permission can copy it to
`.github/workflows/tetrahedral-lean.yml` at the repository root. The template
alone does not run a CI job.

## Model and proof

[Statement.lean](ProteinFolding/Tetrahedral/Statement.lean) fixes the lattice:
A-sites have even coordinates and coordinate sum divisible by four; B-sites
have odd coordinates and sum congruent to three modulo four. The four
A-to-B bond vectors are `(1,1,1)`, `(1,-1,-1)`, `(-1,1,-1)` and `(-1,-1,1)`.
The graph includes the reverse bonds.

An input is a finite H/P word and a signed bond threshold. All residues occupy
distinct sites. Every H–H lattice bond contributes, including backbone bonds.
There are no input obstacles, pinned sites, scaffolds, or bounding boxes.
The model is the diamond lattice, distinct from the FCC lattice and the
sibling cubic-lattice problem.

The proof uses the project's finite-machine definition of NP and an actual
polynomial-time TM2 reduction from unary exact-capacity packing. The source
hardness proof uses the proved universal Cook–Levin construction in
`Common/CookLevinProofUniversal.lean`. The closed reduction computes its bulk
records, endpoint colours, linker flags and signed threshold internally.

| Step | Main checked sources |
| --- | --- |
| Fixed model, encoding and target | `Tetrahedral/Statement`, `Encodings`, `MainTheorem` |
| Sharp contact bound and equality classification | `SharpBound`, `SiteRigidity*`, `FoldRigidity` |
| Actual bulk graph and component cover | `BulkAcyclicity`, `BulkCanonicalCover`, `ReductionTM2BulkRuntime*` |
| Source-ordered local words and selected columns | `NearFieldCanonicalCappedUnits`, `CanonicalUnits`, `CanonicalPairwise`, `CanonicalSelectedWireClearance` |
| Computed parity and complete forward fold | `NearFieldCanonicalRoutingParity`, `CanonicalMixedFamily`, `CanonicalCompleteness` |
| Actual reduction soundness and equivalence | `ReductionTM2CanonicalBackward`, `NPCompleteness` |
| Polynomial computation, source hardness and NP membership | `ReductionTM2Canonical`, `PackingSource`, `CertificatesTM2Correctness`, `ReductionNPComposition` |

The integer isoperimetric corollary used by this proof is formalised. The
manuscript's more general real-valued inequality is not formalised here and
is not needed for that corollary or the final theorem.

## Distribution

The [source manifest](checks/source-manifest.json) lists every module, direct
import and SHA256. It includes 921 tetrahedral modules, their complete shared
closure of 154 Common, 48 Cubic and 11 Square modules, and one generated package
entry point. The 1,134 copied proof modules are byte-for-byte unchanged from
the verified workspace. The eleven Square modules supply reusable machine
infrastructure; their presence does not assert square-lattice NP-hardness.

`FinalAudit.lean` checks the exact theorem type and prints axioms for the final
theorem, reduction equivalence and actual bulk acyclicity. `Audit.lean` contains
the broader tetrahedral declaration audit. The frozen statement, encoding,
complexity and exact-type audit hashes are recorded in the source manifest.
Sibling Lean packages retain their own statements and proof boundaries.

This export contains sources, pinned configuration, documentation, verification
infrastructure and selected proof records. It excludes local caches, compiled
artifacts, research drafts, PDFs and personal settings. No new source-code
license is assigned by this export; upstream dependency licenses remain with
their sources.
