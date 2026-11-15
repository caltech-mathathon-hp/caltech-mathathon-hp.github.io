# Cubic HP folding: Lean certificates

Lean **4.24.0** / mathlib **v4.24.0** formalisation of Berger and Leighton,
*Protein Folding in the Hydrophobic-Hydrophilic (HP) Model is NP-Complete*,
RECOMB 1998, pp. 30–39, [DOI: 10.1145/279069.279080](https://doi.org/10.1145/279069.279080).

**Proof boundary:** the geometric equivalence and both NP memberships are proved
unconditionally. The final NP-hardness and NP-completeness theorems are proved
with the explicit argument `(hCL : SAT.CookLevin)`. This distribution does not
provide a proof of Cook–Levin or assert unconditional NP-completeness. `CookLevin`
is a proposition, not a global axiom. The reduction uses an alternative cubic
frame, preserving the original problem statements and encodings.

## Obtain and build

Install [elan](https://github.com/leanprover/elan), then:

```sh
git clone --branch lean-certificates --single-branch https://github.com/mathathon-caltech-hp/mathathon-caltech-hp.github.io.git
cd mathathon-caltech-hp.github.io/lean/cubic
lake exe cache get
lake build
lake env lean checks/CubicHardness.lean
```

Run these commands inside `lean/cubic`, not the website root. Keep
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pinned; no `lake update`
is needed. The source is small, but the Lean toolchain and mathlib cache can
consume several GB locally. A first build also checks the project proofs.

For the automated source-integrity, forbidden-token, and axiom checks, install
PowerShell 7 (available on Windows, macOS and Linux), then run:

```sh
pwsh -NoProfile -File checks/Verify.ps1
```

The [CI workflow](../../.github/workflows/lean-certificates.yml) builds this package
and runs the same checks. See [verification.md](docs/verification.md) for scope,
logs, and the distinction between a fresh build and a cached local check.

## Main declarations

All names below are in `namespace ProteinFolding`. The statement definitions
are in [Cubic/MainTheorem.lean](ProteinFolding/Cubic/MainTheorem.lean):

```lean
def HPStringFoldNPComplete : Prop :=
  NPComplete hpEncoding (fun I : HPInstance => I.Accepts)

def PerfectHPStringFoldNPHard : Prop :=
  NPHard perfectEncoding (fun I : PerfectInput => PerfectHPStringFold I.1 I.2)

def PerfectHPStringFoldNPComplete : Prop :=
  NPComplete perfectEncoding (fun I : PerfectInput => PerfectHPStringFold I.1 I.2)
```

The proved signatures in [Cubic/Proofs/Main.lean](ProteinFolding/Cubic/Proofs/Main.lean) are:

```lean
theorem perfectIffThreshold_holds : PerfectIffThreshold
theorem perfectHPStringFold_NPHard (hCL : SAT.CookLevin) : PerfectHPStringFoldNPHard
theorem perfectHPStringFold_NPComplete (hCL : SAT.CookLevin) : PerfectHPStringFoldNPComplete
theorem hpStringFold_NPComplete (hCL : SAT.CookLevin) : HPStringFoldNPComplete
```

Import `ProteinFolding` for the project, or
`ProteinFolding.Cubic.Proofs.Main` for just the main results. These are source
proofs that Lean checks, not a collection of assumed theorem declarations.

## Guide for readers and models

| Resource | Purpose |
| --- | --- |
| [Theorem index](docs/theorem-index.md) | Paper statements, exact declaration names, and source links |
| [Model and assumptions](docs/model.md) | Scoring, encodings, NP, universes, boundary conventions |
| [Proof route](docs/proof-route.md) | Alternative reduction and its relation to the paper |
| [Verification](docs/verification.md) | Reproduce kernel checks and inspect their limitations |
| [AGENTS.md](AGENTS.md) | Navigation and rules for automated contributors |
| [Source manifest](checks/source-manifest.json) | Every distributed module, SHA256, and direct imports |
| [Main axiom audit](checks/CubicHardness.lean) | Types and transitive axioms of the main results and reductions |

`ProteinFolding/Common` contains the model, encodings, complexity definitions,
SAT/packing sources and actual polynomial-time TM2 constructions.
`ProteinFolding/Cubic` contains the 3D geometry, verifiers and folding reduction.
Eleven modules under `ProteinFolding/Square` are retained because the cubic
machines import their reusable infrastructure. This is not a distribution of
the separate square-lattice hardness development. The manifest records the
complete project import closure, including those dependencies.

No source definitions or proof bodies were changed for this export. The package
entry point and verification infrastructure are tailored to the cubic case.
PDFs, unrelated research, local chat/configuration files, compiler binaries,
mathlib sources and build caches are not included. No new source-code license
is assigned by this export; dependency licenses remain with their upstreams.
