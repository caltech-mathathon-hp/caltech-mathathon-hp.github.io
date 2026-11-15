# Cook–Levin theorem in Lean 4

A standalone extract of the Cook–Levin formalisation from the Mathathon
HP protein-folding Lean project. It proves, with no extra hypotheses, that
CNF satisfiability is NP-hard. NP-hardness here is universal: every NP
language Karp-reduces to SAT through an actual polynomial-time mathlib
Turing machine (`Turing.FinTM2`).

- Lean `v4.24.0`, mathlib `v4.24.0` (versions locked in `lake-manifest.json`)
- 130 project modules, all under `ProteinFolding/Common/`. Their only
  external dependency is mathlib.
- Axioms used: only `propext`, `Classical.choice`, `Quot.sound`.

## Main results

| Statement | Declaration | File |
| --- | --- | --- |
| CNF-SAT is NP-hard | `ProteinFolding.SAT.CookLevinUniversal.cookLevin : ProteinFolding.SAT.CookLevin` | `ProteinFolding/Common/CookLevinProofUniversal.lean` |
| Every NP language Karp-reduces to CNF-SAT | `ProteinFolding.SAT.CookLevinUniversal.inNP_karp` | same |
| CNF-SAT restricted to clause width ≤ 3 is NP-hard | `ProteinFolding.SAT.CookLevinUniversalWidthThree.npHard` | `ProteinFolding/Common/CookLevinProofUniversalWidthThree.lean` |

## Definitions to check

These definitions fix what the theorem means. Read them first.

- `ProteinFolding/Common/CookLevin.lean`: literals, clauses, `CNF`,
  `Satisfiable`, the five-symbol encoding `cnfEncoding` (binary variable
  indices), and `def CookLevin : Prop := NPHard cnfEncoding Satisfiable`.
- `ProteinFolding/Common/Complexity.lean`: `InNP` (a polynomially bounded
  certificate checked by a polynomial-time `FinTM2` decider), `KarpReduces`
  (a reduction computed by a `TM2ComputableInPolyTime` machine), `NPHard`
  (every `InNP` language Karp-reduces) and `NPComplete`.

## Proof outline

The proof is a tableau construction. Most of it builds Turing machines that
output the formula, with proofs of what they compute and how fast.

1. **Verifier normal form** (`CookLevinProofVerifierBridge`): turns an NP
   verifier into a bounded run of a single `FinTM2` on the certificate.
2. **Tableau semantics** (`Cells`, `Rows`, `Window`, `Locality`, `Padded`,
   `Runs`, `Tableau`): bounded padded runs are described by local cell and
   window rules.
3. **Formula** (`GlobalCNF`, `StepCNF`, `CertificateCNF`, `NPFormula`): a
   concrete CNF that is satisfiable exactly when an accepting bounded
   certificate exists. Polynomial bounds on its size are proved in `*Size`.
4. **Emitter** (`*Compiler` modules and the `TM2*` library): real polynomial-time
   TM2 machines that output this CNF in `cnfEncoding`. Each output is proved
   equal to the semantic formula up to a bijective renaming of variables
   (`VerifierCompiler`, `VerifierCompilerBounds`).
5. **Width three** (`WidthThree*`): a polynomial-time post-processor that
   converts the formula to clause width at most three and preserves
   satisfiability.

## Build and check

```bash
lake exe cache get
```

```bash
lake build
```

```bash
lake env lean checks/AxiomAudit.lean
```

`lake exe cache get` downloads mathlib's prebuilt files. Without it, mathlib
compiles from source, which takes hours. `checks/` also has three small
regression files for the boundary, lookup and source-query compilers. Run
each one with `lake env lean <file>`.

The module names still use the original `ProteinFolding.` prefix. That keeps
the files byte-identical to the source project.
