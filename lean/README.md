# Lean certificates

The [3D cubic project](cubic/README.md) formalises Berger and Leighton's HP
folding problem and proves its NP-completeness **with an explicit Cook–Levin
premise**. Start with its README, [theorem index](cubic/docs/theorem-index.md),
and [verification instructions](cubic/docs/verification.md).

The [tetrahedral project](tetrahedral/README.md) proves NP-completeness for HP
folding on the fixed infinite diamond lattice, including backbone H–H bonds.
Its theorem `ProteinFolding.Tetrahedral.tetrahedral_hp_npComplete` has no
Cook–Levin hypothesis: the required Cook–Levin proof is included. The exact
statement, source manifest, verification commands and original audit records
are in that package. It does not change the cubic project's theorem signatures.

Each package contains its complete project-local proof dependencies. Run Lake
inside the package being checked. The pinned compiler and mathlib are downloaded;
compiler binaries and build caches are not checked into Git. The website remains
a separate project at the repository root and is deployed from `main`.
