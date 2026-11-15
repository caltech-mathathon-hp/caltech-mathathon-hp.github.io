# Lean certificates

The [3D cubic project](cubic/README.md) formalises Berger and Leighton's HP
folding problem and proves its NP-completeness **with an explicit Cook–Levin
premise**. Start with its README, [theorem index](cubic/docs/theorem-index.md),
and [verification instructions](cubic/docs/verification.md).

This branch contains Lean source certificates and all project-local dependencies.
The compiler and mathlib are downloaded using the pinned Lake configuration;
they are not checked into Git. The website remains a separate project at the
repository root. The live site is deployed from `main`, not this branch.
