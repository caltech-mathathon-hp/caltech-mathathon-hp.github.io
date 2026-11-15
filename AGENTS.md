# Repository guide

This repository contains an Astro website and, on the `lean-certificates`
branch, a separate Lean package in `lean/cubic/`.

For Lean certificates, start with `lean/cubic/README.md` and follow
`lean/cubic/AGENTS.md`. Run Lake inside `lean/cubic/`. The final cubic complexity
theorems have an explicit Cook–Levin premise; inspect the theorem types as well
as their axiom reports. `lean/cubic/checks/source-manifest.json` is the complete
project-local module/import index for this distribution.

The website uses the root `package.json`. Its live deployment tracks `main`.
Keep website synchronization separate from certificate maintenance, preserving
`lean/` and its verification workflow. Never commit compiler/download caches.
