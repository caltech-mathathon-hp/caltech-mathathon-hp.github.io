# Repository guide

This repository holds the website (an Astro project at the root) and the team's Lean project in
`lean/cubic/`. The team works on `main` only; the website's rules are in `CLAUDE.md` and
`README.md`.

For the Lean certificates, start with `lean/cubic/README.md` and follow `lean/cubic/AGENTS.md`.
Run Lake inside `lean/cubic/`. The final cubic complexity theorems have an explicit Cook–Levin
premise; inspect the theorem types as well as their axiom reports.
`lean/cubic/checks/source-manifest.json` is the complete project-local module/import index.

The website uses the root `package.json`, and every push to `main` publishes it. After changing
`lean/cubic`, run `python3 scripts/build_lean.py` so the Lean page shows the new version. Never
commit compiler or download caches.
