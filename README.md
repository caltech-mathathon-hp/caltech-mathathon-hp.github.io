# HP folding is NP-complete

A website on why folding a string of H's and P's into the 3D grid with as many H–H contacts as
possible is NP-complete, made for Problem 07 of the Caltech × SAIR Mathathon 2026. It has a folding
game and a bin-packing game, Berger and Leighton's 1998 proof as a board of cards, related work,
and the plan for a proof in Lean.

**Site:** <https://mathathon-caltech-hp.github.io/>

## Lean certificates (3D cubic lattice)

The [`lean-certificates` branch](https://github.com/mathathon-caltech-hp/mathathon-caltech-hp.github.io/tree/lean-certificates/lean/cubic)
contains the [Lean 4.24.0 project](lean/cubic/README.md),
[theorem index](lean/cubic/docs/theorem-index.md), full project-local proof
dependencies, pinned mathlib configuration, and build/axiom-check CI.
The final cubic NP-completeness results retain an explicit Cook–Levin premise.
Start with [lean/README.md](lean/README.md); the website and Lean package have
separate build commands. This branch does not deploy the live website.

## Run it locally

```bash
npm ci
npm run dev      # http://localhost:4321/
npm run build    # the static site, in dist/
```

The site is built with [Astro](https://astro.build), MDX and Preact. The text of each page is in
`src/content/`, the interactive widgets are in `src/widgets/`.

## How this repository is updated

The site is written in the team's main repository and copied here by a script there. Every
push to `main` rebuilds the site with GitHub Pages (`.github/workflows/pages.yml`). Files changed
directly in this repository, other than this README, the workflow and `.gitignore`, are replaced by
the next copy.

The Lean distribution is maintained separately on `lean-certificates`. Preserve
`lean/`, `.gitattributes`, and `.github/workflows/lean-certificates.yml` if site
changes are synchronized to this branch; the website copy process is not a
source of Lean certificates.
