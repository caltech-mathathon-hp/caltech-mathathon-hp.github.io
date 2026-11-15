# HP folding is NP-complete

A website on why folding a string of H's and P's into the 3D grid with as many H–H contacts as
possible is NP-complete, made for Problem 07 of the Caltech × SAIR Mathathon 2026. It has a folding
game and a bin-packing game, Berger and Leighton's 1998 proof as a board of cards, related work,
and the Lean formalisation.

**Site:** <https://caltech-mathathon-hp.github.io/>

```bash
npm ci
npm run dev        # http://localhost:4321/
npm run build      # the static site, in dist/
```

## Changing the site

This repository is the site's source, so edit the files here. No other repository is copied over
it, and none is needed to build or change the site.

We all work on `main`, with no other branches and no pull requests. Every push to `main` rebuilds
and publishes the site with GitHub Pages (`.github/workflows/pages.yml`). If the build fails, the
deploy stops and the site already online stays up.

```bash
git pull --rebase            # get everyone's latest work first
# edit, then check that the site still builds:
npm run build
git add <files> && git commit -m "…"
git pull --rebase && git push
```

If `git pull --rebase` stops on a conflict, someone changed the same lines. Keep both changes
where they make sense, then `git add` the file and `git rebase --continue`.

Older commits on `main` are named "Update from front-page at …". They come from an earlier setup
in which the site was copied here from another repository. That setup is gone: there is no
`front-page` branch here, and nothing is copied any more.

Everything in this repository is public, including pages with `status: hidden`.

A repository named `<owner>.github.io` is served at the root, so the workflow sets `SITE_BASE=/`.

`lean/` holds the team's Lean certificates
for Berger and Leighton's theorem; see `lean/README.md`. Its own workflow,
`.github/workflows/lean-certificates.yml`, builds it.

## Layout

```
astro.config.mjs          math (remark-math + KaTeX), Preact, YAML imports, base path
src/
  content/sections/       ONE MDX FILE PER SECTION  ← the content of the site
  content.config.ts       the frontmatter schema of a section
  content/home.mdx        the front page text (game, problem, idea of the proof, our question)
  pages/index.astro       front page: renders content/home.mdx, then one card per section
  pages/[slug].astro      renders every section at /<slug>/
  layouts/BaseLayout.astro  header, navigation, footer
  components/             prose components usable in any MDX file (see below)
  widgets/<name>/         interactive widgets, one self-contained folder each
  data/                   content data: papers, proof maps, site strings
  styles/tokens.css       EVERY colour, font, size: retune the look here
  styles/global.css       element styles and the page grid
  lib/                    small helpers (withBase, listedSections)
scripts/                  generators (e.g. papers.json from the literature notes)
public/                   static files served as is
lean/                     the Lean certificates, a Lean 4 project (see lean/README.md)
explainer-video/          source of the explainer video, not part of the site (npm run stepper inside)
```

## Adding, hiding or removing a section

Sections are the files in `src/content/sections/`. The navigation, the home-page cards and the
previous/next links are generated from them, sorted by `order`.

```yaml
---
title: The original proof      # h1
slug: original-proof           # URL /original-proof/
navTitle: Original proof       # optional, label in the nav bar
kicker: Part I                 # optional, small line above the title
lede: One or two sentences.    # optional, under the title
summary: One sentence for the home-page card.
order: 3
status: ready                  # ready | draft (banner) | soon (placeholder) | hidden (not built)
---
```

## Writing content (MDX)

All reader-facing text follows the project's writing guide, the `unslop` skill in the team's
workspace: short declarative sentences, concrete facts instead of adjectives, no filler.

Markdown plus LaTeX (`$…$`, `$$…$$`, rendered at build time). These components are available
in every section **without importing them**:

| component | use |
|---|---|
| `<Seq s="PHHP(PHP)^k" />` | an HP string, coloured; `^k` becomes a superscript |
| `<Status kind="proved" />` | claim label: proved, computed, cited, conjecture, draft, lean, open |
| `<Theorem kind="Lemma" number="3.12" name="…" source="BL p. 38" status="cited">…</Theorem>` | a formal statement |
| `<Callout kind="hard" title="…">…</Callout>` | boxed remark: note, idea, hard, warning |
| `<Aside>…</Aside>` | margin note (inline on small screens) |
| `<Figure caption="…" size="wide">…</Figure>` | figure; size prose, wide or full |
| `<Cite k="berger1998protein" at="Lemma 3.12" />` | citation linking to the paper on the Context page |
| `<Placeholder title="…">…</Placeholder>` | visible stand-in for something not built yet |

Blocks are laid out in a reading column. A top-level element with class `wide` or `full`
breaks out of it (`<div class="wide">…</div>`); `Figure` does this with `size`.

Links between sections: use relative links (`[the playground](../playground/)`), so they keep
working when the site is served from a sub-path. In code, use `withBase('/x/')`.

## Widgets

Each widget lives in `src/widgets/<name>/` and owns everything it needs (code, styles, its own
data loader). A widget is a Preact component used as an Astro island; a section imports it
explicitly and hydrates it when it scrolls into view:

```mdx
import FoldGame from '../../widgets/fold-game/FoldGame.tsx';

<div class="wide"><FoldGame client:visible lattice="square" sequence="HPHPPHHPHPPHPHHPPHPH" /></div>
```

Rules that keep widgets interchangeable and the style consistent:

- **Colours and fonts only from `tokens.css`** (`var(--h)`, `var(--p)`, `var(--bond)`, `var(--accent)`,
  `var(--font-sans)`, …). Canvas or WebGL code reads them with `getComputedStyle` and re-reads them
  on the `themechange` event fired on `<html>`. The site is light by default; dark mode applies
  only when the reader picks it with the header toggle (`data-theme="dark"` on `<html>`).
- **Styles are scoped by a class prefix** per widget (`fg-` fold game, `pb-` proof board, `pmf-` proof
  figures, `pp-` papers) in a CSS file next to the component. Shared button styles: `.btn`, `.btn.primary`, `.btn.ghost`.
- **Data in files, not in code**: proof steps in `src/content/proof-steps/<map>/*.mdx`, papers in
  `src/data/papers/papers.json`, game levels in the widget's `levels/`.
- **Works without a mouse** (keyboard focus, labels) and at phone width.

| widget | folder | data |
|---|---|---|
| Folding game (2D square, 3D cubic; pluggable lattices) | `widgets/fold-game/` | `widgets/fold-game/levels/` |
| Proof board: picture cards, each opening its step in a popup | `widgets/proof-map/` (`ProofBoard.astro`) | `content/proof-steps/<map>/*.mdx`: frontmatter is the card, the body is the popup, split at `###` headings; figures registered in `widgets/proof-map/figures/index.ts` |
| Fold it yourself: fold $S_B$ of a small instance into a 12×12×12 cube by hand (original-proof page) | `widgets/fold-it-yourself/` (`FoldItYourself.astro`, `game.client.js`) | the eight levels at the top of `game.client.js` |
| Papers map | `widgets/papers/` | `data/papers/papers.json`, generated by `npm run papers` from `data/papers/curation.toml` and the team's literature notes, which are not in this repository. Without the notes, edit `curation.toml`, leave `papers.json` alone and say in the pull request that it needs regenerating |

## Colour language

The HP model has fixed colours everywhere: **H** = `--h` (burnt orange, filled disc),
**P** = `--p` (slate blue, hollow circle), a scoring H–H contact = `--bond` (amber, dashed),
the chain = `--backbone`. Difficulty on the proof board: `--diff-1` routine, `--diff-2` needs care,
`--diff-3` where the proof is hard. The items of the running example in the proof figures:
`--item-1` … `--item-4`, padding `--item-pad`.

## Working on it in parallel

Several dev servers can run side by side if each gets its own port and Vite cache:

```bash
VITE_CACHE_DIR=node_modules/.vite-game npx astro dev --port 4401 --ignore-lock
```

They still share Astro's content store (`.astro/data-store.json`) and sometimes corrupt it: an
error overlay about renaming `data-store.json.tmp`, or every page 404 with "collection sections
does not exist". Restarting the dev server fixes it.
