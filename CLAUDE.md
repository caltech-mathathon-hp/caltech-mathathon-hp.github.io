# Instructions for agents

This repository is the source of the website <https://caltech-mathathon-hp.github.io/>. Read
`README.md` first: it has the layout, the components and the rules for widgets.

- Edit the files here. No other repository is copied over this one, and none is needed to build or
  change the site.
- Commits named "Update from front-page at …" come from an earlier setup that copied the site in
  from another repository. There is no `front-page` branch to look for.
- The team works on `main` only: no other branches, no pull requests. Every push to `main`
  publishes the site. Before you push: `git pull --rebase`, `npm run build`, then
  `git pull --rebase && git push`.
- Everything here is public, including pages with `status: hidden`.
- `src/data/papers/papers.json` is generated; don't edit it by hand (see the papers map in
  `README.md`).
