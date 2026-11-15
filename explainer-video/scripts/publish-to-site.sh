#!/usr/bin/env bash
# Rebuild the step-through page and copy it to the website's public/explainer/, where the
# ExplainerVideo widget (src/widgets/explainer/) shows it in an iframe.
# Run from anywhere: bash explainer-video/scripts/publish-to-site.sh
set -euo pipefail

here="$(cd "$(dirname "$0")/.." && pwd)"
site="$(cd "$here/.." && pwd)"

cd "$here"
npm ci
npm run stepper:build

mkdir -p "$site/public/explainer"
rsync -a --delete "$here/out/stepper/" "$site/public/explainer/"
du -sh "$site/public/explainer"
