// @ts-check
import { defineConfig } from 'astro/config';
import mdx from '@astrojs/mdx';
import preact from '@astrojs/preact';
import { unified } from '@astrojs/markdown-remark';
import remarkMath from 'remark-math';
import rehypeKatex from 'rehype-katex';
import yaml from '@modyfi/vite-plugin-yaml';

// Deployment: SITE_URL=https://<owner>.github.io, and SITE_BASE=/ for a repository named
// <owner>.github.io or /<repo>/ for any other (the website repository's workflow sets both;
// see README, Deploying).
// Locally both default to the root, so `npm run dev` serves at http://localhost:4321/.
const site = process.env.SITE_URL ?? 'http://localhost:4321';
const base = process.env.SITE_BASE ?? '/';

export default defineConfig({
  site,
  base,
  trailingSlash: 'always',
  build: { format: 'directory' },
  markdown: {
    // LaTeX in Markdown/MDX: $inline$ and $$display$$, rendered to HTML at build time.
    processor: unified({
      remarkPlugins: [remarkMath],
      rehypePlugins: [[rehypeKatex, { strict: false }]],
    }),
  },
  integrations: [mdx(), preact()],
  vite: {
    plugins: [yaml()],
    // Lets several dev servers run side by side without sharing a dependency cache.
    cacheDir: process.env.VITE_CACHE_DIR ?? 'node_modules/.vite',
  },
});
