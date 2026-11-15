import { defineCollection } from 'astro:content';
import { glob } from 'astro/loaders';
import { z } from 'astro/zod';

/**
 * One MDX file per section of the site, in src/content/sections/.
 * Add a file to add a section; set `status: hidden` (or delete the file) to remove it.
 * Navigation, the home page cards and prev/next links are all generated from this list.
 */
const sections = defineCollection({
  loader: glob({ pattern: '*.mdx', base: './src/content/sections' }),
  schema: z.object({
    /** Page title (h1). */
    title: z.string(),
    /** URL segment: /<slug>/. Keep stable once published. */
    slug: z.string(),
    /** Short label for the navigation bar. Defaults to the title. */
    navTitle: z.string().optional(),
    /** Small line above the title, e.g. "Part I". */
    kicker: z.string().optional(),
    /** One or two sentences under the title. */
    lede: z.string().optional(),
    /** One sentence for the card on the home page. */
    summary: z.string(),
    /** Position in navigation and on the home page. */
    order: z.number(),
    /**
     * ready  – normal page
     * draft  – page shown with a "draft" banner
     * soon   – card and nav entry shown as "coming soon"; page shows a short placeholder
     * hidden – not built, not listed
     */
    status: z.enum(['ready', 'draft', 'soon', 'hidden']).default('ready'),
  }),
});

/**
 * The step cards of a proof board: one MDX file per card, in src/content/proof-steps/<map>/<step>.mdx
 * (e.g. bl/walls.mdx; the folder is the map, so our proof can live in ours/ later).
 * The frontmatter is the card; the MDX body is the popup that opens when the card is selected.
 * Rendered by src/widgets/proof-map/ProofBoard.astro.
 */
const proofSteps = defineCollection({
  loader: glob({ pattern: '**/*.mdx', base: './src/content/proof-steps' }),
  schema: z.object({
    /** Card title, at most four words. */
    title: z.string(),
    /** One sentence on the card. May contain $math$ and `HP strings` in backticks. */
    caption: z.string(),
    /** Where the card sits: the idea (one wide card on top), the setup row, one of the two
        directions, or the conclusion. */
    lane: z.enum(['top', 'setup', 'left', 'right', 'end']),
    /** Position within its lane (ascending). */
    order: z.number(),
    /** 1 routine (green), 2 needs care (orange), 3 hard (red). Our rating. */
    difficulty: z.union([z.literal(1), z.literal(2), z.literal(3)]),
    /** Picture on the card: a key of src/widgets/proof-map/figures/index.ts. */
    figure: z.string().optional(),
    /** Folds this card with its neighbours into one group on the board (a key of the ProofBoard
        `groups` prop). Cards of a group must be consecutive in their lane. */
    group: z.string().optional(),
    /** Where it is in the paper, e.g. "Lemma 3.12, pp. 37–38". */
    source: z.string().optional(),
  }),
});

export const collections = { sections, proofSteps };
