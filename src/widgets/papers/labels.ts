/** Wording and small helpers shared by the papers map (PapersMap.tsx) and the static list (PapersList.astro). */
import type { Paper, PapersData, ReadStatus, Relation, RelationKind } from '../../data/papers/types';

/**
 * How a relation A → B reads from either end.
 * out: on A's card ("A reduces from B"); in: on B's card ("B is the source problem for A").
 * soft: drawn dashed (context rather than a technical dependency).
 */
export const REL: Record<RelationKind, { out: string; in: string; soft?: boolean; alarm?: boolean }> = {
  'reduces-from': { out: 'reduces from', in: 'source problem for' },
  'builds-on': { out: 'uses', in: 'used by' },
  extends: { out: 'strengthens', in: 'strengthened by' },
  'variant-of': { out: 'variant of', in: 'variant studied in', soft: true },
  refutes: { out: 'refutes', in: 'refuted by', alarm: true },
  surveys: { out: 'surveys', in: 'surveyed in', soft: true },
  formalizes: { out: 'formalizes', in: 'formalized in' },
  answers: { out: 'answers', in: 'answered by' },
  discusses: { out: 'discusses', in: 'discussed in', soft: true },
};

/** How far we read a source, as a short phrase after "Our reading:". */
export const STATUS: Record<ReadStatus, string> = {
  read: 'full text',
  skim: 'skimmed',
  abstract: 'abstract and citing papers',
  todo: 'not read',
};

/** "Our reading: full text." plus the curated note, if any. */
export function statusLine(p: Paper): string {
  if (!p.status) return p.statusNote ?? '';
  return `Our reading: ${STATUS[p.status]}.${p.statusNote ? ` ${p.statusNote}` : ''}`;
}

/**
 * Relevance as a reading-list marker (the Annual Reviews convention):
 * •• central to our question, • relevant, nothing for background.
 */
export const RELEVANCE: Record<Paper['relevance'], { mark: string; label: string }> = {
  3: { mark: '••', label: 'Central to our question' },
  2: { mark: '•', label: 'Relevant to our question' },
  1: { mark: '', label: 'Background' },
};

/** "Berger and Leighton", "Crescenzi, Goldman, Papadimitriou, Piccolboni and Yannakakis". */
export function joinAuthors(a: string[]): string {
  if (a.length <= 1) return a[0] ?? '';
  return `${a.slice(0, -1).join(', ')} and ${a[a.length - 1]}`;
}

/** Up to three surnames in full, otherwise "First et al.": the byline of a list entry. */
export function bylineAuthors(a: string[]): string {
  return a.length <= 3 ? joinAuthors(a) : `${a[0]} et al.`;
}

export interface Link {
  other: string; // key of the other paper
  kind: RelationKind;
  dir: 'out' | 'in';
  note?: string;
}

/** Order of relation kinds on a card: technical dependencies first, context last. */
const KIND_ORDER: RelationKind[] = [
  'reduces-from',
  'builds-on',
  'extends',
  'answers',
  'refutes',
  'formalizes',
  'variant-of',
  'discusses',
  'surveys',
];

/** Outgoing and incoming relations of every paper: outgoing first, then by kind and year. */
export function buildLinks(data: PapersData): Map<string, Link[]> {
  const links = new Map<string, Link[]>();
  for (const p of data.papers) links.set(p.key, []);
  for (const p of data.papers) {
    for (const r of p.relations ?? ([] as Relation[])) {
      links.get(p.key)?.push({ other: r.to, kind: r.kind, dir: 'out', note: r.note });
      links.get(r.to)?.push({ other: p.key, kind: r.kind, dir: 'in', note: r.note });
    }
  }
  const year = new Map(data.papers.map((p) => [p.key, p.year]));
  for (const list of links.values()) {
    list.sort(
      (a, b) =>
        (a.dir === b.dir ? 0 : a.dir === 'out' ? -1 : 1) ||
        KIND_ORDER.indexOf(a.kind) - KIND_ORDER.indexOf(b.kind) ||
        (year.get(a.other) ?? 0) - (year.get(b.other) ?? 0) ||
        a.other.localeCompare(b.other),
    );
  }
  return links;
}

export function relLabel(l: Link): string {
  return l.dir === 'out' ? REL[l.kind].out : REL[l.kind].in;
}
