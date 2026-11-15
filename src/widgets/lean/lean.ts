/**
 * The Lean page's data. Everything the page shows from a Lean project comes from a
 * src/data/lean/certificate*.json file, which scripts/build_lean.py writes from the project
 * (lean/cubic in this repository: certificate.json). Each file is one certificate, named by its
 * `id`; the widgets take `cert="<id>"` and default to "cubic". The page never reads the Lean
 * files themselves.
 */
export type Status = 'definition' | 'proved' | 'conditional' | 'premise';

export interface Decl {
  full: string;
  kw: string;
  file: string;
  line: number;
  /** Its line on GitHub; null when the project has no public address. */
  href: string | null;
  code: string;
}

export interface IndexRow {
  concept: string;
  names: string[];
  status: Status;
  sources: { label: string; href: string | null }[];
  note: string;
}

export interface RouteStep {
  problem: string;
  /** The declaration that reduces the previous problem to this one. */
  via: string | null;
  /** The link is a hypothesis of the main theorems, not proved. */
  assumed: boolean;
  /** The declaration proving that the problem is in NP. */
  np: string | null;
}

export interface Certificate {
  id?: string;
  source: { ref: string; path: string; commit: string | null; date: string | null };
  project: {
    lean: string;
    mathlib: string;
    files: number;
    lines: number;
    declarations: number;
    theorems: number;
    sorries: number;
    axioms: number;
    nativeDecide: number;
    /** The project's check files: the one that prints the main results, the full audit. */
    checks?: { audit: string; verify: string | null };
    /** Folders left out of the counts above (a copied library). */
    excluded?: { paths: string[]; files: number; lines: number; theorems: number };
  };
  /** Empty when the project has no public address. */
  links: Partial<{
    repo: string;
    tree: string;
    clone: string;
    branch: string;
    ci: string;
    docs: Record<'readme' | 'theoremIndex' | 'model' | 'proofRoute' | 'verification' | 'audit', string>;
  }>;
  download: { path: string; bytes: number; sha256: string; folder?: string };
  route?: RouteStep[];
  index: IndexRow[];
  decls: Record<string, Decl>;
  axiomReport: { name: string; type: string; axioms: string[] }[];
}

const files = import.meta.glob('../../data/lean/certificate*.json', { eager: true, import: 'default' });

/** Every certificate, by id. */
export const certs: Record<string, Certificate> = Object.fromEntries(
  Object.values(files).map((c) => [(c as Certificate).id ?? 'cubic', c as Certificate]),
);

/** A certificate by id; fails the build if there is none. */
export function cert(id = 'cubic'): Certificate {
  const c = certs[id];
  if (!c) throw new Error(`Lean page: no certificate "${id}" in src/data/lean/certificate*.json.`);
  return c;
}

/** The team's certificate (lean/cubic). */
export const lean = cert('cubic');

/** A declaration by its name in the namespace (`Fold`, `SAT.CookLevin`); fails the build if missing. */
export function decl(name: string, id = 'cubic'): Decl {
  const d = cert(id).decls[name];
  if (!d)
    throw new Error(
      `Lean page: ${name} is not in the "${id}" certificate. Add it to [show] extra in its ` +
        'src/data/lean/certificate*.toml and run python3 scripts/build_lean.py.',
    );
  return d;
}

/** Names from a prop: "Fold hhBonds, bondCount" → ["Fold", "hhBonds", "bondCount"]. */
export const names = (s: string) => s.split(/[\s,]+/).filter(Boolean);

/** The last part of a Lean name: CubicPacking.packingToPerfect_karp → packingToPerfect_karp. */
export const short = (n: string) => n.slice(n.lastIndexOf('.') + 1);

export const statusLabel: Record<Status, string> = {
  definition: 'Definition',
  proved: 'Proved',
  conditional: 'Proved, assuming Cook–Levin',
  premise: 'Assumed',
};

/** A file under public/, with the site's base path. */
export const asset = (path: string) => `${import.meta.env.BASE_URL.replace(/\/$/, '')}/${path.replace(/^\//, '')}`;

export const num = (n: number) => n.toLocaleString('en-GB');

export const size = (bytes: number) =>
  bytes >= 1e6 ? `${(bytes / 1e6).toFixed(1)} MB` : `${Math.max(1, Math.round(bytes / 1e3))} kB`;

export const date = (iso: string) =>
  new Date(`${iso}T00:00:00Z`).toLocaleDateString('en-GB', {
    day: 'numeric',
    month: 'long',
    year: 'numeric',
    timeZone: 'UTC',
  });

/** The project's folder name inside the zip. */
export const zipFolder = (c: Certificate) => c.download.folder ?? c.download.path.split('/').pop()!.replace(/\.zip$/, '');
