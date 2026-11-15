/**
 * The Lean page's data. Everything the page shows from the Lean project comes from
 * src/data/lean/certificate.json, which scripts/build_lean.py writes from lean/cubic on the
 * website repo's lean-certificates branch. The page never reads the Lean files themselves.
 */
import cert from '../../data/lean/certificate.json';

export type Status = 'definition' | 'proved' | 'conditional' | 'premise';

export interface Decl {
  full: string;
  kw: string;
  file: string;
  line: number;
  href: string;
  code: string;
}

export interface IndexRow {
  concept: string;
  names: string[];
  status: Status;
  sources: { label: string; href: string }[];
  note: string;
}

export interface Certificate {
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
  };
  links: {
    repo: string;
    tree: string;
    clone: string;
    branch: string;
    ci: string;
    docs: Record<'readme' | 'theoremIndex' | 'model' | 'proofRoute' | 'verification' | 'audit', string>;
  };
  download: { path: string; bytes: number; sha256: string };
  index: IndexRow[];
  decls: Record<string, Decl>;
  axiomReport: { name: string; type: string; axioms: string[] }[];
}

export const lean = cert as Certificate;

/** A declaration by its name in the namespace (`Fold`, `SAT.CookLevin`); fails the build if missing. */
export function decl(name: string): Decl {
  const d = lean.decls[name];
  if (!d)
    throw new Error(
      `Lean page: ${name} is not in src/data/lean/certificate.json. Add it to [show] extra in ` +
        'src/data/lean/certificate.toml and run python3 scripts/build_lean.py.',
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
export const zipFolder = 'lean-cubic';
