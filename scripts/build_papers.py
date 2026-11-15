#!/usr/bin/env python3
"""Generate src/data/papers/papers.json from the team's literature folder.

Facts come from ../private/literature/, the literature notes in the team's private repository,
checked out next to this one in the workspace (the single source of truth):
  INDEX.md        one row per paper: key, year, ref (authors; venue), tags, relevance, status, takeaway
  refs.bib        authors (surnames), title, DOI / URL / arXiv id
  notes/<key>.md  checked to exist (one note per INDEX row)

Judgement comes from src/data/papers/curation.toml (hand-edited): themes (lanes), the
one-clause gist shown by default, the longer takeaway and "why it matters" shown on demand,
relations between papers, wording overrides, and papers that are in refs.bib but not in INDEX.md.
A paper whose curation entry has `offsite = "<reason>"` stays in the literature folder but is left
out of papers.json, so the website does not list it.

Usage (from site/):
    python3 scripts/build_papers.py           # write src/data/papers/papers.json
    python3 scripts/build_papers.py --check   # validate only, exit 1 on errors

Python 3.11+ standard library only (tomllib).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import tomllib
import unicodedata
from pathlib import Path

SITE = Path(__file__).resolve().parents[1]
ROOT = SITE.parent  # the workspace: private/ and site/ side by side
LIT = ROOT / "private" / "literature"
INDEX = LIT / "INDEX.md"
BIB = LIT / "refs.bib"
NOTES = LIT / "notes"
CURATION = SITE / "src" / "data" / "papers" / "curation.toml"
OUT = SITE / "src" / "data" / "papers" / "papers.json"

RELATION_KINDS = {
    "reduces-from", "builds-on", "extends", "variant-of", "refutes",
    "surveys", "formalizes", "answers", "discusses",
}
STATUSES = {"read", "skim", "abstract", "todo"}
GIST_MAX = 110  # characters; the gist is the one line a reader sees by default

# Default lane for a paper the curation file does not mention, from its INDEX tags
# (first match wins). Curation overrides this.
TAG_TO_THEME = [
    ("core", "core"),
    ("formal", "formal"),
    ("approx", "approx"),
    ("string-fold", "variants"),
    ("lattice-variant", "variants"),
    ("alt-proof", "variants"),
    ("reduction-source", "sources"),
    ("gadget", "sources"),
    ("survey", "background"),
    ("background", "background"),
    ("auxiliary", "background"),
]


class Problems:
    def __init__(self) -> None:
        self.errors: list[str] = []
        self.warnings: list[str] = []

    def error(self, msg: str) -> None:
        self.errors.append(msg)

    def warn(self, msg: str) -> None:
        self.warnings.append(msg)


# ---------------------------------------------------------------- LaTeX → text

ACCENTS = {
    "'": "\u0301", '"': "\u0308", "^": "\u0302", "`": "\u0300", "~": "\u0303",
    "=": "\u0304", ".": "\u0307", "v": "\u030c", "u": "\u0306", "H": "\u030b",
    "c": "\u0327", "k": "\u0328",
}
SPECIALS = {
    "o": "ø", "O": "Ø", "ss": "ß", "ae": "æ", "AE": "Æ", "aa": "å", "AA": "Å",
    "l": "ł", "L": "Ł", "i": "ı", "j": "ȷ",
}


def latex_to_text(s: str) -> str:
    # dotless i under an accent: {\'\i} → í
    s = re.sub(r"(\\['\"^`~=.vuHck]\s*\{?\s*)\\i(?![A-Za-z])", r"\1i", s)
    # \url{x} → x ; \& → & ; -- → –
    s = re.sub(r"\\url\{([^}]*)\}", r"\1", s)
    # accented letters: \'a, \'{a}, {\'a}, \v{n}, \v n
    s = re.sub(
        r"\\([vuHck])\s*\{\s*([A-Za-z])\s*\}|\\([vuHck])\s+([A-Za-z])",
        lambda m: (m.group(2) or m.group(4)) + ACCENTS[m.group(1) or m.group(3)],
        s,
    )
    s = re.sub(
        r"\\(['\"^`~=.])\s*\{?\s*([A-Za-z])\s*\}?",
        lambda m: m.group(2) + ACCENTS[m.group(1)],
        s,
    )
    s = re.sub(
        r"\\(ss|ae|AE|aa|AA|o|O|l|L)(?![A-Za-z])\s*",
        lambda m: SPECIALS[m.group(1)],
        s,
    )
    s = s.replace("\\&", "&").replace("\\_", "_").replace("\\%", "%")
    s = s.replace("---", "—").replace("--", "–")
    s = s.replace("{", "").replace("}", "")
    s = re.sub(r"\s+", " ", s).strip()
    return unicodedata.normalize("NFC", s)


# ---------------------------------------------------------------- refs.bib

def parse_bib(text: str) -> dict[str, dict[str, str]]:
    """Minimal BibTeX reader: @type{key, field = {…} | "…" | number, …}."""
    entries: dict[str, dict[str, str]] = {}
    i = 0
    while True:
        m = re.compile(r"@(\w+)\s*\{\s*([^,\s]+)\s*,").search(text, i)
        if not m:
            break
        etype, key = m.group(1).lower(), m.group(2)
        j = m.end()
        fields: dict[str, str] = {"_type": etype}
        depth = 1
        # scan fields until the entry's closing brace
        while j < len(text) and depth > 0:
            fm = re.compile(r"\s*([A-Za-z_]+)\s*=\s*").match(text, j)
            if not fm:
                # skip separators / closing brace
                c = text[j]
                if c == "}":
                    depth -= 1
                j += 1
                continue
            name = fm.group(1).lower()
            j = fm.end()
            if text[j] == "{":
                d, k = 0, j
                while k < len(text):
                    if text[k] == "{":
                        d += 1
                    elif text[k] == "}":
                        d -= 1
                        if d == 0:
                            break
                    k += 1
                value = text[j + 1 : k]
                j = k + 1
            elif text[j] == '"':
                k = text.index('"', j + 1)
                value = text[j + 1 : k]
                j = k + 1
            else:
                vm = re.compile(r"[^,}\s]+").match(text, j)
                value = vm.group(0) if vm else ""
                j = vm.end() if vm else j + 1
            fields[name] = value.strip()
        entries[key] = fields
        i = j
    return entries


def bib_surnames(author_field: str) -> list[str]:
    names = []
    for raw in re.split(r"\s+and\s+", author_field.strip()):
        raw = raw.strip()
        if not raw:
            continue
        if raw.lower() == "others":
            names.append("contributors")
            continue
        if raw.startswith("{") and raw.endswith("}") and raw.count("{") == 1:
            names.append(latex_to_text(raw))  # corporate / handle, e.g. {MIT Hardness Group}
            continue
        if "," in raw:
            surname = raw.split(",")[0]
        else:
            parts = raw.split()
            surname = parts[-1] if parts else raw
        names.append(latex_to_text(surname))
    return names


def bib_url(fields: dict[str, str]) -> str | None:
    doi = fields.get("doi", "").strip()
    if doi:
        return "https://doi.org/" + doi
    for name in ("url", "howpublished"):
        v = fields.get(name, "")
        m = re.search(r"https?://[^\s}]+", v)
        if m:
            return m.group(0)
    eprint = fields.get("eprint", "").strip()
    if eprint:
        return "https://arxiv.org/abs/" + eprint
    m = re.search(r"https?://[^\s},]+", fields.get("note", ""))
    return m.group(0) if m else None


# ---------------------------------------------------------------- INDEX.md

def parse_index(text: str, problems: Problems) -> list[dict]:
    rows = []
    in_table = False
    for line in text.splitlines():
        if line.startswith("| key | year |"):
            in_table = True
            continue
        if not in_table:
            continue
        if not line.startswith("|"):
            if rows:
                break
            continue
        if re.match(r"^\|[\s\-|]+\|$", line):
            continue
        cells = [c.strip() for c in re.split(r"(?<!\\)\|", line.strip())[1:-1]]
        if len(cells) != 7:
            problems.error(f"INDEX.md: cannot parse row: {line[:80]}")
            continue
        key, year, ref, tags, rel, status, takeaway = cells
        rows.append(
            {
                "key": key,
                "year": int(year),
                "ref": ref,
                "tags": [t.strip() for t in tags.split(",") if t.strip()],
                "relevance": rel.count("★"),
                "status": status,
                "takeaway": takeaway,
            }
        )
    return rows


def venue_from_ref(ref: str) -> str:
    """The INDEX 'ref' column is 'Authors; venue' or 'Authors, venue'."""
    if ";" in ref:
        return ref.split(";", 1)[1].strip()
    if ", " in ref:
        return ref.split(", ", 1)[1].strip()
    return ref.strip()


def apply_abbreviations(s: str, table: dict[str, str]) -> str:
    for short, long in sorted(table.items(), key=lambda kv: -len(kv[0])):
        s = re.sub(r"(?<![\w-])" + re.escape(short) + r"(?![\w-])", long, s)
    return s


def tidy_sentence(s: str) -> str:
    s = s.strip()
    if s and s[0].islower():
        s = s[0].upper() + s[1:]
    if s and s[-1] not in ".!?":
        s += "."
    return s


# ---------------------------------------------------------------- build

def build(problems: Problems) -> dict:
    cur = tomllib.loads(CURATION.read_text(encoding="utf-8"))
    bib = parse_bib(BIB.read_text(encoding="utf-8"))
    index_rows = parse_index(INDEX.read_text(encoding="utf-8"), problems)

    themes = cur.get("themes", [])
    theme_ids = [t["id"] for t in themes]
    if len(set(theme_ids)) != len(theme_ids):
        problems.error("curation: duplicate theme id")
    abbr_venue = cur.get("abbreviations", {}).get("venue", {})
    abbr_text = cur.get("abbreviations", {}).get("text", {})
    cur_papers: dict = cur.get("papers", {})
    extras: dict = cur.get("extra", {})

    # Base records: INDEX rows, then curated extras that exist in refs.bib.
    base: list[dict] = []
    for row in index_rows:
        if not (NOTES / f"{row['key']}.md").exists():
            problems.warn(f"{row['key']}: no notes/{row['key']}.md")
        base.append(row)
    seen = {r["key"] for r in base}
    for key, ex in extras.items():
        if key in seen:
            problems.warn(f"extra.{key}: already in INDEX.md; the INDEX row wins")
            continue
        if key not in bib:
            problems.error(f"extra.{key}: not in refs.bib")
            continue
        year = bib[key].get("year", "")
        base.append(
            {
                "key": key,
                "year": int(ex.get("year", year or 0)),
                "ref": "",
                "tags": ex.get("tags", []),
                "relevance": int(ex.get("relevance", 1)),
                "status": ex.get("status", "todo"),
                "takeaway": "",
                "statusNote": ex.get("statusNote"),
                "venue": ex.get("venue"),
            }
        )

    keys = {r["key"] for r in base}
    for key in cur_papers:
        if key not in keys:
            problems.error(f"curation: papers.{key} is not in INDEX.md or [extra]")
    offsite = {k for k, c in cur_papers.items() if "offsite" in c}
    for k in offsite:
        if not str(cur_papers[k]["offsite"]).strip():
            problems.error(f"{k}: offsite needs a reason")
    keys -= offsite

    papers = []
    for row in base:
        key = row["key"]
        if key in offsite:
            continue
        c = cur_papers.get(key, {})
        b = bib.get(key)
        if b is None:
            problems.error(f"{key}: not in refs.bib")
            b = {}

        authors = bib_surnames(b["author"]) if b.get("author") else []
        if not authors:
            problems.error(f"{key}: no authors in refs.bib")
        title = c.get("title") or latex_to_text(b.get("title", "")) or key

        venue = c.get("venue") or row.get("venue")
        if not venue and b.get("_type") == "book" and b.get("publisher"):
            venue = latex_to_text(b["publisher"]) + " (book)"
        if not venue and row["ref"]:
            venue = venue_from_ref(row["ref"])
        if not venue and b.get("journal"):
            venue = latex_to_text(b["journal"])
            if b.get("volume"):
                venue += " " + b["volume"] + (f"({b['number']})" if b.get("number") else "")
        if venue:
            venue = apply_abbreviations(venue, abbr_venue)

        # gist: one clause, always shown. takeaway: more detail, shown on demand. A curated
        # gist replaces the terse INDEX takeaway; without one, the INDEX text becomes the gist.
        gist = c.get("gist") or ""
        takeaway = c.get("takeaway") or ""
        if not gist:
            gist = row["takeaway"]
            if key in cur_papers:
                problems.warn(f"{key}: no gist in curation; using the INDEX takeaway")
        if not gist:
            problems.error(f"{key}: no gist")
        gist = tidy_sentence(apply_abbreviations(gist, abbr_text))
        if len(gist) > GIST_MAX:
            problems.warn(f"{key}: gist is {len(gist)} characters; keep it under {GIST_MAX}")
        if takeaway:
            takeaway = tidy_sentence(apply_abbreviations(takeaway, abbr_text))

        if c.get("themes"):
            paper_themes = list(c["themes"])
        else:
            paper_themes = [next((th for tag, th in TAG_TO_THEME if tag in row["tags"]), "background")]
            problems.warn(f"{key}: not curated; lane '{paper_themes[0]}' guessed from tags {row['tags']}")
        for th in paper_themes:
            if th not in theme_ids:
                problems.error(f"{key}: unknown theme '{th}'")

        rel = int(c.get("relevance", row["relevance"]))
        if rel not in (1, 2, 3):
            problems.error(f"{key}: relevance must be 1–3, got {rel}")
            rel = max(1, min(3, rel))

        status = row["status"]
        if status not in STATUSES:
            problems.warn(f"{key}: unknown status '{status}'")

        paper: dict = {
            "key": key,
            "year": row["year"],
            "authors": authors,
            "title": title,
        }
        if venue:
            paper["venue"] = venue
        url = c.get("url") or bib_url(b)
        if url:
            paper["url"] = url
        paper["themes"] = paper_themes
        paper["relevance"] = rel
        paper["gist"] = gist
        if takeaway:
            paper["takeaway"] = takeaway
        if c.get("badge"):
            paper["badge"] = c["badge"]
        if c.get("why"):
            paper["why"] = tidy_sentence(c["why"])
        relations = []
        for r in c.get("relations", []):
            if r.get("kind") not in RELATION_KINDS:
                problems.error(f"{key}: relation kind '{r.get('kind')}' unknown")
            if r.get("to") in offsite:
                problems.error(f"{key}: relation to '{r.get('to')}', which is offsite")
            elif r.get("to") not in keys:
                problems.error(f"{key}: relation to unknown paper '{r.get('to')}'")
            if r.get("to") == key:
                problems.error(f"{key}: relation to itself")
            out = {"to": r["to"], "kind": r["kind"]}
            if r.get("note"):
                out["note"] = tidy_sentence(r["note"])
            relations.append(out)
        if relations:
            paper["relations"] = relations
        paper["status"] = status
        note = c.get("statusNote") or row.get("statusNote")
        if note:
            paper["statusNote"] = tidy_sentence(note)

        for field in ("gist", "takeaway", "why"):
            if '"' in paper.get(field, "") or "“" in paper.get(field, ""):
                problems.warn(f"{key}: {field} contains a quotation; the Context page allows one quote")
        papers.append(paper)

    papers.sort(key=lambda p: (p["year"], p["key"]))

    # Duplicate relations (same pair and kind) are almost certainly mistakes.
    pairs = set()
    for p in papers:
        for r in p.get("relations", []):
            t = (p["key"], r["to"], r["kind"])
            if t in pairs:
                problems.warn(f"{p['key']}: duplicate relation {r['kind']} → {r['to']}")
            pairs.add(t)

    out_themes = []
    for t in themes:
        th = {"id": t["id"], "label": t["label"]}
        for f in ("short", "description", "color"):
            if t.get(f):
                th[f] = t[f]
        out_themes.append(th)

    return {
        "_comment": (
            "GENERATED by scripts/build_papers.py from the team's literature notes (facts) and "
            "src/data/papers/curation.toml (themes, gist, takeaway, why, relations). Do not edit by hand."
        ),
        "themes": out_themes,
        "papers": papers,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true", help="validate only; do not write papers.json")
    args = ap.parse_args()

    problems = Problems()
    data = build(problems)
    for w in problems.warnings:
        print(f"warning: {w}", file=sys.stderr)
    for e in problems.errors:
        print(f"error: {e}", file=sys.stderr)
    if problems.errors:
        return 1

    n_rel = sum(len(p.get("relations", [])) for p in data["papers"])
    by_theme = {t["id"]: 0 for t in data["themes"]}
    for p in data["papers"]:
        by_theme[p["themes"][0]] = by_theme.get(p["themes"][0], 0) + 1
    summary = ", ".join(f"{k} {v}" for k, v in by_theme.items())
    if args.check:
        print(f"ok: {len(data['papers'])} papers, {n_rel} relations ({summary})")
        return 0
    OUT.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {OUT.relative_to(SITE)}: {len(data['papers'])} papers, {n_rel} relations ({summary})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
