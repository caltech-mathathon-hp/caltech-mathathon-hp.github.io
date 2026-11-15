#!/usr/bin/env python3
"""Generate the Lean page's data from a Lean project (by default the teammate's, lean/cubic).

Reads   the project from git (--repo at --ref; defaults in src/data/lean/certificate.toml), or a
        plain directory (--lean DIR): docs/theorem-index.md, checks/publication-axioms.txt,
        lean-toolchain, lake-manifest.json / lakefile.toml and every .lean file.
Writes  src/data/lean/certificate.json and public/lean/lean-cubic.zip (deterministic).
Fails   on a theorem-index row without a status, an unknown declaration, a sorry/admit or an
        axiom in the code; warns on native_decide.

Another project gets its own settings file and outputs (--config, --out, --zip); see
certificate-shelf.toml. Without a repo_url there, the certificate has no links.

Usage (from site/; REPO defaults to the git repo holding site/):
    python3 scripts/build_lean.py [--repo REPO] [--ref REF]   # write both files
    python3 scripts/build_lean.py [--repo REPO] --check       # exit 1 if either is out of date
    python3 scripts/build_lean.py --lean DIR [--out FILE] [--zip FILE] [--config FILE]
    python3 scripts/test_build_lean.py
"""
from __future__ import annotations

import argparse
import hashlib
import io
import json
import posixpath
import re
import subprocess
import sys
import tarfile
import tempfile
import tomllib
import zipfile
from bisect import bisect_right
from dataclasses import dataclass
from pathlib import Path

SITE = Path(__file__).resolve().parents[1]
CONFIG = SITE / "src" / "data" / "lean" / "certificate.toml"
OUT = SITE / "src" / "data" / "lean" / "certificate.json"
PUBLIC = SITE / "public"

INDEX_MD = "docs/theorem-index.md"
AXIOMS_TXT = "checks/publication-axioms.txt"
CI_WORKFLOW = "lean-certificates.yml"
VERIFY = "checks/Verify.ps1"
AUDIT = "checks/CubicHardness.lean"  # default for [source] audit
DOCS = {
    "readme": "README.md",
    "theoremIndex": "docs/theorem-index.md",
    "model": "docs/model.md",
    "proofRoute": "docs/proof-route.md",
    "verification": "docs/verification.md",
}  # and "audit", from the settings
SKIP_DIRS = {".lake", "lake-packages", "build", ".git", "__pycache__"}
SKIP_FILES = {".DS_Store"}
DEFINITION_KWS = {"def", "abbrev", "structure", "inductive", "class"}
COUNTED_KWS = DEFINITION_KWS | {"theorem", "lemma", "instance"}
STATEMENT_KWS = {"theorem", "lemma"}
ROUTE_KEYS = {"problem", "via", "assumed", "np"}


class Problems:
    def __init__(self) -> None:
        self.errors: list[str] = []
        self.warnings: list[str] = []

    def error(self, msg: str) -> None:
        self.errors.append(msg)

    def warn(self, msg: str) -> None:
        self.warnings.append(msg)


# ---------------------------------------------------------------- getting the project


def git(*args: str) -> str | None:
    """stdout of a git command, or None if it fails."""
    try:
        r = subprocess.run(["git", *args], capture_output=True, text=True, check=False)
    except OSError:
        return None
    return r.stdout.strip() if r.returncode == 0 else None


def read_dir(root: Path) -> dict[str, bytes]:
    """Every file under root (build and VCS folders skipped), by POSIX path, sorted."""
    files = {}
    for p in root.rglob("*"):
        rel = p.relative_to(root)
        if p.is_file() and not SKIP_DIRS.intersection(rel.parts) and p.name not in SKIP_FILES:
            files[rel.as_posix()] = p.read_bytes()
    return dict(sorted(files.items()))


def from_dir(lean: Path) -> tuple[dict[str, bytes], str | None, str | None]:
    out = git("-C", str(lean), "log", "-1", "--format=%H %cs", "--", ".")
    commit, date = out.split() if out else (None, None)
    return read_dir(lean), commit, date


def from_git(repo: Path, ref: str, path: str, problems: Problems) -> tuple[dict[str, bytes], str | None, str | None]:
    """The files of `path` at the last commit on `ref` that touched it."""
    head = git("-C", str(repo), "rev-parse", "--verify", "--quiet", f"{ref}^{{commit}}")
    if not head:
        problems.error(f"cannot resolve {ref} in {repo} (git fetch, or pass --repo / --ref)")
        return {}, None, None
    out = git("-C", str(repo), "log", "-1", "--format=%H %cs", head, "--", path)
    if not out:
        problems.error(f"{path} does not exist at {ref} in {repo}")
        return {}, None, None
    commit, date = out.split()
    tar = subprocess.run(["git", "-C", str(repo), "archive", "--format=tar", commit, path],
                         capture_output=True, check=False)
    if tar.returncode != 0:
        problems.error(f"git archive {commit} {path} failed: {tar.stderr.decode(errors='replace').strip()}")
        return {}, None, None
    with tempfile.TemporaryDirectory() as tmp, tarfile.open(fileobj=io.BytesIO(tar.stdout)) as tf:
        try:
            tf.extractall(tmp, filter="data")
        except TypeError:  # Python < 3.11.4
            tf.extractall(tmp)
        return read_dir(Path(tmp) / path), commit, date


# ---------------------------------------------------------------- Lean source


def _skip(src: str, i: int) -> int | None:
    """If a comment or a string starts at i, the index just after it; else None."""
    n = len(src)
    if src.startswith("--", i):
        j = src.find("\n", i)
        return n if j < 0 else j
    if src.startswith("/-", i):
        depth, i = 1, i + 2
        while i < n and depth:
            if src.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif src.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                i += 1
        return i
    if src[i] == '"':
        j = i + 1
        while j < n and src[j] != '"':
            j += 2 if src[j] == "\\" else 1
        return min(j + 1, n)
    return None


def strip_comments(src: str, keep_strings: bool = True, blank: bool = False) -> str:
    """Remove -- and /- -/ comments (docstrings too). keep_strings=False empties string literals.
    blank=True replaces what it removes by spaces and keeps the newlines, so lines stay aligned."""
    out, i, n = [], 0, len(src)
    while i < n:
        j = _skip(src, i)
        if j is None:
            out.append(src[i])
            i += 1
            continue
        piece = src[i:j]
        is_string = piece.startswith('"')
        if is_string and keep_strings:
            out.append(piece)
        elif blank:
            out.append(re.sub(r"[^\n]", " ", piece))
        elif is_string:
            out.append('""')
        i = j
    return "".join(out)


def docstrings(src: str) -> dict[int, int]:
    """For every /-- -/ comment: the line it ends on -> the line it starts on (0-based)."""
    nl = [k for k, c in enumerate(src) if c == "\n"]
    line = lambda k: bisect_right(nl, k)
    out, i, n = {}, 0, len(src)
    while i < n:
        j = _skip(src, i)
        if j is None:
            i += 1
            continue
        if src.startswith("/--", i):
            out[line(j - 1)] = line(i)
        i = j
    return out


OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"


def proof_start(decl: str) -> int:
    """Index where the body of a declaration starts: the first `:=`, `where`, or `|` at the start
    of a line, at bracket depth 0, outside comments and strings. len(decl) if there is none."""
    i, n, depth, line_start = 0, len(decl), 0, True
    word = lambda k: 0 <= k < n and (decl[k].isalnum() or decl[k] in "_'.")
    while i < n:
        j = _skip(decl, i)
        if j is not None:
            i = j
            continue
        c = decl[i]
        if c == "\n":
            line_start = True
            i += 1
            continue
        if c in " \t":
            i += 1
            continue
        if depth == 0:
            if decl.startswith(":=", i):
                return i
            if decl.startswith("where", i) and not word(i - 1) and not word(i + 5):
                return i
            if c == "|" and line_start and i > 0:
                return i
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth = max(0, depth - 1)
        line_start = False
        i += 1
    return n


MODIFIERS = r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*"
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*" + MODIFIERS +
    r"(?P<kw>class\s+inductive|def|theorem|lemma|abbrev|structure|inductive|class|instance|opaque|axiom)\b"
    r"(?:[ \t]+(?P<name>[^\s:({\[⦃⟨]+))?"
)
AXIOM_RE = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\]\s*)*" + MODIFIERS + r"axiom\s+\S")
SORRY_RE = re.compile(r"(?<![\w.])(sorry|admit)(?![\w'])")
NATIVE_RE = re.compile(r"(?<![\w.])native_decide(?![\w'])|\bdecide\s*\+native\b")
# A line at column 0 that continues the declaration above rather than starting something new.
CONTINUES = re.compile(r"^(\||where\b|deriving\b|termination_by\b|decreasing_by\b|with\b|\)|\]|\})")


@dataclass
class Decl:
    full: str | None  # None for an anonymous instance
    kw: str
    file: str
    line: int  # 1-based, the line of the keyword
    text: str  # with its attributes and the docstring directly above


def scan(rel: str, src: str) -> list[Decl]:
    """The declarations that start at column 0 of one .lean file, with their namespaces."""
    lines = src.split("\n")
    masked = strip_comments(src, blank=True).split("\n")  # a commented-out declaration is not found
    docs = docstrings(src)
    stack: list[tuple[str, str]] = []  # ('ns' | 'sec', name)
    starts = []
    for i, line in enumerate(masked):
        if not line or line[0].isspace():
            continue
        if m := re.match(r"^namespace\s+(\S+)", line):
            stack.append(("ns", m.group(1)))
        elif m := re.match(r"^(?:noncomputable\s+)?(?:section|mutual)\b\s*(\S*)", line):
            stack.append(("sec", m.group(1)))
        elif re.match(r"^end\b", line):
            if stack:
                stack.pop()
        elif m := DECL_RE.match(line):
            kw = "class" if m.group("kw").startswith("class") else m.group("kw")
            name = m.group("name")
            if name is None and kw != "instance":
                continue
            if name is None:
                full = None
            else:
                name = name.replace("«", "").replace("»", "")
                ns = ".".join(n for k, n in stack if k == "ns")
                full = name[len("_root_."):] if name.startswith("_root_.") else (f"{ns}.{name}" if ns else name)
            starts.append((i, kw, full))
    decls = []
    for i, kw, full in starts:
        # upward over attribute lines and the docstring directly above
        a = i
        while a > 0:
            prev = lines[a - 1]
            if prev.startswith("@["):
                a -= 1
            elif a - 1 in docs and prev.rstrip().endswith("-/"):
                a = docs[a - 1]
                break
            else:
                break
        # downward to the next line at column 0 that starts something new
        b = i + 1
        while b < len(lines):
            ln = lines[b]
            if ln and not ln[0].isspace() and not CONTINUES.match(ln):
                break
            b += 1
        text = "\n".join(lines[a:b]).rstrip()
        decls.append(Decl(full, kw, rel, i + 1, text))
    return decls


def without_proof(text: str) -> str:
    """Docstring and statement of a declaration, without the proof."""
    return text[: proof_start(text)].rstrip()


def has_sorry(text: str) -> bool:
    return bool(SORRY_RE.search(strip_comments(text, keep_strings=False)))


def line_of(src: str, k: int) -> int:
    return src.count("\n", 0, k) + 1


# ---------------------------------------------------------------- docs/theorem-index.md


def split_cells(line: str) -> list[str]:
    """Split a table row at | outside backticks; \\| is a literal bar."""
    cells, cur, in_code = [], [], False
    s = line.strip()
    if s.startswith("|"):
        s = s[1:]
    if s.endswith("|") and not s.endswith("\\|"):
        s = s[:-1]
    i = 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s) and s[i + 1] == "|":
            cur.append("|")
            i += 2
            continue
        if c == "`":
            in_code = not in_code
        if c == "|" and not in_code:
            cells.append("".join(cur).strip())
            cur = []
        else:
            cur.append(c)
        i += 1
    cells.append("".join(cur).strip())
    return cells


LINK_RE = re.compile(r"\[([^\]]*)\]\(\s*([^)\s]*)(?:\s+\"[^\"]*\")?\s*\)")


def parse_names(cell: str) -> list[str]:
    ticked = re.findall(r"`([^`]+)`", cell)
    parts = ticked or re.split(r"[,;]", LINK_RE.sub(r"\1", cell))
    return [p.strip() for p in parts if p.strip() and p.strip() not in ("—", "-")]


def note_of(cell: str) -> str:
    s = LINK_RE.sub("", cell)
    s = re.sub(r"\s+", " ", s)
    s = re.sub(r"\s*([,;])(?:\s*[,;])+", r"\1", s)  # separators left next to each other by a removed link
    return s.strip(",; ")


def status_of(note: str, kws: list[str | None]) -> str | None:
    s = note.lower()
    if "proposition only" in s:
        return "premise"
    if "cook" in s and "levin" in s:
        return "conditional"
    if "unconditional" in s:
        return "proved"
    if "definition" in s:
        return "definition"
    if kws and all(k in DEFINITION_KWS for k in kws):
        return "definition"
    return None


def read_index_table(md: str) -> list[tuple[int, str, str, str]]:
    """(line, concept, declaration, source) for each row of the table with a Declaration column."""
    lines = md.split("\n")
    in_fence = False
    for i, line in enumerate(lines):
        if line.lstrip().startswith("```"):
            in_fence = not in_fence
        if in_fence or not line.lstrip().startswith("|") or i + 1 >= len(lines):
            continue
        if not re.match(r"^\s*\|?\s*:?-{3,}", lines[i + 1]):
            continue
        header = [c.lower() for c in split_cells(line)]
        col = lambda word, default: next((k for k, h in enumerate(header) if word in h), default)
        dc = col("declaration", None)
        if dc is None:
            continue
        cc, sc = col("concept", 0), col("source", col("status", 2))
        rows = []
        for j in range(i + 2, len(lines)):
            if not lines[j].lstrip().startswith("|"):
                break
            cells = split_cells(lines[j])
            get = lambda k: cells[k] if k < len(cells) else ""
            rows.append((j + 1, get(cc), get(dc), get(sc)))
        return rows
    return []


# ---------------------------------------------------------------- checks/publication-axioms.txt


def parse_axioms(text: str) -> list[dict]:
    """`Name rest-of-type` blocks (continued on indented lines), each followed by Lean's
    `'Name' depends on axioms: [a, b]` (which may wrap) or `'Name' does not depend on any axioms`."""
    out: list[dict] = []
    types: dict[str, list[str]] = {}
    cur: list[str] | None = None  # the type being read
    lines = text.replace("\r\n", "\n").split("\n")
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^'([^']+)' (depends on axioms: \[|does not depend on any axioms)", line)
        if m:
            name, axioms = m.group(1), []
            if m.group(2).startswith("depends"):
                buf = line[m.end():]
                while "]" not in buf and i + 1 < len(lines):
                    i += 1
                    buf += " " + lines[i]
                axioms = [a.strip() for a in buf.split("]")[0].split(",") if a.strip()]
            typ = " ".join(" ".join(types[name]).split()) if name in types else None
            out.append({"name": name, "type": typ, "axioms": axioms})
            cur = None
        elif line and not line[0].isspace():
            name, _, rest = line.partition(" ")
            cur = types[name] = [rest]
        elif line.strip() and cur is not None:
            cur.append(line)
        i += 1
    return out


# ---------------------------------------------------------------- build


def resolve(name: str, namespace: str, index: dict[str, list[Decl]]) -> tuple[Decl | None, str | None]:
    """`<namespace>.<name>`, else the unique declaration whose name ends in `.<name>`."""
    exact = index.get(f"{namespace}.{name}" if namespace else name)
    if exact:
        if len(exact) > 1:
            return None, f"`{name}` is declared more than once ({', '.join(d.file for d in exact)})"
        return exact[0], None
    cands = sorted(k for k in index if k == name or k.endswith("." + name))
    if len(cands) == 1 and len(index[cands[0]]) == 1:
        return index[cands[0]][0], None
    if cands:
        return None, f"`{name}` is ambiguous: {', '.join(cands)}"
    return None, f"`{name}` not found"


def project_versions(files: dict[str, bytes]) -> tuple[str | None, str | None]:
    text = lambda k: files[k].decode("utf-8") if k in files else None
    lean = None
    if tc := text("lean-toolchain"):
        lean = tc.strip().split(":")[-1].removeprefix("v")
    mathlib = None
    if man := text("lake-manifest.json"):
        try:
            for p in json.loads(man).get("packages", []):
                if p.get("name") == "mathlib":
                    mathlib = p.get("inputRev") or (p.get("rev") or "")[:7] or None
        except json.JSONDecodeError:
            pass
    if not mathlib and (lf := text("lakefile.toml")):
        try:
            for r in tomllib.loads(lf).get("require", []):
                if r.get("name") == "mathlib":
                    mathlib = r.get("rev")
        except tomllib.TOMLDecodeError:
            pass
    if not mathlib and (lf := text("lakefile.lean")):
        m = re.search(r'require\s+"?mathlib"?\s+from\s+git\s+"[^"]+"\s*@\s*"([^"]+)"', lf)
        mathlib = m.group(1) if m else None
    return lean, mathlib


def make_zip(files: dict[str, bytes], top: str, date: str | None) -> bytes:
    """Same files and date in, same bytes out: sorted entries, fixed times and permissions."""
    stamp = (1980, 1, 1, 0, 0, 0)
    if date:
        y, m, d = (int(x) for x in date.split("-"))
        stamp = (max(y, 1980), m, d, 0, 0, 0)
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w") as zf:
        for rel in sorted(files):
            zi = zipfile.ZipInfo(f"{top}/{rel}", date_time=stamp)
            zi.create_system = 3
            zi.external_attr = 0o100644 << 16
            zi.compress_type = zipfile.ZIP_DEFLATED
            zf.writestr(zi, files[rel], compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    return buf.getvalue()


def under(rel: str, folders: list[str]) -> bool:
    """Whether rel is in one of these folders of the project."""
    return any(rel == f or rel.startswith(f + "/") for f in folders)


def build(files: dict[str, bytes], cfg: dict, commit: str | None, date: str | None,
          problems: Problems) -> tuple[dict, bytes]:
    src_cfg, show = cfg.get("source", {}), cfg.get("show", {})
    repo_url = src_cfg.get("repo_url", "").rstrip("/")
    branch = src_cfg.get("branch", "")
    path = src_cfg.get("path", "lean/cubic").strip("/")
    namespace = src_cfg.get("namespace", "")
    zip_path = src_cfg.get("zip", "lean/lean-cubic.zip")
    audit = src_cfg.get("audit", AUDIT)
    has_index = src_cfg.get("index", True)  # false: the project has no docs/theorem-index.md
    exclude = [f.strip("/") for f in src_cfg.get("count_exclude", [])]
    at = commit or branch

    def blob(rel: str, frag: str = "") -> str | None:
        """A file of the repo at the commit read; None when the project has no public address."""
        if not repo_url:
            return None
        return f"{repo_url}/blob/{at}/{rel}" + (f"#{frag}" if frag else "")

    # the code. Files under count_exclude (a vendored library) are checked and searched for
    # names like the others, but not counted as the project's own.
    sources = {rel: b.decode("utf-8").replace("\r\n", "\n") for rel, b in files.items() if rel.endswith(".lean")}
    index: dict[str, list[Decl]] = {}
    sorries = axioms = native = 0
    own = {"files": 0, "lines": 0, "declarations": 0, "theorems": 0}
    other = dict.fromkeys(own, 0)
    for rel, src in sources.items():
        tally = other if under(rel, exclude) else own
        tally["files"] += 1
        tally["lines"] += sum(1 for ln in src.split("\n") if ln.strip())
        code = strip_comments(src, keep_strings=False, blank=True)
        for m in SORRY_RE.finditer(code):
            sorries += 1
            problems.error(f"{rel}:{line_of(code, m.start())}: `{m.group(1)}` in the code")
        for m in AXIOM_RE.finditer(code):
            axioms += 1
            problems.error(f"{rel}:{line_of(code, m.end() - 1)}: an `axiom` declaration")
        for m in NATIVE_RE.finditer(code):
            native += 1
            problems.warn(f"{rel}:{line_of(code, m.start())}: `{m.group(0)}` (trusts the compiler)")
        for d in scan(rel, src):
            tally["declarations"] += d.kw in COUNTED_KWS
            tally["theorems"] += d.kw in STATEMENT_KWS
            if d.full:
                index.setdefault(d.full, []).append(d)

    decls: dict[str, dict] = {}

    def show_decl(name: str, where: str) -> Decl | None:
        d, err = resolve(name, namespace, index)
        if err:
            problems.error(f"{where}: {err}")
            return None
        if name not in decls:
            code = without_proof(d.text) if d.kw in STATEMENT_KWS else d.text
            decls[name] = {"full": d.full, "kw": d.kw, "file": d.file, "line": d.line,
                           "href": blob(f"{path}/{d.file}", f"L{d.line}"),
                           "code": code.rstrip()}
        return d

    # the theorem index
    rows = []
    if not has_index:
        pass
    elif INDEX_MD not in files:
        problems.error(f"{path}/{INDEX_MD} is missing")
    else:
        table = read_index_table(files[INDEX_MD].decode("utf-8"))
        if not table:
            problems.error(f"{path}/{INDEX_MD} has no table with a Declaration column")
        for lineno, concept, decl_cell, source_cell in table:
            where = f"{INDEX_MD}:{lineno}"
            names = parse_names(decl_cell)
            found = [show_decl(n, where) for n in names]
            note = note_of(source_cell)
            status = status_of(note, [d.kw if d else None for d in found])
            if status is None:
                problems.error(f"{where}: cannot tell the status of '{concept}' from '{note}' "
                               "(say definitions, unconditional, Cook–Levin or proposition only)")
            links = []
            for label, href in LINK_RE.findall(source_cell):
                if not repo_url:
                    href = None
                elif not re.match(r"^[a-z][a-z0-9+.-]*:", href, re.I):
                    target, _, frag = href.partition("#")
                    href = blob(posixpath.normpath(posixpath.join(path, posixpath.dirname(INDEX_MD), target)), frag)
                links.append({"label": label.strip(), "href": href})
            rows.append({"concept": LINK_RE.sub(r"\1", concept).strip(), "names": names,
                         "status": status, "sources": links, "note": note})
    for name in show.get("extra", []):
        show_decl(name, "[show] extra")
    route = read_route(cfg.get("route", []), show_decl, problems)

    docs = {**DOCS, "audit": audit}
    if not has_index:  # a project outside the team's format: link the files it has
        docs = {key: rel for key, rel in docs.items() if rel in files or key == "audit"}
    for key, rel in docs.items():
        if rel not in files:
            problems.warn(f"{path}/{rel} is missing" + (f"; links.docs.{key} points nowhere" if repo_url else ""))

    lean, mathlib = project_versions(files)
    project = {
        "lean": lean, "mathlib": mathlib, **own,
        "sorries": sorries, "axioms": axioms, "nativeDecide": native,
        "checks": {"audit": audit, "verify": VERIFY if VERIFY in files else None},
    }
    if exclude:
        project["excluded"] = {"paths": exclude, "files": other["files"], "lines": other["lines"],
                               "theorems": other["theorems"]}
    links = {} if not repo_url else {
        "repo": repo_url,
        "tree": f"{repo_url}/tree/{at}/{path}",
        "clone": f"{repo_url}.git",
        "branch": branch,
        "ci": f"{repo_url}/actions/workflows/{src_cfg.get('ci', CI_WORKFLOW)}",  # [source] ci: its own workflow
        "docs": {key: blob(f"{path}/{rel}") for key, rel in docs.items()},
    }
    folder = Path(zip_path).stem  # the zip holds one folder, named like the zip
    zip_bytes = make_zip(files, folder, date)
    data = {
        "_comment": f"Written by scripts/build_lean.py from {path}. Do not edit by hand.",
        "id": src_cfg.get("id", "cubic"),
        "source": {"ref": src_cfg.get("ref"), "path": path, "commit": commit, "date": date},
        "project": project,
        "links": links,
        "download": {"path": zip_path, "folder": folder, "bytes": len(zip_bytes),
                     "sha256": hashlib.sha256(zip_bytes).hexdigest()},
        "index": rows,
        "route": route,
        "decls": decls,
        "axiomReport": parse_axioms(files[AXIOMS_TXT].decode("utf-8")) if AXIOMS_TXT in files else [],
    }
    return data, zip_bytes


def read_route(steps: list[dict], show_decl, problems: Problems) -> list[dict]:
    """The [[route]] tables: the chain of problems, each reached from the one before by `via`
    (`assumed` marks the hypothesis), with `np` proving it is in NP. Their names join decls."""
    route = []
    for k, step in enumerate(steps, 1):
        where = f"[[route]] {k}"
        if unknown := sorted(set(step) - ROUTE_KEYS):
            problems.error(f"{where}: unknown key {', '.join(unknown)} (use {', '.join(sorted(ROUTE_KEYS))})")
        if not isinstance(step.get("problem"), str) or not step["problem"].strip():
            problems.error(f"{where}: no problem")
        for key in ("via", "np"):
            if step.get(key):
                show_decl(step[key], where)
        route.append({"problem": step.get("problem"), "via": step.get("via") or None,
                      "assumed": bool(step.get("assumed", False)), "np": step.get("np") or None})
    return route


def summary(data: dict) -> str:
    sts = [r["status"] for r in data["index"]]
    counts = ", ".join(f"{s} {sts.count(s)}" for s in ("definition", "proved", "conditional", "premise") if s in sts)
    p, src = data["project"], data["source"]
    at = f"{src['commit'][:7]} ({src['date']})" if src["commit"] else "no commit"
    files = f"{p['files']} files"
    if x := p.get("excluded"):
        files += f" (and {x['files']} in {', '.join(x['paths'])}, not counted)"
    rows = f"{len(sts)} index rows ({counts})" if sts else "no index"
    return (f"{at}: {rows}, {len(data['decls'])} declarations shown, "
            f"{files}, {p['theorems']} theorems, zip {data['download']['bytes']} bytes")


def shown(p: Path) -> str:
    try:
        return str(p.resolve().relative_to(SITE))
    except ValueError:
        return str(p)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", type=Path, help="git repo holding the Lean project (default: the one holding site/)")
    ap.add_argument("--ref", help="git ref (default: [source].ref in certificate.toml)")
    ap.add_argument("--lean", type=Path, help="read the Lean project from this directory instead of git")
    ap.add_argument("--config", type=Path, default=CONFIG, help="settings (default src/data/lean/certificate.toml)")
    ap.add_argument("--out", type=Path, default=OUT, help="JSON to write (default src/data/lean/certificate.json)")
    ap.add_argument("--zip", type=Path, help="zip to write (default public/<[source].zip>)")
    ap.add_argument("--check", action="store_true", help="write nothing; exit 1 if either output is out of date")
    args = ap.parse_args(argv)

    problems = Problems()
    try:
        cfg = tomllib.loads(args.config.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as e:
        print(f"error: {args.config}: {e}", file=sys.stderr)
        return 1
    src_cfg = cfg.get("source", {})
    zip_out = args.zip or PUBLIC / src_cfg.get("zip", "lean/lean-cubic.zip")

    if args.lean:
        files, commit, date = from_dir(args.lean.resolve())
        rerun = f"python3 scripts/build_lean.py --lean {args.lean}"
    else:
        repo = args.repo or Path(git("-C", str(SITE), "rev-parse", "--show-toplevel") or SITE)
        ref = args.ref or src_cfg.get("ref", "HEAD")
        cfg.setdefault("source", {})["ref"] = ref
        files, commit, date = from_git(repo.resolve(), ref, src_cfg.get("path", "lean/cubic"), problems)
        rerun = f"python3 scripts/build_lean.py --repo {args.repo or repo}" + (f" --ref {args.ref}" if args.ref else "")
    for flag, value, default in (("--config", args.config, CONFIG), ("--out", args.out, OUT), ("--zip", args.zip, None)):
        if value and value != default:
            rerun += f" {flag} {value}"
    data, zip_bytes = build(files, cfg, commit, date, problems) if files else ({}, b"")
    for w in problems.warnings:
        print(f"warning: {w}", file=sys.stderr)
    for e in problems.errors:
        print(f"error: {e}", file=sys.stderr)
    if problems.errors or not files:
        if not problems.errors:
            print("error: the Lean project is empty", file=sys.stderr)
        return 1

    text = json.dumps(data, ensure_ascii=False, indent=2) + "\n"
    if args.check:
        # The zip's bytes depend on the machine's zlib, so compare what it holds, and check
        # that certificate.json describes the zip that is there.
        stale = []
        old: dict = {}
        try:
            old = json.loads(args.out.read_text(encoding="utf-8"))
            if without_zip_hash(old) != without_zip_hash(data):
                stale.append(f"{shown(args.out)} is out of date")
        except (OSError, json.JSONDecodeError):
            stale.append(f"{shown(args.out)} is missing or unreadable")
        try:
            blob = zip_out.read_bytes()
            if zip_members(blob) != zip_members(zip_bytes):
                stale.append(f"{shown(zip_out)} is out of date")
            elif old and old.get("download", {}) != {
                **data["download"],
                "bytes": len(blob),
                "sha256": hashlib.sha256(blob).hexdigest(),
            }:
                stale.append(f"{shown(args.out)} does not describe {shown(zip_out)}")
        except (OSError, zipfile.BadZipFile):
            stale.append(f"{shown(zip_out)} is missing or unreadable")
        if stale:
            print(f"error: {'; '.join(stale)}; run {rerun}", file=sys.stderr)
            return 1
        print(f"ok: {summary(data)}")
        return 0
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(text, encoding="utf-8")
    zip_out.parent.mkdir(parents=True, exist_ok=True)
    zip_out.write_bytes(zip_bytes)
    print(f"wrote {shown(args.out)} and {shown(zip_out)}: {summary(data)}")
    return 0


def without_zip_hash(data: dict) -> dict:
    """The certificate without the zip's size and hash, which depend on the machine's zlib."""
    download = {k: v for k, v in data.get("download", {}).items() if k not in ("bytes", "sha256")}
    return {**data, "download": download}


def zip_members(blob: bytes) -> list[tuple[str, int, bytes]]:
    """What a zip holds: each member's name, permissions and content, in order."""
    with zipfile.ZipFile(io.BytesIO(blob)) as z:
        return [(i.filename, i.external_attr, z.read(i)) for i in z.infolist()]


if __name__ == "__main__":
    sys.exit(main())
