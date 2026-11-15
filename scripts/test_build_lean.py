#!/usr/bin/env python3
"""Tests for build_lean.py, on the made-up project in scripts/fixtures/lean-cubic/.

Run from site/:  python3 scripts/test_build_lean.py
"""
from __future__ import annotations

import hashlib
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import tomllib
import unittest
import zipfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import build_lean as bl  # noqa: E402

FIXTURE = HERE / "fixtures" / "lean-cubic"
CONFIG = HERE / "fixtures" / "certificate.toml"
SCRIPT = HERE / "build_lean.py"


def load_cfg() -> dict:
    return tomllib.loads(CONFIG.read_text(encoding="utf-8"))


def build_fixture(files: dict[str, bytes] | None = None, cfg: dict | None = None, date: str | None = None):
    problems = bl.Problems()
    data, zip_bytes = bl.build(files or bl.read_dir(FIXTURE), cfg or load_cfg(), None, date, problems)
    return data, zip_bytes, problems


def run(*args: str | Path) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, str(SCRIPT), "--config", str(CONFIG), *map(str, args)],
                          capture_output=True, text=True)


class FixtureBuild(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data, cls.zip, cls.problems = build_fixture()

    def test_no_problems(self):
        self.assertEqual(self.problems.errors, [])
        self.assertEqual(self.problems.warnings, [])

    def test_statuses(self):
        self.assertEqual([r["status"] for r in self.data["index"]],
                         ["definition", "definition", "proved", "conditional", "premise"])

    def test_index_rows(self):
        first, second, third, fourth = self.data["index"][:4]
        self.assertEqual(first["concept"], "Section 2: words and folds")
        self.assertEqual(first["names"], ["Residue", "Sequence", "Fold"])
        self.assertEqual(first["note"], "definitions")
        self.assertEqual(first["sources"], [{
            "label": "Common/Statement",
            "href": "https://github.com/example/hp/blob/main/lean/cubic/ProteinFolding/Common/Statement.lean",
        }])
        self.assertEqual(second["names"], ["bondCount", "emptyFold"])  # split on ;
        self.assertEqual(second["note"], "")  # no status text: inferred from the declarations
        self.assertEqual([s["label"] for s in second["sources"]], ["Statement", "Main"])
        self.assertTrue(third["sources"][0]["href"].endswith("/lean/cubic/ProteinFolding/Main.lean#L5"))
        self.assertEqual(fourth["note"], "Same file; proof with Cook–Levin")
        self.assertEqual(fourth["sources"], [])

    def test_resolution(self):
        decls = self.data["decls"]
        self.assertEqual(decls["Fold"]["full"], "ProteinFolding.Fold")  # exact beats Square.Fold
        self.assertEqual(decls["Square.Fold"]["full"], "ProteinFolding.Square.Fold")
        self.assertEqual(decls["Grid"]["full"], "ProteinFolding.Square.Grid")  # unique suffix
        self.assertEqual(decls["SAT.CookLevin"]["full"], "ProteinFolding.SAT.CookLevin")
        self.assertEqual(list(decls), ["Residue", "Sequence", "Fold", "bondCount", "emptyFold", "bondCount_le",
                                       "main_conditional", "SAT.CookLevin", "Square.Fold", "Grid",
                                       "emptyFold_bonds"])

    def test_resolution_ambiguous_or_missing(self):
        index: dict[str, list[bl.Decl]] = {}
        for rel, b in bl.read_dir(FIXTURE).items():
            if rel.endswith(".lean"):
                for d in bl.scan(rel, b.decode()):
                    if d.full:
                        index.setdefault(d.full, []).append(d)
        d, err = bl.resolve("Instance.Accepts", "ProteinFolding", index)
        self.assertIsNone(d)
        self.assertIn("ambiguous", err)
        self.assertIn("ProteinFolding.Cubic.Instance.Accepts", err)
        self.assertIn("ProteinFolding.Square.Instance.Accepts", err)
        d, err = bl.resolve("Square.Instance.Accepts", "ProteinFolding", index)
        self.assertEqual(d.full, "ProteinFolding.Square.Instance.Accepts")
        d, err = bl.resolve("nothing", "ProteinFolding", index)
        self.assertIn("not found", err)

    def test_theorem_code_has_no_proof(self):
        decls = self.data["decls"]
        self.assertEqual(decls["bondCount_le"]["code"], (
            "/-- No fold has more bonds than the square of its length. -/\n"
            "@[simp]\n"
            "theorem bondCount_le (S : Sequence) (f : Fold S.length) :\n"
            "    bondCount S f ≤ S.length ^ 2"))
        self.assertEqual(decls["main_conditional"]["code"], (
            "/-- The main theorem, assuming Cook–Levin. -/\n"
            "theorem main_conditional (hCL : SAT.CookLevin) : bondCount [] emptyFold = 0"))
        self.assertEqual(decls["emptyFold_bonds"]["code"], "lemma emptyFold_bonds : bondCount [] emptyFold = 0")
        self.assertEqual(decls["emptyFold_bonds"]["kw"], "lemma")

    def test_definition_code_is_whole(self):
        decls = self.data["decls"]
        self.assertEqual(decls["emptyFold"]["code"], (
            "/-- The empty fold, built with a `where` structure. -/\n"
            "def emptyFold : Fold 0 where\n"
            "  pos := fun i => i.elim0\n"
            "  injective_pos := fun i => i.elim0"))
        self.assertEqual(decls["Residue"]["code"], (
            "/-- Hydrophobic (H) and hydrophilic (P) residues. -/\n"
            "inductive Residue where\n  | H\n  | P\n  deriving DecidableEq"))
        self.assertEqual(decls["bondCount"]["code"], "def bondCount (S : Sequence) (f : Fold S.length) : ℕ := 0")

    def test_lines_and_links(self):
        r = self.data["decls"]["Residue"]
        self.assertEqual((r["kw"], r["file"], r["line"]), ("inductive", "ProteinFolding/Common/Statement.lean", 8))
        self.assertEqual(r["href"], "https://github.com/example/hp/blob/main/lean/cubic/"
                                    "ProteinFolding/Common/Statement.lean#L8")
        self.assertEqual(self.data["decls"]["bondCount_le"]["line"], 7)  # the keyword, not the docstring
        links = self.data["links"]
        self.assertEqual(links["tree"], "https://github.com/example/hp/tree/main/lean/cubic")
        self.assertEqual(links["clone"], "https://github.com/example/hp.git")
        self.assertEqual(links["docs"]["audit"],
                         "https://github.com/example/hp/blob/main/lean/cubic/checks/CubicHardness.lean")

    def test_axiom_report(self):
        self.assertEqual(self.data["axiomReport"], [
            {"name": "ProteinFolding.bondCount_le",
             "type": "(S : ProteinFolding.Sequence) (f : ProteinFolding.Fold S.length) : "
                     "ProteinFolding.bondCount S f ≤ S.length ^ 2",
             "axioms": ["propext", "Classical.choice", "Quot.sound"]},
            {"name": "ProteinFolding.emptyFold_bonds",
             "type": ": ProteinFolding.bondCount [] ProteinFolding.emptyFold = 0",
             "axioms": ["propext"]},
        ])

    def test_axiom_report_without_axioms(self):
        self.assertEqual(bl.parse_axioms("Foo.bar : True\n'Foo.bar' does not depend on any axioms\n"),
                         [{"name": "Foo.bar", "type": ": True", "axioms": []}])

    def test_counts(self):
        self.assertEqual(self.data["project"], {
            "lean": "4.24.0", "mathlib": "v4.24.0", "files": 4, "lines": 58,
            # Statement: Residue Sequence Fold bondCount instance; Square: Fold Grid Accepts message
            # Accepts; Main: bondCount_le emptyFold CookLevin main_conditional emptyFold_bonds
            "declarations": 15, "theorems": 3, "sorries": 0, "axioms": 0, "nativeDecide": 0,
        })
        self.assertEqual(self.data["source"], {"ref": "HEAD", "path": "lean/cubic", "commit": None, "date": None})

    def test_zip(self):
        again = build_fixture()[1]
        self.assertEqual(hashlib.sha256(again).hexdigest(), hashlib.sha256(self.zip).hexdigest())
        self.assertEqual(self.data["download"], {"path": "lean/lean-cubic.zip", "bytes": len(self.zip),
                                                 "sha256": hashlib.sha256(self.zip).hexdigest()})
        with zipfile.ZipFile(io.BytesIO(self.zip)) as zf:
            names = zf.namelist()
            self.assertEqual(names, sorted(names))
            self.assertTrue(all(n.startswith("lean-cubic/") for n in names))
            self.assertIn("lean-cubic/ProteinFolding/Main.lean", names)
            self.assertEqual(len(names), len(bl.read_dir(FIXTURE)))
            self.assertEqual({i.date_time for i in zf.infolist()}, {(1980, 1, 1, 0, 0, 0)})
        dated = build_fixture(date="2026-11-14")[1]
        with zipfile.ZipFile(io.BytesIO(dated)) as zf:
            self.assertEqual({i.date_time for i in zf.infolist()}, {(2026, 11, 14, 0, 0, 0)})


class Failures(unittest.TestCase):
    def edited(self, rel: str, old: str, new: str) -> dict[str, bytes]:
        files = bl.read_dir(FIXTURE)
        text = files[rel].decode()
        self.assertIn(old, text)
        files[rel] = text.replace(old, new, 1).encode()
        return files

    def test_sorry_is_an_error(self):
        files = self.edited("ProteinFolding/Main.lean", "  simp [bondCount]", "  sorry")
        _, _, problems = build_fixture(files)
        self.assertEqual(len(problems.errors), 1)
        self.assertIn("ProteinFolding/Main.lean:9: `sorry`", problems.errors[0])

    def test_axiom_is_an_error(self):
        files = self.edited("ProteinFolding/Main.lean", "end SAT", "axiom cheat : False\n\nend SAT")
        data, _, problems = build_fixture(files)
        self.assertTrue(any("`axiom`" in e for e in problems.errors))
        self.assertEqual(data["project"]["axioms"], 1)

    def test_unknown_status_is_an_error(self):
        files = self.edited("docs/theorem-index.md", "unconditional proof", "see the file")
        _, _, problems = build_fixture(files)
        self.assertEqual(len(problems.errors), 1)
        self.assertIn("cannot tell the status of 'The bond bound'", problems.errors[0])

    def test_unknown_declaration_is_an_error(self):
        cfg = load_cfg()
        cfg["show"]["extra"] = ["Instance.Accepts", "nothing"]
        _, _, problems = build_fixture(cfg=cfg)
        self.assertEqual(len(problems.errors), 2)
        self.assertIn("ambiguous", problems.errors[0])
        self.assertIn("`nothing` not found", problems.errors[1])

    def test_native_decide_is_a_warning(self):
        files = self.edited("ProteinFolding/Main.lean", "end ProteinFolding",
                            "theorem four : 2 + 2 = 4 := by native_decide\n\nend ProteinFolding")
        data, _, problems = build_fixture(files)
        self.assertEqual(problems.errors, [])
        self.assertEqual(len(problems.warnings), 1)
        self.assertEqual(data["project"]["nativeDecide"], 1)


class CommandLine(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.tmp)
        self.lean = self.tmp / "lean-cubic"
        shutil.copytree(FIXTURE, self.lean)  # never edit the fixture in place
        self.out, self.zip = self.tmp / "certificate.json", self.tmp / "lean-cubic.zip"

    def build(self, *extra: str) -> subprocess.CompletedProcess:
        return run("--lean", self.lean, "--out", self.out, "--zip", self.zip, *extra)

    def test_check_after_build_and_after_an_edit(self):
        r = self.build()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(self.out.read_text(encoding="utf-8")[-2:], "}\n")
        r = self.build("--check")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertTrue(r.stdout.startswith("ok:"))
        main = self.lean / "ProteinFolding" / "Main.lean"
        main.write_text(main.read_text(encoding="utf-8") + "\n-- edited\n", encoding="utf-8")
        r = self.build("--check")
        self.assertEqual(r.returncode, 1)
        self.assertIn("is out of date", r.stderr)
        self.assertIn("python3 scripts/build_lean.py --lean", r.stderr)

    def test_check_without_zip_fails(self):
        self.assertEqual(self.build().returncode, 0)
        self.zip.unlink()
        r = self.build("--check")
        self.assertEqual(r.returncode, 1)
        self.assertIn("lean-cubic.zip is missing", r.stderr)

    def test_errors_write_nothing(self):
        main = self.lean / "ProteinFolding" / "Main.lean"
        main.write_text(main.read_text(encoding="utf-8").replace("  rfl\n", "  admit\n"), encoding="utf-8")
        r = self.build()
        self.assertEqual(r.returncode, 1)
        self.assertIn("`admit` in the code", r.stderr)
        self.assertFalse(self.out.exists() or self.zip.exists())

    @unittest.skipUnless(shutil.which("git"), "git not installed")
    def test_git_source_matches_directory(self):
        repo = self.tmp / "repo"
        shutil.copytree(FIXTURE, repo / "lean" / "cubic")
        env = {**os.environ, "GIT_AUTHOR_DATE": "2026-11-14T12:00:00Z", "GIT_COMMITTER_DATE": "2026-11-14T12:00:00Z"}
        git = ["git", "-C", str(repo), "-c", "user.name=test", "-c", "user.email=test@example.com",
               "-c", "commit.gpgsign=false"]
        for cmd in (["init", "-q"], ["add", "."], ["commit", "-q", "-m", "fixture"]):
            subprocess.run(git + cmd, check=True, env=env, capture_output=True)
        r = run("--repo", repo, "--out", self.out, "--zip", self.zip)
        self.assertEqual(r.returncode, 0, r.stderr)
        from_git = json.loads(self.out.read_text(encoding="utf-8"))
        self.assertRegex(from_git["source"]["commit"], r"^[0-9a-f]{40}$")
        self.assertEqual(from_git["source"]["date"], "2026-11-14")
        self.assertIn(f"/tree/{from_git['source']['commit']}/lean/cubic", from_git["links"]["tree"])
        r = run("--repo", repo, "--out", self.out, "--zip", self.zip, "--check")
        self.assertEqual(r.returncode, 0, r.stderr)
        # the same files read as a plain directory of that repo give the same certificate
        out2 = self.tmp / "dir.json"
        r = run("--lean", repo / "lean" / "cubic", "--out", out2, "--zip", self.tmp / "dir.zip")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(json.loads(out2.read_text(encoding="utf-8")), from_git)
        r = run("--repo", repo, "--ref", "no-such-ref", "--out", self.out, "--zip", self.zip)
        self.assertEqual(r.returncode, 1)
        self.assertIn("cannot resolve no-such-ref", r.stderr)


if __name__ == "__main__":
    unittest.main()
