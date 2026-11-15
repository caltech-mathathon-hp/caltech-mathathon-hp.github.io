#!/usr/bin/env python3
"""Check the exported sources, then freshly elaborate the frozen FinalAudit.

This script does not build imported modules. Run `lake build` first for a clean
package build; --lean instead permits an explicitly supplied local Lean/cache.
Only the Python standard library is needed for --sources-only.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

sys.dont_write_bytecode = True

PACKAGE = Path(__file__).resolve().parents[1]
MANIFEST = "checks/source-manifest.json"
TOOLCHAIN = "leanprover/lean4:v4.24.0"
MATHLIB_REV = "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
PROOF_ROOTS = [
    "ProteinFolding.Tetrahedral.NPCompleteness",
    "ProteinFolding.Tetrahedral.FinalAudit",
    "ProteinFolding.Tetrahedral.Audit",
]
EXPECTED_REPORTS = [
    "ProteinFolding.Tetrahedral.tetrahedral_hp_npComplete",
    "ProteinFolding.Tetrahedral.ReductionTM2.Canonical.reduction_correct",
    "ProteinFolding.Tetrahedral.ReductionTM2.Canonical.source_bulk_acyclic",
    "ProteinFolding.Tetrahedral.bulkFiniteGraph_acyclic",
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FROZEN_FILES = {
    "ProteinFolding/Common/Statement.lean": "9bc3081e5337c8165b4eb63c3549e5dc484dd947a966a1590180db26da364e1d",
    "ProteinFolding/Common/Encodings.lean": "0a6ce4711cfadbee0065eb11903c1d6f784d1ea8d5ddbea329c11583c7dfcf9c",
    "ProteinFolding/Common/Complexity.lean": "30c18a7b2f834a8461e7763f5f3e8777beb8e6d5072a71061f81e90cc10ab36e",
    "ProteinFolding/Tetrahedral/Statement.lean": "d1238634cdcc8477b1c1e81b27939205c28e46cf5388ec5b05c4cd5aafc2afd6",
    "ProteinFolding/Tetrahedral/Encodings.lean": "b09380f2f385cf54bae4e4aec6b02ae569f109e0f621fdf126d7b92888187f21",
    "ProteinFolding/Tetrahedral/MainTheorem.lean": "680f6d3fdc028a758d087d447b75dafabfae57ca7fd874dbb132d0f56f2b617b",
    "ProteinFolding/Tetrahedral/FinalAudit.lean": "86852032b7e6c0f40e272fd34847de9c0a85723acac67a22544fb69042638b12",
}
# The sole existing macro expands only to simp/decide; its entire original file
# must remain byte-exact. This exception does not permit any forbidden token.
EXISTING_MACRO = {
    "ProteinFolding/Tetrahedral/CertificatesTM2Checks.lean":
        "3a31789528dc45fed5ab20ac22aedbb814e1b94f7538b89c5d47f133c45b1955",
}
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|axioms|unsafe|extern|implemented_by|native_decide|"
    r"opaque|csimp|proof_wanted|sorryAx|mkSorry|mkAxiom|ofReduceBool|trustCompiler)\b"
    r"|\+native\b|\bLean\.ofReduce\w*|\bdebug\.skipKernelTC\b"
)
EXECUTABLE_EXTENSION = re.compile(
    r"\b(?:macro|macro_rules|syntax|elab|elab_rules|run_tac|run_elab|run_cmd|initialize|"
    r"builtin_initialize|addDecl|addAndCompile)\b|#eval\b|\bpartial\s+def\b"
)
MODULE_NAME = re.compile(r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*\Z", re.ASCII)


class VerificationError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result


def read_json(data):
    return json.loads(data.decode("utf-8-sig"), object_pairs_hook=unique_object)


def safe_file(root, relative):
    require(isinstance(relative, str), "Manifest path must be a string")
    path = PurePosixPath(relative)
    require(relative and "\\" not in relative and ":" not in relative
            and not path.is_absolute() and path.as_posix() == relative
            and all(part not in {".", ".."} for part in path.parts),
            "Unsafe or noncanonical manifest path: " + relative)
    result = root.joinpath(*path.parts)
    for parent in [result] + list(result.parents):
        if parent == root:
            break
        require(not parent.is_symlink(), "Symlink in manifest path: " + relative)
    require(result.is_file(), "Missing manifest file: " + relative)
    return result


def lean_code(text):
    """Mask comments/literal text, preserving offsets and interpolated code."""
    out = list(text)
    size = len(text)

    def mask(start, end):
        for k in range(start, end):
            if text[k] not in "\r\n":
                out[k] = " "

    def string(start, interpolated):
        mask(start, start + 1)
        i = start + 1
        while i < size:
            if text[i] == "\\":
                mask(i, min(size, i + 2))
                i += 2
            elif text[i] == '"':
                mask(i, i + 1)
                return i + 1
            elif interpolated and text.startswith("{{", i):
                mask(i, i + 2)
                i += 2
            elif interpolated and text[i] == "{":
                mask(i, i + 1)
                i = code(i + 1, True)
            else:
                mask(i, i + 1)
                i += 1
        raise VerificationError("Unterminated Lean string literal")

    def code(start, interpolation=False):
        i, braces = start, 0
        while i < size:
            if text.startswith("--", i):
                end = text.find("\n", i)
                end = size if end < 0 else end
                mask(i, end)
                i = end
            elif text.startswith("/-", i):
                begin, depth = i, 1
                i += 2
                while i < size and depth:
                    if text.startswith("/-", i):
                        depth += 1
                        i += 2
                    elif text.startswith("-/", i):
                        depth -= 1
                        i += 2
                    else:
                        i += 1
                require(depth == 0, "Unterminated Lean block comment")
                mask(begin, i)
            elif text[i] == '"':
                i = string(i, i >= 2 and text[i - 1] == "!"
                           and (text[i - 2].isalnum() or text[i - 2] == "_"))
            elif text[i] == "r" and (i == 0 or not text[i - 1].isalnum()):
                raw = re.match(r'r(#+)"', text[i:])
                if raw:
                    end = text.find('"' + raw[1], i + len(raw[0]))
                    require(end >= 0, "Unterminated Lean raw string")
                    end += 1 + len(raw[1])
                    mask(i, end)
                    i = end
                else:
                    i += 1
            elif interpolation and text[i] == "}" and braces == 0:
                mask(i, i + 1)
                return i + 1
            else:
                if interpolation and text[i] == "{":
                    braces += 1
                elif interpolation and text[i] == "}":
                    braces -= 1
                i += 1
        require(not interpolation, "Unterminated Lean string interpolation")
        return i

    code(0)
    return "".join(out)


def imports_of(code):
    imports = []
    for match in re.finditer(r"(?m)^[ \t]*import[ \t]+([^\r\n]+)", code):
        for name in match[1].split():
            require(MODULE_NAME.fullmatch(name), "Invalid import name: " + name)
            imports.append(name)
    return imports


def scan_lean(text, path, digest):
    code = lean_code(text)
    # `axioms` is a command argument only in the permitted #print reports.
    scanned = re.sub(r"(?m)^[ \t]*#print[ \t]+axioms\b", "#print", code)
    hit = FORBIDDEN.search(scanned)
    if hit is None:
        hit = EXECUTABLE_EXTENSION.search(scanned)
        if hit and hit[0] == "macro" and EXISTING_MACRO.get(path) == digest:
            hit = EXECUTABLE_EXTENSION.search(scanned, hit.end())
    if hit:
        line = scanned.count("\n", 0, hit.start()) + 1
        raise VerificationError("Forbidden executable Lean token in {}:{}: {}".format(path, line, hit[0]))
    for option in re.finditer(r"\bset_option\s+(\S+)\s+(\S+)", code):
        require(option[1] in {"maxRecDepth", "maxHeartbeats"},
                "Unexpected Lean option in {}: {}".format(path, option[1]))
    return imports_of(code)


def verify_sources(root):
    manifest_bytes = safe_file(root, MANIFEST).read_bytes()
    manifest = read_json(manifest_bytes)
    require(manifest.get("schemaVersion") == 1, "Unsupported manifest schema")
    require(manifest.get("originalSourcesUnmodified") is True, "Original-source flag changed")
    require(manifest.get("roots") == ["ProteinFolding"]
            and manifest.get("proofRoots") == PROOF_ROOTS
            and manifest.get("generatedSources") == ["ProteinFolding.lean"]
            and manifest.get("copiedModuleCount") == 1134
            and manifest.get("generatedModuleCount") == 1,
            "The exported module roots or counts changed")
    require(manifest.get("toolchain") == TOOLCHAIN
            and manifest.get("mathlib", {}).get("rev") == MATHLIB_REV,
            "Pinned Lean/mathlib versions changed")
    require(manifest.get("theorem") == EXPECTED_REPORTS[0]
            and manifest.get("target") == "ProteinFolding.Tetrahedral.HPStringFoldNPComplete",
            "The final theorem/target changed")
    frozen_rows = manifest.get("frozenFiles", [])
    frozen = {row["path"]: row["sha256"].lower() for row in frozen_rows}
    require(len(frozen_rows) == len(FROZEN_FILES) and frozen == FROZEN_FILES,
            "Frozen statement/foundation pins changed")
    modules, hashes, paths, config_paths = {}, {}, set(), set()
    for row in manifest["files"]:
        path = row["path"]
        require(path.casefold() not in paths, "Duplicate manifest path: " + path)
        paths.add(path.casefold())
        data = safe_file(root, path).read_bytes()
        digest = sha256(data)
        require(re.fullmatch(r"[0-9a-fA-F]{64}", row["sha256"]), "Invalid SHA256: " + path)
        require(digest == row["sha256"].lower(), "Source/config hash mismatch: " + path)
        if path in FROZEN_FILES:
            require(digest == FROZEN_FILES[path], "Frozen source changed: " + path)
        hashes[path] = digest
        if path.endswith(".lean"):
            name = row["module"]
            require(isinstance(name, str) and MODULE_NAME.fullmatch(name)
                    and name.replace(".", "/") + ".lean" == path,
                    "Module/path mismatch: " + path)
            require(name not in modules, "Duplicate module: " + name)
            imports = scan_lean(data.decode("utf-8-sig"), path, digest)
            require(imports == row["imports"], "Manifest import list differs from source: " + path)
            modules[name] = imports
        else:
            require("module" not in row and "imports" not in row, "Config marked as module: " + path)
            config_paths.add(path)
    require(len(modules) == 1135, "Expected exactly 1135 exported Lean modules")
    require(config_paths == {"lakefile.toml", "lake-manifest.json", "lean-toolchain"},
            "Expected exactly the three package configuration files")
    require(safe_file(root, "lean-toolchain").read_text(encoding="utf-8").strip() == TOOLCHAIN,
            "lean-toolchain differs from pinned version")
    lake = read_json(safe_file(root, "lake-manifest.json").read_bytes())
    mathlib = [p for p in lake["packages"] if p["name"] == "mathlib"]
    require(len(mathlib) == 1 and mathlib[0]["rev"] == MATHLIB_REV,
            "lake-manifest mathlib revision changed")
    actual = set()
    for directory, children, files in os.walk(root):
        children[:] = [c for c in children if c not in {".lake", ".git", "__pycache__"}]
        for filename in files:
            if filename.endswith(".lean"):
                actual.add((Path(directory) / filename).relative_to(root).as_posix())
    require(actual == {name.replace(".", "/") + ".lean" for name in modules},
            "Unlisted or missing package-local Lean sources")
    reached, pending, edges = set(), ["ProteinFolding"], 0
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        require(name in modules, "Missing project-local import: " + name)
        reached.add(name)
        for dependency in modules[name]:
            if dependency == "ProteinFolding" or dependency.startswith("ProteinFolding."):
                require(dependency in modules, "Missing project-local import: " + dependency)
                edges += 1
                pending.append(dependency)
    require(reached == set(modules), "Manifest contains modules outside the declared import closure")
    for row in manifest.get("provenance", {}).get("files", []):
        path = row["path"]
        digest = sha256(safe_file(root, path).read_bytes())
        require(digest == row["sha256"].lower(), "Historical provenance hash mismatch: " + path)
        hashes[path] = digest
    require(sha256(safe_file(root, MANIFEST).read_bytes()) == sha256(manifest_bytes),
            "Manifest changed during verification")
    return sha256(manifest_bytes), hashes, len(modules), edges


def verify_axiom_reports(output):
    require(not re.search(r"PANIC|declaration uses .sorry.|\berror:", output),
            "Lean reported an error, panic, or unfinished proof")
    reports = list(re.finditer(
        r"(?m)^'(?P<name>[^'\r\n]+)' (?:depends on axioms:\s*\[(?P<axioms>[^\]]*)\]"
        r"|does not depend on any axioms)[ \t]*\r?$", output))
    names = [report["name"] for report in reports]
    require(len(reports) == 4 and sorted(names) == sorted(EXPECTED_REPORTS),
            "Expected exactly one axiom report for each of the four frozen final declarations")
    all_axioms = set()
    for report in reports:
        axioms = {a.strip() for a in (report["axioms"] or "").split(",") if a.strip()}
        require(axioms <= ALLOWED_AXIOMS,
                "Unexpected axioms for {}: {}".format(report["name"], sorted(axioms - ALLOWED_AXIOMS)))
        all_axioms.update(axioms)
    return all_axioms


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--sources-only", action="store_true", help="check sources without Lean or Lake")
    mode.add_argument("--lean", metavar="EXECUTABLE", help="use supplied Lean and inherited LEAN_PATH; does not rebuild imports")
    args = parser.parse_args(argv)
    try:
        before = verify_sources(PACKAGE)
        print("PASS: source hashes, seven frozen pins, proof-token scan, and import closure ({} modules, {} project-local edges).".format(before[2], before[3]), flush=True)
        if args.sources_only:
            print("Sources only: no Lean elaboration or clean-build claim.")
            return 0
        command = ([args.lean] if args.lean else ["lake", "env", "lean"]) + [
            "--threads=1", "--tstack=65536", "--root=" + str(PACKAGE),
            "ProteinFolding/Tetrahedral/FinalAudit.lean",
        ]
        print("Checking fresh FinalAudit" + (" with supplied Lean/LEAN_PATH." if args.lean else " via lake env lean."), flush=True)
        result = subprocess.run(command, cwd=PACKAGE, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, encoding="utf-8", errors="replace", check=False)
        log = PACKAGE / "checks" / "local-final-axioms.txt"
        log.write_text(result.stdout, encoding="utf-8")
        print(result.stdout, end="" if result.stdout.endswith("\n") else "\n")
        require(result.returncode == 0, "Lean exited with status {}; see checks/local-final-axioms.txt".format(result.returncode))
        axioms = verify_axiom_reports(result.stdout)
        require(verify_sources(PACKAGE) == before, "Sources or manifest changed during Lean verification")
        print("PASS: fresh exact FinalAudit; four required reports; axioms: {}.".format(", ".join(sorted(axioms)) or "none"))
        print("Imported artifacts were not rebuilt by this verifier; this is not a clean-build claim.")
        return 0
    except (VerificationError, OSError, ValueError, KeyError, TypeError) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
