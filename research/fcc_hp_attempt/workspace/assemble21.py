"""assembles code21.md from the scripts and outputs of the twenty-fourth pass"""
import os
head = """# FCC HP folding: verification code, part 21 (twenty-fourth pass, 15 Nov 2026)

Scripts for Section 47 of the note (`claude/fcc-hp-hardness-attempt-part3.md`): shape-regular sites and fans (Lemma 68); the count (A) of active runs of one length against units, and the inequality of Theorem 69; roots and charges (Lemmas 70, 71); tips (Proposition 72); three counts that are false (fans, sources of runs, end-sources). They import `gmin.py`, `psi.py` (part 16), `chords.py` (part 19) and `islands.py`, `chordM3.py` (part 20). `acount.py local` and `structure.py tips` are the enumerations behind Lemma 68 and Proposition 72, and `acount.py` checks the inequality of Theorem 69(a) on bodies; the scans are evidence for (A), not a proof.

| Script | What it does | Run |
|---|---|---|
| `fans.py` | shape-regular sites, fans, active runs, the kind of root of each fan; the number of fans against units (false) | `python3 fans.py named`, `unions a b`, `near r`, `near2 r`, `islands r`, `bridge r`, `roof N n` |
| `acount.py` | a_L, the count (A), the inequality of Theorem 69(a) against M'_n; `local`: the enumerations of Lemma 68 and the constant 99 | `python3 acount.py local`, `named`, `special`, `unions a b`, `near r`, `near2 r`, `islands r`, `pits r`, `bridge r`, `roof N n` |
| `structure.py` | Lemma 68(d), Lemma 70, Lemma 71 and the parent of a run with regular surroundings, on bodies; `tips`: Lemma 68(d) and Proposition 72 by enumeration | `python3 structure.py tips`, `named`, `unions a b`, `near r`, `islands r`, `bridge r`, `roof N n` |
| `charges.py` | the nearest-root charge site by site | `python3 charges.py` |
| `asearch.py` | annealing against (A) | `python3 asearch.py seed steps T0 kind` |
| `sources.py` | sources of runs by matching on neighbouring lines, with the telescoping bound; the count of sources against units (false) | `python3 sources.py named` |
| `endsrc.py` | end-sources along ridge segments, with the telescoping bound; the count against units (false) | `python3 endsrc.py named` |
"""
def code(name):
    return f"\n## `{name}`\n\n```python\n" + open(name).read().rstrip() + "\n```\n"
def outp(title, files):
    body = "".join(open(os.path.join('out', f)).read() for f in files).rstrip()
    return f"\n## Output of {title}\n\n```\n" + body + "\n```\n"
parts = [head]
for s in ("fans.py", "acount.py", "structure.py", "charges.py", "asearch.py", "sources.py", "endsrc.py"): parts.append(code(s))
parts.append(outp("`python3 acount.py local`", ["acount_local.txt"]))
parts.append(outp("`python3 structure.py tips`", ["structure_tips.txt"]))
parts.append(outp("`python3 acount.py named` and `special`", ["acount_named.txt", "acount_special.txt"]))
parts.append(outp("`python3 acount.py`: `unions 7 7`, `unions 9 9`, `unions 5 8`, `unions 6 9`, `near 5` to `near 8`, `islands 9`, `islands 13`, `pits 9`, `pits 13`, `bridge 5`, `bridge 6`, `roof 6 5`, `roof 6 6`, `roof 7 5`, `roof 7 6`, `roof 8 4`; then `near2 5`", ["acount_scans.txt", "acount_near2_5.txt"]))
parts.append(outp("`python3 structure.py`: `named`, `unions 7 7`, `unions 5 8`, `near 6`, `islands 9`, `bridge 5`, `roof 6 5`", ["structure.txt"]))
parts.append(outp("`python3 charges.py`", ["charges.txt"]))
parts.append(outp("`python3 asearch.py`: `1 1200 3 octa`, `2 1200 3 near`, `3 900 3 islands`, `4 900 4 unions`, `5 1000 3 steps`, `6 1200 8 octa`, `7 900 6 islands`", [f"asearch_{i}.out" for i in range(1, 8)]))
parts.append(outp("`python3 fans.py named`", ["fans_named.txt"]))
parts.append(outp("`python3 fans.py`: `unions 7 7`, `unions 5 8`, `near 5`, `near 6`, `near 7`, `islands 9`, `bridge 5`, `roof 6 5`", ["fans_a.out"]))
parts.append(outp("`python3 sources.py named`", ["sources_named.txt"]))
parts.append(outp("`python3 endsrc.py named`", ["endsrc_named.txt"]))
open('code21.md', 'w').write("".join(parts))
t = open('code21.md').read(); print(len(t.encode()), "bytes", t.count("\n"), "lines")
