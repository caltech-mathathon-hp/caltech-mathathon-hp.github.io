import os
parts = []
parts.append("""# FCC HP folding: verification code, sixteenth pass (14 Nov 2026)

Scripts for Part III of the note (`claude/fcc-hp-hardness-attempt-part3.md`, Sections 26 to 32): the completeness of the reduction. They are self-contained: none of them imports a script of an earlier pass. `surface.py` recomputes the decoration of Lemma 47 and counts its defect units from the definitions of Theorem 5. Python 3 with numpy (only `fold.py` and `check.py` need numpy).

| Script | Statement | Run |
|---|---|---|
| `slicepath.py` | Lemma 49 (cut slice) | `python3 slicepath.py 3 44` |
| `surface.py` | decoration, pieces, rows, strips; the pairing search of Lemma 50 | `python3 surface.py 8 30` |
| `pairtest.py`, `strips.py` | Lemma 50 over all defects | `python3 pairtest.py 12 24 4 9`, `python3 pairtest.py 12 20 3 7`, `python3 pairtest.py 12 14 1 6`, `python3 strips.py` |
| `interior3.py`, `canon.py` | Lemma 51 (interior paths, run ends) | `python3 interior3.py 8 22`, `python3 canon.py 12 24` |
| `octa.py` | Proposition 52 (one octahedron) | `python3 octa.py 18 24 0 3`, `python3 octa.py regime B t` |
| `fold.py`, `check.py`, `controls.py` | Lemma 53 (routing), Theorem 54 (whole fold), independent checker | `python3 fold.py n8 n8x n8m3 n10 n10x n12 n14`, `python3 controls.py` |
""")
for f in ['slicepath.py', 'surface.py', 'pairtest.py', 'strips.py', 'interior3.py', 'canon.py', 'octa.py', 'fold.py', 'check.py', 'controls.py']:
    parts.append(f"## `{f}`\n\n```python\n{open(f).read().rstrip()}\n```\n")
outs = [('slicepath.txt', '`python3 slicepath.py 3 44`'), ('surface.txt', '`python3 surface.py 8 30`'),
        ('pairtest.txt', '`python3 pairtest.py 12 24 4 9` (the range of Lemma 50)'), ('pairtest_wide.txt', '`python3 pairtest.py 12 20 3 7` (a wider range)'),
        ('pairtest_outside.txt', '`python3 pairtest.py 12 14 1 6` (outside the range of the lemma: failures are expected)'), ('strips.txt', '`python3 strips.py`'),
        ('interior3.txt', '`python3 interior3.py 8 22`'), ('canon.txt', '`python3 canon.py 12 24`'), ('octa_all.txt', '`python3 octa.py 18 24 0 3`'),
        ('octa_regime.txt', '`python3 octa.py regime B t` for (B, t) = (7, 4), (10, 2), (11, 2), (13, 2), (17, 2)'), ('octa_regime2.txt', '`python3 octa.py regime 3 4` and `python3 octa.py regime 10 4`'),
        ('fold.txt', '`python3 fold.py n8 n8x n8m3 n10 n10x n12 n14`'), ('controls.txt', '`python3 controls.py`')]
for f, title in outs:
    parts.append(f"## Output of {title}\n\n```\n{open('out/' + f).read().rstrip()}\n```\n")
open('code14.md', 'w').write("\n".join(parts))
print(len(open('code14.md').read()), 'bytes', len(open('code14.md').read().splitlines()), 'lines')
