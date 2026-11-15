parts = ["""# FCC HP folding: verification code, part 19 (twenty-second pass, 15 Nov 2026)

Scripts for Section 45 of the note (`claude/fcc-hp-hardness-attempt-part3.md`): the linear inequality (L_n), which implies soundness (Proposition 62); silhouette runs, the pointwise inequality of Lemma 63 and the identity of Proposition 64; the counts (M_n) and (K); statements that turned out false; and the smallest violators of G_chi. They import `gmin.py`, `psi.py` (part 16), `tops.py` (part 17) and `euler.py` (part 18). Apart from `chordB.py` (the enumeration behind Lemma 63) and `algebra62.py` (the arithmetic of Proposition 62), nothing here is a proof.

| Script | What it does | Run |
|---|---|---|
| `lin.py` | Lam_n, its least value over n, the discriminant D; octahedra, unions, bodies at one site, bridged pairs | `python3 lin.py families`, `near r`, `bridge r` |
| `lintest.py` | Lam_n and the largest n with M_n < 0 on special bodies, roofs, pairs joined by two sites, bodies at two sites | `python3 lintest.py special`, `roof N n`, `bridge2 r`, `near2 r` |
| `linsearch.py` | annealing against (L_n) | `python3 linsearch.py seed steps T0 kind` |
| `dscan.py` | the discriminant form on 1,790 bodies | `python3 dscan.py` |
| `algebra62.py` | the identities of Proposition 62 and the two other forms of M_n | `python3 algebra62.py` |
| `chords.py` | chords and silhouette runs; three statements of which (A) is false | `python3 chords.py` |
| `chordB.py` | Lemma 63: 12 e - 4 deg <= o for all 4,096 neighbourhoods | `python3 chordB.py` |
| `chordM.py` | M_n and the identity Lam_n = M_n + 3B + 3D_n+ | `python3 chordM.py families` |
| `chordM2.py` | the largest n with M_n < 0, by family | `python3 chordM2.py families`, `unions a b`, `near r`, `bridge r` |
| `steps.py` | (M_n) for O_9 with small translates | `python3 steps.py 9` |
| `slopes.py` | the count of slopes (false, Section 45.6) | `python3 slopes.py families` |
| `msearch.py` | (K) on unions and bodies at one site; annealing against (M_n), n >= 6 | `python3 msearch.py K`, `python3 msearch.py anneal seed steps T0` |
| `minviol.py` | smallest violators of G_chi | `python3 minviol.py 1 0.5 3000 6` |
"""]
for f in ['lin.py', 'lintest.py', 'linsearch.py', 'dscan.py', 'algebra62.py', 'chords.py', 'chordB.py', 'chordM.py', 'chordM2.py', 'steps.py', 'slopes.py', 'msearch.py', 'minviol.py']:
    parts.append(f"## `{f}`\n\n```python\n{open(f).read().rstrip()}\n```\n")
def cat(files): return "\n".join(open('out/' + f).read().rstrip() for f in files)
def minviol():
    L = open('out/minviol.txt').read().rstrip().splitlines(); return "\n".join(l if not l.startswith('[') else l[:400] + ' ... (133 sites)' for l in L)
outs = [('`python3 lin.py families`', cat(['lin_families.txt'])), ('`python3 lin.py near r`, r = 5, 6, 7, 8', cat(['lin_near.txt'])), ('`python3 lin.py bridge 5` and `bridge 6`', cat(['lin_bridge.txt'])),
        ('`python3 lintest.py special`', cat(['lintest_special.txt'])),
        ('`python3 lintest.py roof N n` for (N, n) = (6, 5), (6, 6), (7, 5), (7, 6), (8, 4); `bridge2 5`; `near2 5`', cat(['lintest_roof_6_5.out', 'lintest_roof_6_6.out', 'lintest_roof_7_5.out', 'lintest_roof_7_6.out', 'lintest_roof_8_4.out', 'lintest_bridge2_5.out', 'lintest_near2_5.out'])),
        ('`python3 linsearch.py`: `1 4000 0.3 octa`, `2 3000 0.2 twin`, `3 3000 0.2 bridge`, `4 2500 0.3 unions 5 12`, `5 2500 0.3 unions 6 10`, `6 4000 0.5 blobs 6`, `7 4000 0.05 octa`', cat([f'linsearch_{i}.out' for i in range(1, 8)])),
        ('`python3 dscan.py`', cat(['dscan.txt'])), ('`python3 algebra62.py`', cat(['algebra62.txt'])), ('`python3 chords.py`', cat(['chords.txt'])), ('`python3 chordB.py`', cat(['chordB.txt'])),
        ('`python3 chordM.py families`', cat(['chordM_families.txt'])),
        ('`python3 chordM2.py`: `families`, `unions 7 7`, `unions 5 8`, `near 5`, `near 7`, `bridge 5`, then `unions 9 9`, `unions 6 9`, `near 6`, `near 8`', cat(['chordM2.txt', 'chordM2_rest.out'])),
        ('`python3 steps.py 9`', cat(['steps.txt'])), ('`python3 slopes.py families`', cat(['slopes.txt'])),
        ('`python3 msearch.py K`', cat(['msearch_K.out'])), ('`python3 msearch.py anneal 1 1500 0.2` (seed 2 gives the same lines)', cat(['msearch_a1.out'])),
        ('`python3 minviol.py 1 0.5 3000 6` (site list cut)', minviol())]
for title, text in outs:
    parts.append(f"## Output of {title}\n\n```\n{text}\n```\n")
open('code19.md', 'w').write("\n".join(parts))
t = open('code19.md').read(); print(len(t), 'bytes', len(t.splitlines()), 'lines')
