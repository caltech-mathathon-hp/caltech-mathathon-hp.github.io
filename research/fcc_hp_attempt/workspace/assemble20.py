import glob
parts = ["""# FCC HP folding: verification code, part 20 (twenty-third pass, 15 Nov 2026)

Scripts for Section 46 of the note (`claude/fcc-hp-hardness-attempt-part3.md`): islands on a face of an octahedron, which refute "(M_n) from n = 6 on" of Section 45; the repaired decomposition with half-open chords (Proposition 65); the local potential (Lemma 66); the increments of M'_n and the conjecture (I_n) (Proposition 67); statements that turned out false. They import `gmin.py`, `psi.py` (part 16) and `lin.py`, `chords.py`, `chordM.py` (part 19). `blocked.py` is the enumeration behind Lemma 66(b) and `check67.py` checks the identities on bodies; nothing else here is a proof.

| Script | What it does | Run |
|---|---|---|
| `islands.py`, `islands2.py` | one-layer triangular islands on a face of O_r: U*, Lam_n, the n with M_n < 0, the slack of (K) | `python3 islands.py 9`, `python3 islands2.py 13` |
| `chordM3.py` | M'_n (half-open chords counted), the identity of Proposition 65, the n with M_n < 0 and with M'_n < 0 | `python3 chordM3.py island r k a b`, `families`, `unions a b`, `near r`, `islands r` |
| `ends.py` | open ends: (K'), the increments (I_n), M'_3, the least M'_n for n >= 4, by family | `python3 ends.py families`, `special`, `unions a b`, `near r`, `near2 r`, `islands r`, `bridge r`, `roof N n` |
| `stacks.py` | islands on all eight faces, stacked islands | `python3 stacks.py 9` |
| `blocked.py` | Lemma 66(b): tau and the bound for blocked ends over the 4,096 neighbourhoods | `python3 blocked.py` |
| `sharp.py` | the potential pi, Pi, and the runs-only inequality (false) | `python3 sharp.py` |
| `m0.py` | the runs-only form M0_n with the potential | `python3 m0.py named`, `island r k a b`, `islands r` |
| `check67.py` | Lemma 66(a), formula (3), both forms of the increment | `python3 check67.py` |
| `corner.py` | units at a corner site against the number of corners, over all neighbourhoods | `python3 corner.py` |
| `isearch.py` | annealing against (I_n) and (M'_n) | `python3 isearch.py seed steps T0 kind` |
"""]
for f in ['islands.py', 'islands2.py', 'chordM3.py', 'ends.py', 'stacks.py', 'blocked.py', 'sharp.py', 'm0.py', 'check67.py', 'corner.py', 'isearch.py']:
    parts.append(f"## `{f}`\n\n```python\n{open(f).read().rstrip()}\n```\n")
def cat(files): return "\n".join(open('out/' + f).read().rstrip() for f in files)
ends_files = ['ends_families.out', 'ends_special.out'] + [f"ends_{x}.out" for x in ("unions_7_7", "unions_9_9", "unions_5_8", "unions_6_9", "near_5", "near_6", "near_7", "near_8", "near2_5", "islands_9", "islands_13", "bridge_5", "bridge_6", "roof_6_5", "roof_6_6", "roof_7_5", "roof_7_6", "roof_8_4")]
outs = [('`python3 islands.py 9`', cat(['islands_9.txt'])), ('`python3 islands2.py 9` and `python3 islands2.py 13`', cat(['islands2_9.txt', 'islands2_13.txt'])),
        ('`python3 chordM3.py island` for (r, k, a, b) = (9, 3, 1, 1), (13, 4, 0, 4), (17, 6, 1, 4), (21, 9, 1, 5)', cat(['chordM3_island.txt'])),
        ('`python3 chordM3.py`: `families`, `unions 7 7`, `unions 5 8`, `near 5`, `near 6`; `unions 9 9`, `unions 6 9`; `islands 9`, `near 7`; `islands 13`', cat(['chordM3_a.out', 'chordM3_b.out', 'chordM3_c.out', 'chordM3_d.out'])),
        ('`python3 ends.py`: `families`, `special`, then the scans `unions`, `near`, `near2 5`, `islands`, `bridge`, `roof`', cat(ends_files)),
        ('`python3 stacks.py 9`', cat(['stacks_9.txt'])), ('`python3 blocked.py`', cat(['blocked.txt'])), ('`python3 sharp.py`', cat(['sharp.txt'])),
        ('`python3 m0.py named`, `island` for five islands, `islands 9`', cat(['m0.txt'])), ('`python3 check67.py`', cat(['check67.txt'])), ('`python3 corner.py`', cat(['corner.txt'])),
        ('`python3 isearch.py`: `1 1500 0.05 octa`, `2 1500 0.05 near`, `3 1200 0.05 islands`, `4 1200 0.1 unions`, `5 1500 0.05 bridge`, `6 2500 0.3 blobs`, `7 1500 0.2 near`, `8 1200 0.15 islands` (stopped; lines written until then, run 6 had written none)', cat([f'isearch_{i}.out' for i in (1, 2, 3, 4, 5, 7, 8)]))]
for title, text in outs:
    parts.append(f"## Output of {title}\n\n```\n{text}\n```\n")
open('code20.md', 'w').write("\n".join(parts))
t = open('code20.md').read(); print(len(t), 'bytes', len(t.splitlines()), 'lines')
