parts = ["""# FCC HP folding: verification code, part 16 (nineteenth pass, 14 Nov 2026)

Scripts for Section 42 of the note (`claude/fcc-hp-hardness-attempt-part3.md`): a search for a counterexample to Conjecture R. Nothing here proves anything; the scripts compute the least number of defect units of finite bodies exactly and compare it with what the bodies hold. They are self-contained (none imports a script of an earlier pass). Python 3 with numpy and scipy.

| Script | What it does | Run |
|---|---|---|
| `gmin.py` | U* and n2* of a finite set by two bipartite matchings; reproduces the values of Section 8 | `python3 gmin.py` |
| `scan2.py` | all connected unions of two regular octahedra: U*, n2* against the capacity of one octahedron | `python3 scan2.py a b` |
| `psi.py` | X3, K, Psi; the same unions; local search on Psi over the whole boundary | `python3 psi.py scan a b`, `python3 psi.py search a b steps [f]` |
| `lgeo.py`, `lscan.py` | long geometric chains; on every union | `python3 lgeo.py`, `python3 lscan.py` |
| `price.py` | units paid per pyramid beyond six | `python3 price.py` |
| `near.py` | bodies at one or two sites from a regular octahedron | `python3 near.py n [2]` |
| `junction.py` | local search around the contact of two lumps, with a guard on what the body holds | `python3 junction.py a b r [steps]` |
| `roof.py` | a roof over two legs (three octahedra) | `python3 roof.py N n J` |

The searches use fixed random seeds. The first version of `junction.py`, without the guard, is described in Section 42; its two low results (U* = 28 and 30) are bodies fused into one lump.
"""]
for f in ['gmin.py', 'scan2.py', 'psi.py', 'lgeo.py', 'lscan.py', 'price.py', 'near.py', 'junction.py', 'roof.py']:
    parts.append(f"## `{f}`\n\n```python\n{open(f).read().rstrip()}\n```\n")
outs = [('gmin.txt', '`python3 gmin.py`'), ('scan2_7_7.txt', '`python3 scan2.py 7 7`'), ('scan2_9_9.txt', '`python3 scan2.py 9 9`'), ('scan2_5_8.txt', '`python3 scan2.py 5 8`'),
        ('scan2_6_9.txt', '`python3 scan2.py 6 9`'), ('psi_scan_7_7.txt', '`python3 psi.py scan 7 7`'), ('psi_scan_9_9.txt', '`python3 psi.py scan 9 9`'),
        ('psi_scan_5_8.txt', '`python3 psi.py scan 5 8`'), ('psi_scan_6_9.txt', '`python3 psi.py scan 6 9`'), ('lgeo.txt', '`python3 lgeo.py`'), ('lscan.txt', '`python3 lscan.py`'),
        ('price.txt', '`python3 price.py`'), ('near.txt', '`python3 near.py n` for n = 5, 6, 7, 8 and `python3 near.py 5 2` (last line)'),
        ('psi_search_5_5.txt', '`python3 psi.py search 5 5 1500`'), ('psi_search_6_6.txt', '`python3 psi.py search 6 6 800 0.5`'),
        ('junction_6_6_r2.txt', '`python3 junction.py 6 6 2`'), ('junction_6_6_r3.txt', '`python3 junction.py 6 6 3 1500`'), ('junction_7_7.txt', '`python3 junction.py 7 7 2 1000`'),
        ('roof_all.txt', '`python3 roof.py N n J` for (N, n, J) = (6, 5, 2), (7, 5, 2), (7, 6, 3), (6, 6, 2), (8, 4, 2)')]
def trimmed(f):
    """search logs: the header line if there is one, the five lowest ends, and the summary line"""
    L = open('out/' + f).read().rstrip().splitlines()
    if not (f.startswith('psi_search') or f.startswith('junction')): return "\n".join(L), ''
    key = (lambda l: float(l.split('after search ')[1].split()[0])) if f.startswith('psi') else (lambda l: float(l.split('after search U* ')[1].split(',')[0]))
    body = [l for l in L if 'after search' in l]; head = [l for l in L[:1] if 'after search' not in l]
    return "\n".join(head + sorted(body, key=key)[:5] + ['...'] + L[-1:]), f' (abridged: the five lowest of {len(body)} starts and the summary line)'
for f, title in outs:
    text, note = trimmed(f)
    parts.append(f"## Output of {title}{note}\n\n```\n{text}\n```\n")
open('code15.md', 'w').write("\n".join(parts))
t = open('code15.md').read(); print(len(t), 'bytes', len(t.splitlines()), 'lines')
