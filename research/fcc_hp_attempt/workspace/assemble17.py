parts = ["""# FCC HP folding: verification code, part 17 (twentieth pass, 14 Nov 2026)

Scripts for Section 43 of the note (`claude/fcc-hp-hardness-attempt-part3.md`): the formula U* = W + 3 def1 + 3 def2, local tops, splits and merges of slice pieces, Conjecture G (U* >= 6T - 18), and the cheapest connection between two octahedra. They import `gmin.py` and `psi.py` of part 16 (`claude/fcc-verification-code-16.md`). Python 3 with numpy and scipy. Nothing here is a proof.

| Script | What it does | Run |
|---|---|---|
| `wdef.py` | W, def1, def2 and the identity of Lemma 56(a) on examples | `python3 wdef.py` |
| `tops.py` | local tops in the six directions; U* against 3T, 4T - 6, 6T - 18 on examples | `python3 tops.py` |
| `morse.py` | piece graphs: T, sigma, cycle rank; checks Lemma 57 on every body it is given | `python3 morse.py` |
| `bridge.py` | two octahedra that are not adjacent, joined by one or two sites (Section 43.5) | `python3 bridge.py n` |
| `gcheck.py` | Conjecture G on the families of Section 42 | `python3 gcheck.py` |
| `gprime.py` | Conjecture G and the false extension G' on all small connected sets; search against G' | `python3 gprime.py small 7`, `python3 gprime.py search 1 2500` |
| `gsearch.py` | search against Conjecture G | `python3 gsearch.py seed steps [temperature]` |

`gsearch.py` was run with seeds 1 and 2 (3000 steps, temperature 3) before the five bodies with equality or near equality were added to its starts (42 starts each), and with seeds 3 and 4 (4000 steps, temperatures 1 and 0.4) after (47 starts each).
"""]
for f in ['wdef.py', 'tops.py', 'morse.py', 'bridge.py', 'gcheck.py', 'gprime.py', 'gsearch.py']:
    parts.append(f"## `{f}`\n\n```python\n{open(f).read().rstrip()}\n```\n")
def lowest(f, k=6):
    L = open('out/' + f).read().rstrip().splitlines(); body = [l for l in L if 'least' in l and not l.startswith('seed')]
    key = lambda l: int(l.split('least slack met ')[1].split()[0]) if 'least slack met' in l else int(l.split('least met ')[1].split()[0])
    return "\n".join(sorted(body, key=key)[:k] + ['...'] + [l for l in L if l.startswith('seed')])
outs = [('wdef.txt', '`python3 wdef.py`', None), ('tops.txt', '`python3 tops.py`', None), ('morse.txt', '`python3 morse.py`', None),
        ('bridge.txt', '`python3 bridge.py 5` and `python3 bridge.py 6`', None), ('gcheck.txt', '`python3 gcheck.py`', None),
        ('gprime_small7.txt', '`python3 gprime.py small 7`', None),
        ('gprime_search.txt', "`python3 gprime.py search 1 2500` (abridged: the six lowest of 27 starts and the summary; G' is violated)", 6),
        ('gsearch_1.txt', '`python3 gsearch.py 1 3000` (abridged: the six lowest of 42 starts and the summary)', 6),
        ('gsearch_2.txt', '`python3 gsearch.py 2 3000` (abridged)', 6), ('gsearch_3.txt', '`python3 gsearch.py 3 4000 1.0` (abridged: the six lowest of 47 starts)', 6),
        ('gsearch_4.txt', '`python3 gsearch.py 4 4000 0.4` (abridged)', 6)]
for f, title, k in outs:
    text = open('out/' + f).read().rstrip() if k is None else lowest(f, k)
    parts.append(f"## Output of {title}\n\n```\n{text}\n```\n")
open('code17.md', 'w').write("\n".join(parts))
t = open('code17.md').read(); print(len(t), 'bytes', len(t.splitlines()), 'lines')
