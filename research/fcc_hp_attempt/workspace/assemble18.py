parts = ["""# FCC HP folding: verification code, part 18 (twenty-first pass, 15 Nov 2026)

Scripts for Section 44 of the note (`claude/fcc-hp-hardness-attempt-part3.md`): the Euler characteristic of the boundary surface, the statement G_chi (U* >= 6T - 9 chi), which is false, the change of W when one site is added, and W split by axis. They import `gmin.py`, `psi.py` (part 16) and `wdef.py`, `tops.py`, `morse.py` (part 17). Nothing here is a proof.

| Script | What it does | Run |
|---|---|---|
| `euler.py` | chi of the boundary of the union of Voronoi cells, with or without pinch points resolved | `python3 euler.py` |
| `gchi.py` | G_chi on all small connected sets, and a search against it; the argument `res` resolves pinch points | `python3 gchi.py small 7 res`, `python3 gchi.py search 1 2500 3.0 res` |
| `addsite.py` | the formula for W(S + g) - W(S) | `python3 addsite.py` |
| `waxis.py` | W by axis against tops by axis | `python3 waxis.py` |
"""]
for f in ['euler.py', 'gchi.py', 'addsite.py', 'waxis.py']:
    parts.append(f"## `{f}`\n\n```python\n{open(f).read().rstrip()}\n```\n")
def lowest(f, k=6):
    L = open('out/' + f).read().rstrip().splitlines(); body = [l for l in L if 'least met' in l]
    key = lambda l: int(l.split('least met ')[1].split()[0])
    return "\n".join(sorted(body, key=key)[:k] + ['...'] + [l for l in L if l.startswith('seed')])
outs = [('euler.txt', '`python3 euler.py` (the last column uses chi without resolving pinch points)', None), ('gchi_res_small7.txt', '`python3 gchi.py small 7 res`', None),
        ('gchi_res_search_1.txt', '`python3 gchi.py search 1 2500 3.0 res` (abridged: the six lowest of 26 starts and the summary; G_chi is violated)', 6),
        ('gchi_search_1.txt', '`python3 gchi.py search 1 2500 3.0` (pinch points not resolved; abridged)', 4),
        ('addsite.txt', '`python3 addsite.py`', None), ('waxis.txt', '`python3 waxis.py`', None)]
for f, title, k in outs:
    text = open('out/' + f).read().rstrip() if k is None else lowest(f, k)
    parts.append(f"## Output of {title}\n\n```\n{text}\n```\n")
open('code18.md', 'w').write("\n".join(parts))
t = open('code18.md').read(); print(len(t), 'bytes', len(t.splitlines()), 'lines')
