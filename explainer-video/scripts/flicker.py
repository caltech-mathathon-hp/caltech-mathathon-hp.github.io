"""
Finds flicker in frames rendered by scripts/flicker-frames.ts. Smooth motion and fades change a
pixel a little each frame; a glitch changes it a lot in one frame while everything around it is
still. Two kinds are reported:

  pop    something appears or vanishes from one frame to the next (b → c), with the frames
         before (a → b) and after (c → d) still around it
  blink  a frame b differs from both neighbours, which agree with each other

Prints the frames with the most such pixels and where they are, so they can be looked at.
Scene cuts are skipped.

    python3 -I scripts/flicker.py <framesDir> [--top 25] [--min 6] [--cuts 135,970,...]
"""
import os
import re
import sys

import numpy as np
from PIL import Image

args = sys.argv[1:]
src = args[0]


def opt(name, default):
    return args[args.index(name) + 1] if name in args else default


top = int(opt('--top', 25))
least = int(opt('--min', 6))
cuts = {int(x) for x in opt('--cuts', '').split(',') if x}

files = sorted(
    (int(re.search(r'(\d+)', f).group(1)), f) for f in os.listdir(src) if f.endswith('.png')
)
T = 60  # a change this large (0-255, largest channel) is a visible jump
Q = 10  # a change this small is still


def load(f):
    return np.asarray(Image.open(os.path.join(src, f)).convert('RGB'), dtype=np.int16)


def diff(x, y):
    return np.abs(x - y).max(axis=2)


def grow(m, r=3):
    """max over a (2r+1)² neighbourhood"""
    rows = m.copy()
    for d in range(1, r + 1):
        rows = np.maximum(rows, np.maximum(np.roll(m, d, axis=1), np.roll(m, -d, axis=1)))
    out = rows.copy()
    for d in range(1, r + 1):
        out = np.maximum(out, np.maximum(np.roll(rows, d, axis=0), np.roll(rows, -d, axis=0)))
    return out


def bbox(mask):
    ys, xs = np.nonzero(mask)
    return f'x {xs.min()}-{xs.max()} y {ys.min()}-{ys.max()}'


hits = []
win = []  # last four frames: (n, image)
for n, f in files:
    win.append((n, load(f)))
    if len(win) > 4:
        win.pop(0)
    if len(win) < 4:
        continue
    (na, a), (nb, b), (nc, c), (nd, d) = win
    if any(k in cuts for k in (nb, nc, nd)):
        continue
    dab, dbc, dcd, dac = diff(a, b), diff(b, c), diff(c, d), diff(a, c)
    still_before = grow(dab) < Q
    still_after = grow(dcd) < Q
    pop = (dbc > T) & still_before & still_after
    k = int(pop.sum())
    if k >= least:
        hits.append((k, nc, 'pop', bbox(pop)))
    blink = (dab > T) & (dbc > T) & (grow(dac) < Q)
    k = int(blink.sum())
    if k >= least:
        hits.append((k, nb, 'blink', bbox(blink)))

hits.sort(reverse=True)
print(f'{len(files)} frames, {len(hits)} with a pop or blink of {least}+ px')
for k, n, kind, where in hits[:top]:
    print(f'frame {n}: {kind} {k} px, {where}')

# --show sheet.png: for each hit, the frames before, at and after it, cropped round the region
show = opt('--show', '')
if show and hits:
    byn = dict(files)
    rows = []
    for k, n, kind, where in hits[:top]:
        x0, x1, y0, y1 = map(int, re.findall(r'\d+', where))
        cx, cy = (x0 + x1) // 2, (y0 + y1) // 2
        w, h = max(120, x1 - x0 + 40), max(90, y1 - y0 + 40)
        box = (cx - w // 2, cy - h // 2, cx + w // 2, cy + h // 2)
        tiles = [Image.open(os.path.join(src, byn[m])).convert('RGB').crop(box) for m in (n - 1, n, n + 1) if m in byn]
        s = min(3, 300 // max(w, h)) or 1
        rows.append((f'{n} {kind}', [t.resize((t.width * s, t.height * s), Image.NEAREST) for t in tiles]))
    from PIL import ImageDraw

    rw = max(sum(t.width + 6 for t in ts) for _, ts in rows) + 90
    rh = sum(max(t.height for t in ts) + 6 for _, ts in rows)
    sheet = Image.new('RGB', (rw, rh), 'white')
    dr = ImageDraw.Draw(sheet)
    y = 0
    for label, ts in rows:
        dr.text((4, y + 4), label, fill='black')
        x = 90
        for t in ts:
            sheet.paste(t, (x, y))
            x += t.width + 6
        y += max(t.height for t in ts) + 6
    sheet.save(show)
    print('sheet:', show)
