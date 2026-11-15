"""Controls for check.py.  The fold of the instance n8 is given to the checker unchanged, and then in three altered
forms that it must reject: (a) one residue moved by (2, 0, 0); (b) the same coordinates read with the word shifted by
one residue; (c) the last P before the first H-run declared an H."""
import numpy as np, fold, check
n, items, B, triples = 8, [24, 24, 25, 23, 25, 25], 73, [(0, 1, 2), (3, 4, 5)]
xyz, word, par = fold.build(n, items, B, triples)
print("unchanged:        ", check.report(xyz, word, 2)[-60:])
bad = xyz.copy(); bad[123456] += (2, 0, 0)
print("one residue moved:", check.report(bad, word, 2)[:60])
print("word shifted:     ", check.report(xyz, word[1:] + 'P', 2)[-60:])
i = word.index('H'); w2 = word[:i - 1] + 'H' + word[i:]
print("one P turned to H:", check.report(xyz, w2, 2)[-60:])
