#!/bin/bash
# Lemma N: representative layouts of the family F, UNCHAINED bulk assembly (every bulk path is its own H-run), explicit tethers, NCHECK assertions
for m in 80 82; do
  for K in 1 2 3 4 5 6 7 8; do
    P="["; for k in $(seq 1 $K); do P="$P[4],"; done; P="${P%,}]"
    out=$(NCHECK=1 NEARONLY=1 python3 build3.py $m 4 "$P" 14 nochain 0 natural n${m}_$K 2>&1)
    echo "m=$m K=$K: $(echo "$out" | grep -E 'NEAR FIELD OK|rror|assert' | tail -1) | $(echo "$out" | grep -E 'NCHECK Appendix' | sed 's/NCHECK //')"
  done
  out=$(NCHECK=1 NEARONLY=1 python3 build3.py $m 8 "[[4,4],[4,4]]" 14 nochain 0 natural n${m}_cut 2>&1)
  echo "m=$m cut-test (two bins of two items of 4 dimers): $(echo "$out" | grep -E 'NEAR FIELD OK|rror|assert' | tail -1)"
done
# one layout with K > 8 (m >= 5K+40, J = 14, R = 15)
out=$(NCHECK=1 NEARONLY=1 python3 build3.py 92 4 "[[4],[4],[4],[4],[4],[4],[4],[4],[4],[4]]" 14 nochain 0 natural n92_10 2>&1)
echo "m=92 K=10: $(echo "$out" | grep -E 'NEAR FIELD OK|rror|assert' | tail -1) | $(echo "$out" | grep -E 'NCHECK Appendix' | sed 's/NCHECK //') | $(echo "$out" | grep -E 'linker caps')"
