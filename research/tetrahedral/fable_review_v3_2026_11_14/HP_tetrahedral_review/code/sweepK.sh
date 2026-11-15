#!/bin/bash
# near-field checks for K = 1..6 at larger m (all slot patterns near V_a and V_c, generic slots, generic separators)
for m in 80 82; do for K in 1 2 3 4 5 6; do
  P="["; for k in $(seq 1 $K); do P="$P[2,2],"; done; P="${P%,}]"
  out=$(NEARONLY=1 python3 build3.py $m 4 "$P" 20 nochain 0 natural sweepK 2>&1)
  echo "m=$m K=$K: $(echo "$out" | grep -E 'NEAR FIELD OK|rror|ssert' | tail -1) | borrowed: $(echo "$out" | grep -o 'borrowed columns: [0-9]*') | slacks: $(echo "$out" | grep -o 'slack [0-9]*' | awk '{printf "%s ",$2}')"
done; done
