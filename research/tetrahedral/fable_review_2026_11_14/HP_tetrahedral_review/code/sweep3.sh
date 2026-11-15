#!/bin/bash
# sweep of the final builder over sizes and numbers of bins; each run builds a complete fold and checks optimality
ok=0; fail=0
for m in $(seq 24 46); do
  for K in 1 2 3; do
    need=$((8+K*6+6))
    if [ $((m-2)) -lt $need ]; then continue; fi
    P="["; for k in $(seq 1 $K); do P="$P[2,2],"; done; P="${P%,}]"
    out=$(python3 build3.py $m 4 "$P" 8 chain 0 natural sweep 2>&1)
    if echo "$out" | grep -q "OPTIMAL: True"; then ok=$((ok+1)); else fail=$((fail+1)); echo "FAIL m=$m K=$K: $(echo "$out" | tail -1)"; fi
  done
done
echo "sweep: $ok complete optimal folds built, $fail failures"
rm -f ../sweep_fold_*.txt
