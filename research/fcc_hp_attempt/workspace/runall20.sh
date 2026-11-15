#!/bin/bash
cd /home/claude/fcc
(python3 islands.py 9 > out/islands_9.txt 2>&1; python3 islands2.py 9 > out/islands2_9.txt 2>&1) &
(python3 islands2.py 13 > out/islands2_13.txt 2>&1) &
(for a in "9 3 1 1" "13 4 0 4" "17 6 1 4" "21 9 1 5"; do python3 chordM3.py island $a; done > out/chordM3_island.txt 2>&1) &
(python3 blocked.py > out/blocked.txt 2>&1; python3 sharp.py 2>&1 | sed 's/Fraction(\([-0-9]*\), 1)/\1/g; s/Fraction(\([-0-9]*\), \([0-9]*\))/\1\/\2/g' > out/sharp.txt; python3 check67.py > out/check67.txt 2>&1; python3 stacks.py 9 > out/stacks_9.txt 2>&1) &
(python3 m0.py named > out/m0.txt 2>&1; for a in "9 3 1 2" "13 6 2 2" "13 4 0 4" "17 6 1 4" "21 9 1 5"; do python3 m0.py island $a; done >> out/m0.txt 2>&1; python3 m0.py islands 9 >> out/m0.txt 2>&1) &
wait
echo done > out/runall20.done
