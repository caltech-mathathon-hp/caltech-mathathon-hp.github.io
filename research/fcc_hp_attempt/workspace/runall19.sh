#!/bin/bash
cd /home/claude/fcc
(timeout 300 python3 minviol.py 1 0.5 3000 6 > out/minviol.txt 2>&1) &
(python3 lin.py families > out/lin_families.txt 2>&1; for r in 5 6 7 8; do python3 lin.py near $r; done > out/lin_near.txt 2>&1) &
(python3 lin.py bridge 5 > out/lin_bridge.txt 2>&1; python3 lin.py bridge 6 >> out/lin_bridge.txt 2>&1) &
(python3 lintest.py special > out/lintest_special.txt 2>&1; python3 dscan.py > out/dscan.txt 2>&1; python3 chords.py > out/chords.txt 2>&1; python3 chordB.py > out/chordB.txt 2>&1; python3 chordM.py families > out/chordM_families.txt 2>&1) &
(python3 chordM2.py families; python3 chordM2.py unions 7 7; python3 chordM2.py unions 5 8; python3 chordM2.py near 5; python3 chordM2.py near 7; python3 chordM2.py bridge 5) > out/chordM2.txt 2>&1 &
(python3 steps.py 9 > out/steps.txt 2>&1; python3 slopes.py families > out/slopes.txt 2>&1) &
wait
echo done > out/runall19.done
