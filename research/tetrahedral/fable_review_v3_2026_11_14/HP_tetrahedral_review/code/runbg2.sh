#!/bin/bash
NCHECK=1 NEARONLY=1 python3 build3.py 80 4 "[[4],[4],[4],[4],[4],[4],[4],[4]]" 14 nochain 0 natural T8nc > T8_nochain_try.log 2>&1
NCHECK=1 NEARONLY=1 python3 build3.py 80 8 "[[4,4],[4,4]]" 14 nochain 0 natural Tcutnc > Tcut_nochain_try.log 2>&1
