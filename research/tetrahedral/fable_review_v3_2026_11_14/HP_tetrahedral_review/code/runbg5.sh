#!/bin/bash
# fourth audit: test layouts (unchained) with the universal track table; packing-free word vs words of packings
T8='4 "[[4],[4],[4],[4],[4],[4],[4],[4]]"'; TC='8 "[[4,4],[4,4]]"'; T3='12 "[[4,4,4]]"'
for nm in T8 TC T3; do a=${!nm}; eval "NCHECK=1 NEARONLY=1 python3 build3.py 80 $a 14 nochain 0 natural a4$nm" 2>&1 | grep -E "NEAR FIELD|NCHECK track|NCHECK Appendix|rror|assert" | sed "s/^/$nm: /"; done
I="[4,8,8,4]"
python3 build3.py 80 12 "$I;none" 14 nochain 0 natural a4w0 word 2>&1 | grep -E "WORD|rror|assert" | sed 's/^/no packing: /'
python3 build3.py 80 12 "$I;[[0,1],[2,3]]" 14 nochain 0 natural a4w1 word 2>&1 | grep -E "WORD|rror|assert" | sed 's/^/packing 1: /'
python3 build3.py 80 12 "$I;[[0,2],[1,3]]" 14 nochain 0 natural a4w2 word 2>&1 | grep -E "WORD|rror|assert" | sed 's/^/packing 2: /'
python3 build3.py 80 12 "$I;[[3,1],[2,0]]" 14 nochain 0 natural a4w3 word 2>&1 | grep -E "WORD|rror|assert" | sed 's/^/packing 3: /'
for i in 1 2 3; do cmp ../a4w0_word_rle.txt ../a4w${i}_word_rle.txt && echo "run-length encoded word of packing $i is byte-identical to the packing-free word"; done
head -c 300 ../a4w0_word_rle.txt; echo " ..."; tail -c 120 ../a4w0_word_rle.txt
