#!/bin/bash
# third audit: K > 8, two assignments of the same items, unchained, word only ; then complete chained folds with the explicit tethers
P="[4,4,4,4,4,4,4,4,4,4]"
python3 build3.py 92 4 "$P;[[0],[1],[2],[3],[4],[5],[6],[7],[8],[9]]" 14 nochain 0 natural w92a word 2>&1 | grep -E "WORD|rror|assert"
python3 build3.py 92 4 "$P;[[7],[3],[9],[0],[5],[1],[8],[2],[6],[4]]" 14 nochain 0 natural w92b word 2>&1 | grep -E "WORD|rror|assert"
python3 build3.py 24 4 "[[2,2]]" 8 chain 0 natural t24r text:resid 2>&1 | grep -E "separator 1|OPTIMAL|rror|assert"
python3 verify_fold.py ../t24r_fold_coords.txt | grep -E "valid|attained" | tr '\n' ' '; echo
for tag in A B C; do case $tag in A) AS="[[0,1],[2,3]]";; B) AS="[[0,2],[1,3]]";; C) AS="[[3,0],[2,1]]";; esac
 python3 build3.py 28 4 "[2,2,2,2];$AS" 8 chain 0 natural tp$tag text:bound 2>&1 | grep -E "chain length|OPTIMAL|rror|assert" | tr '\n' ' '; python3 verify_fold.py ../tp${tag}_fold_coords.txt | grep -E "valid|attained" | tr '\n' ' '; md5sum ../tp${tag}_fold_string.txt | cut -c1-32; done
