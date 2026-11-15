#!/bin/bash
python3 bulktable2.py 18 19 79 80 > bulktable2_79_80.log 2>&1
python3 segstruct.py 79 80 > segstruct_79_80.log 2>&1
