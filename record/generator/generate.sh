#!/bin/bash
# bash generate.sh <circuit> <golden.aig> <start_size.blif> <start_depth.blif>; writes ./out.blif
set -u
python3 decsyn.py "$2" out.blif
code=$?
if [ "$code" -eq 3 ]; then  # not a decoder: the method does not apply and the size start is kept unchanged
    cp "$3" out.blif
    code=$?
fi
exit "$code"
