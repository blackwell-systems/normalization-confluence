#!/usr/bin/env bash
# genmany.sh K -> K two-valued variables, K events (set var i := 1), so
# K(K-1)/2 pairs; var0 implies var1 (repair sets var1).
k=$1; printf '(doms'; for i in $(seq 1 $k); do printf ' 2'; done; echo ')'
echo '(inv (le (var 0) (var 1)) (do (set 1 (lit 1))))'
for i in $(seq 0 $((k-1))); do echo "(ev (do (set $i (lit 1))))"; done
