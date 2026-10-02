#!/usr/bin/env bash
# genbool.sh K -> K two-valued variables (2^K states): var0 implies var1 (repair
# sets var1), events set var0, set var2, set var3.
k=$1; printf '(doms'; for i in $(seq 1 $k); do printf ' 2'; done; echo ')'
echo '(inv (le (var 0) (var 1)) (do (set 1 (lit 1))))'
echo '(ev (do (set 0 (lit 1))))'
echo '(ev (do (set 2 (lit 1))))'
echo '(ev (do (set 3 (lit 1))))'
