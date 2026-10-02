#!/usr/bin/env bash
# gen.sh K -> square machine with doms 2^(K/2) 2^(K-K/2): a capped counter, two
# increments and a guarded increment (convergent, so checkBuild runs to the end).
k=$1; a=$((1 << (k/2))); b=$((1 << (k - k/2)))
cat <<M
(doms $a $b)
(inv (le (var 0) (lit $((a-2)))) (do (set 0 (lit $((a-2))))))
(ev (do (set 0 (add (var 0) (lit 1)))))
(ev (do (set 1 (add (var 1) (lit 1)))))
(evwhen (le (var 1) (lit 100000)) (do (set 1 (add (var 1) (lit 1)))))
M
