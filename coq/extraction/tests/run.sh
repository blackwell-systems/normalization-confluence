#!/usr/bin/env bash
# Regression tests for the extracted checkers' front ends and semantics. Each line of
# cases.tsv names the checker, its case file(s) (space-separated, passed in order:
# astchecker takes a machine and an optional pairs file), and the exit code it
# must produce. Run from anywhere after `make` in coq/extraction; exits non-zero on any
# mismatch.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
bin="$here/.."
pass=0; fail=0
while IFS=$'\t' read -r want tool file why; do
  case "$want" in ''|'#'*) continue ;; esac
  args=(); for f in $file; do args+=("$here/cases/$f"); done
  out="$("$bin/$tool" "${args[@]}" 2>&1)"; got=$?
  if [ "$got" = "$want" ]; then
    pass=$((pass + 1)); echo "ok   $tool $file (exit $got)"
  else
    fail=$((fail + 1)); echo "FAIL $tool $file: want exit $want, got $got ($why)"; echo "$out" | sed 's/^/     /'
  fi
done < "$here/cases.tsv"

# The two rules oracles agree (astdiff: checkBuildT, which astchecker runs,
# against checkBuild). checkBuildT_eq proves it; this checks the extraction:
# on every well-formed machine case above, on the profile's machine shapes at
# 2^10 states, and on random machines (accepted and rejected ones; astdiff
# prints the verdict counts and stops at the first disagreement).
while IFS=$'\t' read -r want tool file why; do
  case "$want" in ''|'#'*|2) continue ;; esac
  [ "$tool" = astchecker ] || continue
  args=(); for f in $file; do args+=("$here/cases/$f"); done
  if out="$("$bin/astdiff" "${args[@]}" 2>&1)"; then
    pass=$((pass + 1)); echo "ok   astdiff $file"
  else
    fail=$((fail + 1)); echo "FAIL astdiff $file: the rules oracles disagree"; echo "$out" | sed 's/^/     /'
  fi
done < "$here/cases.tsv"
shapes="$(mktemp -d)"
{ echo "(doms 32 32)"; echo "(inv (le (var 0) (lit 30)) (do (set 0 (lit 30))))"
  echo "(ev (do (set 0 (add (var 0) (lit 1)))))"; echo "(ev (do (set 1 (add (var 1) (lit 1)))))"
  echo "(evwhen (le (var 1) (lit 100000)) (do (set 1 (add (var 1) (lit 1)))))"; } > "$shapes/sq10.machine"
{ printf '(doms'; for i in $(seq 1 10); do printf ' 2'; done; echo ')'
  echo '(inv (le (var 0) (var 1)) (do (set 1 (lit 1))))'
  for i in 0 2 3; do echo "(ev (do (set $i (lit 1))))"; done; } > "$shapes/bool10.machine"
{ printf '(doms'; for i in $(seq 1 10); do printf ' 2'; done; echo ')'
  echo '(inv (le (var 0) (var 1)) (do (set 1 (lit 1))))'
  for i in $(seq 0 9); do echo "(ev (do (set $i (lit 1))))"; done; } > "$shapes/many10.machine"
# A non-convergent variant: event 10 clears variable 1, which the repair sets.
{ cat "$shapes/many10.machine"; echo "(ev (do (set 1 (lit 0))))"; } > "$shapes/many10-bad.machine"
for f in sq10 bool10 many10 many10-bad; do
  if out="$("$bin/astdiff" "$shapes/$f.machine" 2>&1)"; then
    pass=$((pass + 1)); echo "ok   astdiff $f.machine ($out)"
  else
    fail=$((fail + 1)); echo "FAIL astdiff $f.machine: the rules oracles disagree"; echo "$out" | sed 's/^/     /'
  fi
done
rm -rf "$shapes"
# Wide machines: 16 to 20 events (a second 16-entry column block per cell)
# and 256 to about 2000 states (a cell trie at least two levels deep).
for seed in 1 2; do
  if out="$("$bin/astdiff" --wide 200 "$seed" 2>&1)"; then
    pass=$((pass + 1)); echo "ok   astdiff --wide 200 $seed ($out)"
  else
    fail=$((fail + 1)); echo "FAIL astdiff --wide 200 $seed: the rules oracles disagree"; echo "$out" | sed 's/^/     /'
  fi
done
for seed in 1 2 3; do
  if out="$("$bin/astdiff" --random 20000 "$seed" 2>&1)"; then
    pass=$((pass + 1)); echo "ok   astdiff --random 20000 $seed ($out)"
  else
    fail=$((fail + 1)); echo "FAIL astdiff --random 20000 $seed: the rules oracles disagree"; echo "$out" | sed 's/^/     /'
  fi
done

# Large inputs. Identity tables over 2^20 states (gsm's maximum; one event, every
# state valid) must be accepted. Generated, not stored (about 15 MB). The
# previous extraction (check_tables) died here with Stack_overflow under OCaml
# 4.14 native code.
big="$(mktemp -d)"
n=1048576
ids() { awk -v n="$1" 'BEGIN { for (i = 0; i < n; i++) printf " %d", i; print "" }'; }
{ echo "gsm-tables 2"; echo "$n 1"; printf 'nf'; ids $n; echo "pairs all"; ids $n; } > "$big/id20.tables"
# Many events or pairs: the stack must not grow with them either. One state
# (0, valid), every step 0, so each table converges.
zeros() { awk -v n="$1" 'BEGIN { for (i = 0; i < n; i++) printf " 0"; print "" }'; }
{ echo "gsm-tables 2"; echo "1 1000"; echo "nf 0"; echo "pairs all"; zeros 1000; } > "$big/events1000-all.tables"
{ echo "gsm-tables 2"; echo "1 1"; echo "nf 0"; printf 'pairs 500000'; awk 'BEGIN { for (i = 0; i < 500000; i++) printf " 0 0"; print "" }'; echo " 0"; } > "$big/pairs500k.tables"
{ echo "gsm-tables 2"; echo "1 300000"; echo "nf 0"; echo "pairs 0"; zeros 300000; } > "$big/events300k.tables"
# Run them under the common 8 MiB default stack limit, whatever the host's is
# (CI containers may have it unlimited), so the result does not depend on it.
echo "host stack limit: $(ulimit -s); large cases run with 8192 KiB"
for f in id20 events1000-all pairs500k events300k; do
  out="$(ulimit -s 8192 && "$bin/checker" "$big/$f.tables" 2>&1)"; got=$?
  if [ "$got" = 0 ]; then
    pass=$((pass + 1)); echo "ok   checker $f.tables (exit 0)"
  else
    fail=$((fail + 1)); echo "FAIL checker $f.tables: want exit 0, got $got (convergent; the checker must not need stack that grows with the input)"; echo "$out" | sed 's/^/     /'
  fi
done
# The rules oracle on gsm-sized state spaces, also at an 8 MiB stack: one
# variable with 2^20 values (every read converts a large nat to Z), and 20
# two-valued variables (the valuation box has 2^20 entries). One event, so each
# machine converges.
{ echo "(doms 1048576)"; echo "(ev (do (set 0 (lit 1))))"; } > "$big/dom20.machine"
{ printf '(doms'; for i in $(seq 1 20); do printf ' 2'; done; echo ')'; echo "(ev (do (set 0 (lit 1))))"; } > "$big/bits20.machine"
for f in dom20 bits20; do
  out="$(ulimit -s 8192 && "$bin/astchecker" "$big/$f.machine" 2>&1)"; got=$?
  if [ "$got" = 0 ]; then
    pass=$((pass + 1)); echo "ok   astchecker $f.machine (exit 0)"
  else
    fail=$((fail + 1)); echo "FAIL astchecker $f.machine: want exit 0, got $got (convergent; the checker must not need stack that grows with the input)"; echo "$out" | sed 's/^/     /'
  fi
done
# Budget guard: 2^20 states and 20 events with every pair declared (gsm's
# largest machine with its default declaration, 190 pairs) must be checked
# within 30 s, the budget of gsm's in-process gate. Event e sets bit e, so every
# pair commutes and the check does all of its work. The budget is checked on the
# CI runner (the pinned image, OCaml 4.14), where the checker takes about 11 s
# end to end, parsing the 150 MB file included. This is a guard against
# regressions past the budget, not a test that failed before the change: the
# previous check_fast took about 22 s on the same runner (about 29 s on an Apple
# M-series laptop with OCaml 5).
{ echo "gsm-tables 2"; echo "$n 20"; printf 'nf'; ids $n; echo "pairs all"
  awk -v n="$n" 'BEGIN { for (e = 0; e < 20; e++) { b = 2 ^ e; for (s = 0; s < n; s++) printf " %d", (int(s / b) % 2 ? s : s + b); print "" } }'
} > "$big/bits20-all.tables"
start=$SECONDS
out="$(ulimit -s 8192 && "$bin/checker" "$big/bits20-all.tables" 2>&1)"; got=$?
took=$((SECONDS - start))
if [ "$got" = 0 ] && [ "$took" -le 30 ]; then
  pass=$((pass + 1)); echo "ok   checker bits20-all.tables (exit 0, ${took} s)"
else
  fail=$((fail + 1)); echo "FAIL checker bits20-all.tables: want exit 0 within 30 s, got exit $got after ${took} s"; echo "$out" | sed 's/^/     /'
fi
# Memory guard on the same machine: the checker must run in 768 MiB of address
# space (ulimit -v, so a larger allocation fails and the run exits non-zero).
# The input is 20M step entries; held as lists they alone take about 480 MB, so
# the front end reads them into arrays and checks them with check_fn over array
# accessors (TableFn.v). Checked on the CI runner (Linux; macOS does not
# enforce ulimit -v).
if ! (ulimit -v 786432) 2>/dev/null; then
  echo "skip checker bits20-all.tables in 768 MiB (this host cannot limit address space)"
else
out="$(ulimit -s 8192 && ulimit -v 786432 && "$bin/checker" "$big/bits20-all.tables" 2>&1)"; got=$?
if [ "$got" = 0 ]; then
  pass=$((pass + 1)); echo "ok   checker bits20-all.tables in 768 MiB (exit 0)"
else
  fail=$((fail + 1)); echo "FAIL checker bits20-all.tables in 768 MiB: want exit 0, got $got"; echo "$out" | sed 's/^/     /'
fi
fi
# Budget guard for the rules oracle: 20 two-valued variables (2^20 states), one
# invariant with a repair, and 20 events (event i sets variable i), with every
# pair declared (190 pairs). Every pair commutes, so the check does all of its
# work. It must finish within 30 s, the budget of gsm's in-process gate, at an
# 8 MiB stack. The pairwise rules check took about 250 s here on an Apple M1
# Pro; computing step tables from the rules and scanning them as check_fast
# does is what brings it under budget. timeout stops a regression at 60 s.
{ printf '(doms'; for i in $(seq 1 20); do printf ' 2'; done; echo ')'
  echo '(inv (le (var 0) (var 1)) (do (set 1 (lit 1))))'
  for i in $(seq 0 19); do echo "(ev (do (set $i (lit 1))))"; done
} > "$big/many20.machine"
start=$SECONDS
out="$(ulimit -s 8192 && timeout 60 "$bin/astchecker" "$big/many20.machine" 2>&1)"; got=$?
took=$((SECONDS - start))
if [ "$got" = 0 ] && [ "$took" -le 30 ]; then
  pass=$((pass + 1)); echo "ok   astchecker many20.machine (exit 0, ${took} s)"
else
  fail=$((fail + 1)); echo "FAIL astchecker many20.machine: want exit 0 within 30 s, got exit $got after ${took} s"; echo "$out" | sed 's/^/     /'
fi
rm -rf "$big"

# The extracted code must not call unary nat arithmetic or conversions: the Nat
# module's own add, mul, pow, min, max, sub, pred (ExtrOcamlNatInt maps Init.Nat's
# to OCaml's +, *, min, ..., but PeanoNat's Nat module carries unmapped copies),
# or Z.of_nat / N.of_nat / Pos.of_nat, which go through the unary, non-tail
# Pos.of_succ_nat. Each extracts as unary recursion (Nat.mul 2^19 2 overflows an
# 8 MiB stack). Use Init.Nat's operations and AstChecker.natZ.
if grep -nE "Nat\.(add|mul|pow|min|max|sub|pred)\b|Z\.of_nat|N\.of_nat|Pos\.of_nat|of_succ_nat" "$bin/checker_core.ml"; then
  fail=$((fail + 1)); echo "FAIL checker_core.ml calls unary nat arithmetic or conversions (lines above)"
else
  pass=$((pass + 1)); echo "ok   checker_core.ml calls no unary nat arithmetic or conversions"
fi
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
