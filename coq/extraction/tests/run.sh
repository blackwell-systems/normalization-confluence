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
  out="$(ulimit -s 8192; "$bin/checker" "$big/$f.tables" 2>&1)"; got=$?
  if [ "$got" = 0 ]; then
    pass=$((pass + 1)); echo "ok   checker $f.tables (exit 0)"
  else
    fail=$((fail + 1)); echo "FAIL checker $f.tables: want exit 0, got $got (convergent; the checker must not need stack that grows with the input)"; echo "$out" | sed 's/^/     /'
  fi
done
rm -rf "$big"

# The extracted code must not call the Nat module's own add, mul or pow:
# ExtrOcamlNatInt maps Init.Nat's (to OCaml's +, *), but PeanoNat's Nat module
# carries unmapped copies, which extract as unary recursion (Nat.mul 2^19 2
# overflows an 8 MiB stack). Use Init.Nat's (the * and + notations).
if grep -nE "Nat\.(add|mul|pow)\b" "$bin/checker_core.ml"; then
  fail=$((fail + 1)); echo "FAIL checker_core.ml calls the unary Nat.add, Nat.mul or Nat.pow (lines above)"
else
  pass=$((pass + 1)); echo "ok   checker_core.ml calls no unary Nat.add, Nat.mul or Nat.pow"
fi
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
