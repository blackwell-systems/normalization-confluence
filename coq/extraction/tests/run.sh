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

# Large input: identity tables over 2^20 states (gsm's maximum; one event, every
# state valid) must be accepted. Generated, not stored (about 15 MB). The
# previous extraction (check_tables) died here with Stack_overflow under OCaml
# 4.14 native code.
big="$(mktemp -d)"
n=1048576
ids() { awk -v n="$1" 'BEGIN { for (i = 0; i < n; i++) printf " %d", i; print "" }'; }
{ echo "gsm-tables 2"; echo "$n 1"; printf 'nf'; ids $n; echo "pairs all"; ids $n; } > "$big/id20.tables"
out="$("$bin/checker" "$big/id20.tables" 2>&1)"; got=$?
if [ "$got" = 0 ]; then
  pass=$((pass + 1)); echo "ok   checker id20.tables (exit 0)"
else
  fail=$((fail + 1)); echo "FAIL checker id20.tables: want exit 0, got $got (2^20 identity tables are convergent)"; echo "$out" | sed 's/^/     /'
fi
rm -rf "$big"
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
