#!/usr/bin/env bash
# Regression tests for the extracted checkers' front ends and semantics. Each line of
# cases.tsv names a case file, the checker to run on it, and the exit code it must
# produce. Run from anywhere after `make` in coq/extraction; exits non-zero on any
# mismatch.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
bin="$here/.."
pass=0; fail=0
while IFS=$'\t' read -r want tool file why; do
  case "$want" in ''|'#'*) continue ;; esac
  out="$("$bin/$tool" "$here/cases/$file" 2>&1)"; got=$?
  if [ "$got" = "$want" ]; then
    pass=$((pass + 1)); echo "ok   $tool $file (exit $got)"
  else
    fail=$((fail + 1)); echo "FAIL $tool $file: want exit $want, got $got ($why)"; echo "$out" | sed 's/^/     /'
  fi
done < "$here/cases.tsv"
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
