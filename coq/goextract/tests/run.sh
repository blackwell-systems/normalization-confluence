#!/usr/bin/env bash
# Tests for the Go checkers over the generated oracle (run `make build` first).
#   tests/run.sh [<dir with the OCaml checker and astchecker>]
# 1. Every case of ../extraction/tests/cases.tsv gives its expected exit code
#    from bin/tablecheck or bin/rulecheck (and, with the OCaml checkers, the
#    same stdout as they do).
# 2. Large inputs: 2^20 states, and many events or declared pairs, run at an
#    8 MiB stack limit; they must be accepted.
# 3. With the OCaml checkers: the differential tests (random tables and rules).
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$here/.."
cases="$root/../extraction/tests"
ocaml="${1:-}"
pass=0; fail=0
ok() { pass=$((pass + 1)); echo "ok   $*"; }
bad() { fail=$((fail + 1)); echo "FAIL $*"; }

while IFS=$'\t' read -r want tool file why; do
  case "$want" in ''|'#'*) continue ;; esac
  case "$tool" in
    checker) go="$root/bin/tablecheck"; oc="${ocaml:+$ocaml/checker}" ;;
    astchecker) go="$root/bin/rulecheck"; oc="${ocaml:+$ocaml/astchecker}" ;;
    *) continue ;;
  esac
  args=(); for f in $file; do args+=("$cases/cases/$f"); done
  got=0; out="$("$go" "${args[@]}" 2>/dev/null)" || got=$?
  if [ "$got" != "$want" ]; then bad "$tool $file: want exit $want, got $got ($why)"; continue; fi
  if [ -n "$oc" ]; then
    oout="$("$oc" "${args[@]}" 2>/dev/null)"
    if [ "$out" != "$oout" ]; then bad "$tool $file: stdout differs from the OCaml checker"; continue; fi
  fi
  ok "$tool $file (exit $got)"
done < "$cases/cases.tsv"

big="$(mktemp -d)"
trap 'rm -rf "$big"' EXIT
n=1048576
ids() { awk -v n="$1" 'BEGIN { for (i = 0; i < n; i++) printf " %d", i; print "" }'; }
zeros() { awk -v n="$1" 'BEGIN { for (i = 0; i < n; i++) printf " 0"; print "" }'; }
{ echo "gsm-tables 2"; echo "$n 1"; printf 'nf'; ids $n; echo "pairs all"; ids $n; } > "$big/id20.tables"
{ echo "gsm-tables 2"; echo "1 1000"; echo "nf 0"; echo "pairs all"; zeros 1000; } > "$big/events1000-all.tables"
{ echo "gsm-tables 2"; echo "1 1"; echo "nf 0"; printf 'pairs 500000'; awk 'BEGIN { for (i = 0; i < 500000; i++) printf " 0 0"; print "" }'; echo " 0"; } > "$big/pairs500k.tables"
{ echo "gsm-tables 2"; echo "1 300000"; echo "nf 0"; echo "pairs 0"; zeros 300000; } > "$big/events300k.tables"
echo "host stack limit: $(ulimit -s); large cases run with 8192 KiB"
for f in id20 events1000-all pairs500k events300k; do
  got=0; out="$(ulimit -s 8192; "$root/bin/tablecheck" "$big/$f.tables" 2>&1)" || got=$?
  if [ "$got" = 0 ]; then ok "tablecheck $f.tables (exit 0)"; else bad "tablecheck $f.tables: want exit 0, got $got"; echo "$out" | sed 's/^/     /'; fi
done

if [ -n "$ocaml" ]; then
  for args in "400 1" "300 2"; do
    if python3 "$here/difftest_tables.py" "$ocaml/checker" "$root/bin/tablecheck" $args; then ok "difftest_tables $args"; else bad "difftest_tables $args"; fi
  done
  if DIFF_MAXDIM=16 python3 "$here/difftest_tables.py" "$ocaml/checker" "$root/bin/tablecheck" 150 3; then ok "difftest_tables depth 2"; else bad "difftest_tables depth 2"; fi
  for args in "1500 1" "1500 2"; do
    if python3 "$here/difftest_rules.py" "$ocaml/astchecker" "$root/bin/rulecheck" $args; then ok "difftest_rules $args"; else bad "difftest_rules $args"; fi
  done
fi
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
