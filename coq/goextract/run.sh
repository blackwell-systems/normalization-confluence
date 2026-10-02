#!/usr/bin/env bash
# SPIKE (spike/go-extraction): extract check_fast and check_tables to JSON,
# generate Go with gogen, build both Go checkers, and differential-test them
# against the OCaml-extracted checker_fast (built by ../extraction/Makefile).
# Run from coq/ after the .vo files for Trace, TableCheck and TableFast exist.
set -euo pipefail
cd "$(dirname "$0")/.."
coqc -Q . NC goextract/ExtractGo.v
coqc -Q . NC goextract/ExtractGoTables.v
(cd goextract/gogen && go build -o gogen .)
goextract/gogen/gogen -o goextract/gocheck/fastcore_gen.go goextract/fast_core.json
goextract/gogen/gogen -o goextract/gocheck_tables/tablescore_gen.go goextract/tables_core.json
(cd goextract/gocheck && go build -o gocheck .)
(cd goextract/gocheck_tables && go build -o gocheck_tables .)
for b in gocheck/gocheck gocheck_tables/gocheck_tables; do
  python3 goextract/difftest.py extraction/checker_fast goextract/$b 400 1
  DIFF_MAXDIM=16 python3 goextract/difftest.py extraction/checker_fast goextract/$b 150 2
done
