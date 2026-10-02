#!/usr/bin/env bash
# SPIKE (spike/go-extraction): extract check_fast and checkBuild to JSON,
# generate Go with gogen, build the Go checkers, and differential-test them
# against the OCaml-extracted checker_fast and astchecker (built by
# ../extraction/Makefile). Run after the .vo files for Trace, TableCheck,
# TableFast, Checker and AstChecker exist.
set -euo pipefail
cd "$(dirname "$0")/.."
coqc -Q . NC goextract/ExtrGo.v
coqc -Q . NC goextract/ExtractGo.v
(cd goextract/gogen && go build -o gogen .)
goextract/gogen/gogen -o goextract/gocheck/fastcore_gen.go goextract/fast_core.json
goextract/gogen/gogen -o goextract/gocheck_ast/astcore_gen.go goextract/ast_core.json
(cd goextract/gocheck && go build -o gocheck .)
(cd goextract/gocheck_ast && go build -o gocheck_ast .)
python3 goextract/difftest.py extraction/checker_fast goextract/gocheck/gocheck 400 1
DIFF_MAXDIM=16 python3 goextract/difftest.py extraction/checker_fast goextract/gocheck/gocheck 150 2
python3 goextract/difftest_ast.py extraction/astchecker goextract/gocheck_ast/gocheck_ast 1000 1
