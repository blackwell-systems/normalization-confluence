# SPIKE: Coq-to-Go generation (route D)

Not for merge. Evaluates generating Go from the proof's own extraction instead
of running OCaml (natively or as wasm).

- `ExtractGo.v`, `ExtractGoTables.v`: `Extraction Language JSON` of `check_fast`
  and of `check_tables`/`of_list`. The directives map exactly the constants
  ExtrOcamlBasic/ExtrOcamlNatInt map for the OCaml checkers, to `prim_*` symbols.
- `gogen/`: the generator (MiniML JSON to Go): generic structs for inductives,
  Hindley-Milner inference for Go types, curried closures, switch for match,
  self tail calls as loops, short-circuit `andb`, checked int64 nat arithmetic.
- `gocheck/`, `gocheck_tables/`: a Go port of `main_fast.ml` over each generated
  core. `difftest.py`: random tables, Go vs OCaml `checker_fast` vs a direct
  Python reading of `check_tables`.
- `goose/`: route A sketch: the check hand-written in the Goose subset, and the
  Goose translation (`goose/out`), not verified.
- `run.sh`: regenerate and test everything.
