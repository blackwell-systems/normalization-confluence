# SPIKE: Coq-to-Go generation (route D)

Not for merge. Generates Go from the proof's own extraction instead of running
OCaml (natively or as wasm).

- `ExtrGo.v`: the directives. They map exactly the constants ExtrOcamlBasic,
  ExtrOcamlNatInt and ExtrOcamlZInt map for the OCaml checkers, each to its own
  `prim_*` symbol (types to `go_*`).
- `ExtractGo.v`: `Extraction Language JSON` of `check_fast` (fast_core.json) and
  of `checkBuild`, `wfc`, `bounded`, `signSafe`, `compensationFree`,
  `check_tables`, `of_list` (ast_core.json).
- `gogen/`: the generator (MiniML JSON to Go): strict JSON decoding, generic
  structs for inductives, Hindley-Milner inference for Go types, curried
  closures, switch for match, self tail calls as loops, short-circuit `andb`,
  overflow-checked int64 numbers (nat, positive, N, Z), constructor functions
  `K_*` for front ends.
- `gocheck/`, `gocheck_ast/`: Go ports of `main_fast.ml` and `ast_main.ml` over
  the generated cores. `difftest.py`, `difftest_ast.py`: random inputs, Go vs
  the OCaml checkers.
- `goose/`: route A sketch (hand-written Goose-subset checker and its Goose
  translation), not verified.
- `run.sh`: regenerate and test everything locally;
  `.github/workflows/goextract.yml` checks that Coq 8.18, 8.20 and the pinned
  Rocq 9.3 image all give the committed Go, under Go 1.22 and stable.
