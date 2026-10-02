# The Go oracle: the verified checkers, generated as Go

`extraction/` extracts the two verified checkers to OCaml. This directory extracts the same Rocq definitions to Go, so gsm can run them in-process: no OCaml, no subprocess, no cgo, and no dependencies.

- `check_fast` is the table oracle. It is proven equal to `check_tables` (`check_fast_eq`) and convergent (`check_fast_converges`).
- `checkBuild` is the rules oracle, together with `wfc`, `bounded`, `signSafe` and `compensationFree`.

The Go is not hand-written. Rocq extracts the definitions to MiniML (`Extraction Language JSON`), and `gogen` translates that MiniML to Go mechanically.

```
TableFast.v, AstChecker.v
   --(Rocq extraction, ExtrGo.v directives)-->  oracle_core.json
   --(gogen)-->                                 oracle/oracle_gen.go   (package oracle)
```

## Files

- `ExtrGo.v`: the extraction directives.
  - It maps the constants that ExtrOcamlBasic, ExtrOcamlNatInt and ExtrOcamlZInt map for the OCaml checkers, with the same references and the same Require context.
  - Three ExtrOcamlNatInt maps are left out, because the checkers do not use them: `lt_eq_lt_dec`, `Even_or_Odd` and Euclid's division. If one appears, it is extracted as its Rocq definition.
  - Each constant gets its own `prim_*` symbol, and each mapped inductive (`bool`, `sumbool`, `nat`, `positive`, `N`, `Z`) gets a `go_*` type.
  - Nothing else is mapped.
- `ExtractGo.v`: extracts `oracle_core.json`, with the same entry points as `extraction/Extract.v`.
- `gogen/`: the translator from MiniML JSON to Go.
  - **Strict decoding.** An unknown node kind or key, a malformed field, `Obj.magic`, or modular extraction is refused.
  - **Unsupported, and refused rather than translated:**
    - **Coinductive types and cofixpoints.** JSON extraction prints them as an ordinary inductive and a recursive value, so gogen cannot see them, and the Go would recurse until the process dies. `guard.sh` refuses them on the Rocq side: `make json` extracts every entry point once more as OCaml (`GuardCoind.v`) and fails if the output contains `Lazy`. Its self-test (`tests/coind/Coind.v`) must be refused. A gogen test checks that `GuardCoind.v` names every entry point the JSON extractions name.
    - Axioms (`expr:axiom`).
    - Types extraction cannot express (`type:unknown`, which needs `Obj.magic`).
    - A let-bound polymorphic function used at two types (locals are monomorphic).
    - A local fixpoint that extraction leaves in place (`expr:fix`, for example one applied inside a constructor argument).
    - A wildcard or variable case that is not the last case (ML takes the first match, a Go switch its default last).
    - A binder list that binds a name twice.
  - **Absurd branches.** An absurd branch (`expr:exception`) becomes a panic with nothing after it.
  - **Unary recursion refused.** gogen refuses unary recursion on a `nat` unless it is allowed by name in `allow-unary.txt`, with the reason. This means a fixpoint that calls itself, or a function of its fixgroup, on the predecessor bound by an `S` pattern.
    - Its time, and its stack unless the call is a tail call, are linear in the number. Examples are `Nat.add`, `Nat.mul` and `Nat.min` extracted as their Rocq definitions, and `Pos.of_succ_nat`, which `Z.of_nat` goes through.
    - The checkers' entries are all bounded: by fuel, trie depth, list position, the number of events or variables, or a domain size. Each one is a tail call where the bound can be large.
    - A test requires the list to be exact: nothing missing, nothing stale.
    - The check follows names bound by the pattern. A predecessor passed through another binding, such as `let k := p in f k`, is not traced.
  - **Types.** Inductives become generic Go structs. Hindley-Milner inference supplies every Go type, and every generic use is instantiated explicitly.
  - **Functions.** Local lambdas and partial applications become curried closures. A match becomes a switch.
  - **Tail calls.** A self tail call becomes a loop, with a fresh copy of the parameters per iteration so closures never see a later iteration's values. `andb` is a short-circuit `&&` whose right operand is in tail position.
  - **Front-end helpers.** Each constructor gets a `K_*` function, for front ends.
  - **Deterministic output.** The output is gofmt'd and depends only on the JSON. Globals are emitted in name order, and temporaries are numbered per function.
  - **Hand-written semantics.** `gogen/prims.go` holds the only hand-written semantics: the Go meaning of each `prim_*` and each mapped constructor.
- `oracle/oracle_gen.go`: the generated oracle. Do not edit it; run `make gen`.
- `cmd/tablecheck`, `cmd/rulecheck`: ports of `extraction/main.ml` and `extraction/ast_main.ml` over the generated oracle. They use the same formats, validation, output lines and exit codes.
- `PrimRef.v`, `ExtractPrimMapped.v`, `ExtractPrimPlain.v`, `primcheck/`: the prim check (below).
- `Fixture.v`, `ExtractFixture.v`, `fixture/`: small programs that reach the parts of `gogen` the checkers' extraction does not, run by `fixture/fixture_test.go`. Two of those parts are a let outside tail position and wildcard or variable patterns on mapped numbers. A third is closures built inside a tail-recursive loop, each of which must keep its own iteration's value.
- `Semantics.v`, `ExtractSemantics.v`, `SemanticsCompute.v`, `semantics/`: programs from the adversarial review, run by `semantics/semantics_test.go`.
  - The test compares the generated Go with Rocq's own `Compute` of every value (`semantics/compute.out`, written by `make json`).
  - The programs cover closures in loops, argument-swapping tail calls, mutual recursion, shadowing, unmapped Z/N/positive/nat arithmetic, partial and over-application, polymorphism, default branches, int64 edge values, records of functions, unused arguments and absurd branches.
- `gogen/testdata/refuse`: extractions gogen must refuse (an axiom, a let-polymorphic function used at two types, a type needing `Obj.magic`, a local fixpoint in argument position).
- `tests/`: the regression, large-input and differential tests (`tests/run.sh`).
- `ci-extract.sh`: extracts inside a prover image, as CI does.

## Numbers

`nat`, `positive`, `N` and `Z` are Go `int64`. Every operation that can leave the int64 range panics instead of wrapping:
- the `prim_*` arithmetic;
- the successor;
- the `positive` constructors;
- negation.

A result is therefore either the exact mathematical value, or the run stops and the gate fails closed. Every match on a `nat`, `positive` or `N` first checks that the value is in its type (non-negative, or at least 1), and panics otherwise, so a value outside its type never reaches a branch. The front ends' input bounds (integers below 2^31 in magnitude) keep every computation the checkers do far inside int64.

## The prim check

The prims and the mapped constructors are checked against their Rocq definitions rather than trusted.

`PrimRef.v` has two parts:
- one definition per mapped constant (`ref_nat_add := plus`, ...);
- probes that build and match every mapped constructor.

It is extracted twice:
- under `ExtrGo.v`, as package `primcheck/mapped`, which runs on the Go prims;
- with no directives, as package `primcheck/plain`, which runs on the Rocq definitions over unary `nat` and binary `positive`.

`primcheck` compares the two on every input in its ranges. The ranges cover:
- small values exhaustively;
- random values up to 2^30;
- the int64 extremes.

On the extremes the Go side must panic exactly when the exact result leaves int64; that is the only allowed difference. `gogen`'s tests check two coverage properties:
- every prim gogen knows has a reference, and that reference really extracts to the prim under `ExtrGo.v`;
- every mapped constructor is built and matched by a probe.

## Trusted base

The guarantee rests on:
- the Rocq kernel, which checks the theorems;
- Rocq's extraction, which erases to MiniML and prints the JSON;
- `gogen`;
- the Go toolchain.

`gogen` is about 1,450 lines and unverified. Its translation is checked by differential testing against the OCaml checkers. The prims and mapped constructors are checked by the prim check.

The OCaml compiler and runtime are not part of this base.

## Reproducibility

The reference is the digest-pinned Rocq 9.3 image that `extraction/` and gsm also use (`.github/workflows/goextract.yml`). In that image, the extracted JSON and the generated Go must be byte-identical to the committed files. A local Rocq 9.3.0 gives the same bytes.

Coq 8.18 and 8.20 extract the standard library differently, so their Go is not byte-identical:
- some binder names differ;
- the directive for `Pos.succ`, `Pos.add` and `Pos.compare` catches the constant there, while on 9.3 the definitions are extracted.

CI generates, builds and tests their Go with the same tests.

## Build and test

```
make json      # extract the JSON (needs coqc and the compiled proof)
make gen       # regenerate the committed Go from the committed JSON
make test      # go vet, go test (prim check, gogen tests), regression and large cases
make test OCAML=../extraction   # also the differential tests against the OCaml checkers
```

The code builds with Go 1.22 (gsm's floor) and later.
