# Verified convergence checker (extracted oracle)

A runnable checker, **extracted from the machine-checked Coq proof** (`../Checker.v`), that
independently certifies a governed machine's step tables converge: it confirms the per-event
step functions commute and stay in range, so applying the same events in any order reaches the
same state. Because the checking logic is extracted from a Coq development proven axiom-free
(`checked_converges`, `check_commuting_sound`), a bug in gsm's hand-written Go verification
cannot make a non-convergent machine pass here.

This is the **differential-testing oracle** for gsm: gsm builds and verifies a machine in Go and
emits its tables (`Machine.WriteConvergenceTables`); this checker re-certifies them from a
different, verified implementation. If they ever disagree, one of them has a bug, and it is not
this one.

## Build and demo

Requires `coqc` (Rocq/Coq) and OCaml (`ocamlfind ocamlopt`).

```
make          # extract Checker.v to OCaml and compile ./checker
make demo     # accepts a commuting machine, rejects a non-commuting one
```

## Differential test against gsm

```
# in the gsm repo:
GSM_CONVERGENCE_CHECKER=/path/to/normalization-confluence/coq/extraction/checker \
  go test ./... -run TestConvergenceTables_WriteAndVerify
```

The gsm test builds a machine, writes its tables, and runs this checker on them; the test fails
if the verified checker rejects tables gsm called convergent.

## Tables format

Whitespace-separated integers: `V nE`, then `nE` rows of `V` next-state ids, where entry
`(e, s)` is the normalized state reached by applying event `e` in state `s`. gsm emits only the
valid states, remapped to `0..V-1`.

## Scope

The checker certifies **convergence** (order-independent application) of the emitted tables. It
does not re-derive the tables from the registry rules, and it operates on the finite table gsm
produces (so it shares Build's global-enumeration ceiling; compositional machines have no global
tables to export). What it adds is an independent, machine-checked confirmation that the tables
gsm ships actually converge. Extracted code and the compiled binary are build artifacts (see
`.gitignore`); regenerate with `make`.
