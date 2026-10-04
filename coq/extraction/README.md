# Verified convergence checkers (extracted oracles)

Two runnable checkers, both **extracted from the machine-checked Coq proof** and proven
axiom-free, that independently certify a governed machine converges. Because the checking logic
is extracted from Coq, a bug in gsm's hand-written Go verification cannot make a non-convergent
machine pass here.

- **`checker`** (the TABLE oracle, `check_fn` from `../TableFn.v` over accessors on the parsed
  arrays; `check_tables_fn` and `check_fast_fn` prove it equal to `../TableCheck.v`'s
  `check_tables` and to the list entry point `check_fast`): certifies a machine's emitted tables
  have the property gsm's `Build` checks: normal forms and steps land on valid states (`NF s = s`),
  and every declared-independent pair of events commutes on the valid states and the zero state.
  So event sequences that differ only by reordering declared-independent events reach the same
  state. Proven axiom-free via `check_tables_converges` (and `check_tables_converges_all` for
  every permutation when no pairs are declared), and stated on the accessors by
  `check_fn_converges`. It handles gsm's largest machines (2^20 states), and its stack depth does not
  grow with the number of states, events or declared pairs. Its time grows with the number of
  states times (events + declared pairs), not with events times pairs: on 2^20 states, 20 events
  and every pair declared it takes about 11 s end to end on the CI runner, parsing included
  (`tests/run.sh` fails above 30 s, gsm's budget for its in-process gate). It scans the file in
  place and holds the entries in arrays, so on that machine it peaks at about 320 MB (`tests/run.sh`
  runs it in 768 MiB of address space).
- **`astchecker`** (the RULES oracle, `checkBuildC` from `../AstCompact.v`, proven equal to
  `../AstChecker.v`'s `checkBuild` by `checkBuildC_eq`): certifies a combinator machine
  straight from its **rules** (the expression-tree AST), not its output tables. It recomputes
  each event's step function by evaluating the AST (apply the event, then normalize by iterated
  repair) and checks the property gsm's `Build` checks: repair terminates from every valuation
  (WFC), and every declared pair commutes on every valid valuation and on the zero valuation,
  under gsm's step (which normalizes even when a guard is false). So it does not trust gsm to have
  enumerated or normalized anything: it re-derives convergence from the declarations themselves.
  Proven axiom-free via `checkBuild_converges`, `checkBuild_commute`, `checkBuild_wfc_terminates`.
  It evaluates the rules once per state and event into step tables packed in 16-entry blocks,
  without holding the valuation box, and checks every declared pair from them, so its time grows
  with the states times (events + declared pairs): on 2^20 states, 20 events and every pair
  declared it takes about 10 s (`checkBuild`, pair by pair, took about 260 s; `tests/run.sh` fails
  above 30 s) and peaks at about 440 MiB; with 3 events it takes about 2 s in 70 to 130 MiB
  (Apple M1 Pro, OCaml 5; `tests/run.sh` runs two such machines in 256 MiB of address space).
  Arithmetic is gsm's: signed integers, with `check_no_overflow` proving
  that a certified machine never leaves 32-bit range, so Go's `int` never wraps. It also prints a `compensation_free=<bool>` line: the machine-checked
  CRDT-fragment classification (no in-domain valuation ever needs repair, the AST analogue of
  "max repair depth = 0"), proven axiom-free via `compensationFree_step_no_repair`, so a consumer
  can certify the CRDT claim from the rules rather than trust the producer.

These are the **differential-testing oracles** for gsm: gsm builds and verifies a machine in Go,
then emits either its tables (`Machine.WriteConvergenceTables`) or its rules
(`Registry.WriteMachineAST`); the matching checker re-certifies from a different, verified
implementation. If they ever disagree, one of them has a bug, and it is not this one.

## Build and demo

Requires `coqc` (Rocq/Coq) and OCaml (`ocamlfind ocamlopt`).

```
make          # extract to OCaml and compile ./checker and ./astchecker (make test also builds ./astdiff)
make demo     # table oracle: accepts a commuting machine, rejects a non-commuting one
make astdemo  # rules oracle: accepts convergent rules, rejects non-convergent rules
```

## Differential test against gsm

```
# in the gsm repo:

# table oracle -- cross-check gsm's emitted step tables:
GSM_CONVERGENCE_CHECKER=/path/to/normalization-confluence/coq/extraction/checker \
  go test ./... -run TestConvergenceTables_WriteAndVerify

# rules oracle -- cross-check gsm's verdict straight from the combinator rules:
GSM_AST_CHECKER=/path/to/normalization-confluence/coq/extraction/astchecker \
  go test ./... -run TestMachineAST
```

Each gsm test builds a machine, serializes it, and runs the matching checker on it; the test
fails if the verified checker disagrees with gsm's verdict.

## File formats

**Tables** (`checker`), version 2, whitespace-separated:

```
gsm-tables 2
V nE
nf <V state ids>                        ; normal form of each state
pairs all | pairs k a1 b1 ... ak bk     ; event pairs declared independent
<nE rows of V next-state ids>
```

Entry `(e, s)` of a row is the normalized state reached by applying event `e` in state `s`. A
state is valid when `nf[s] = s`; state 0 is the zero state. gsm emits every in-domain encoding
(every variable within its domain), remapped to `0..V-1` in encoding order. A version-1 file
(`V nE` then the rows, no header) is still accepted and checked as if every state were valid and
every pair declared, which is the original check.

**Declared pairs** (`astchecker`'s optional second file): `pairs all` or
`pairs k a1 b1 ... ak bk`, by event index in the order the machine file lists events. Without the
file every pair is checked. gsm writes it with `Registry.WriteDeclaredPairs`; it is not part of the
machine file, so `PolicyBytes` and the digests over it do not change.

**Machine rules** (`astchecker`): S-expressions, one form per top-level line.

```
(doms 5 5 2)                          ; domain size of each variable
(mins 2 -3 0)                         ; logical minimum of each variable (optional; default 0s)
(inv (le (var 0) (lit 5))             ; invariant: a predicate ...
     (do (set 0 (lit 5))))            ;   ... and its repair transform
(ev     (do (set 1 (add (var 1) (lit 1)))))          ; unguarded event
(evwhen (lt (var 0) (lit 6))                          ; guarded event (no-op when guard is false)
        (do (set 0 (add (var 0) (lit 1)))))
```

with `expr ::= (var i) | (lit n) | (add e e) | (sub e e)` (`n` may be negative),
`pred ::= (le e e) | (lt e e) | (eq e e) | (and p...) | (or p...) | (not p)`, and
`xform ::= (do (set i e)...)`. A variable's values live in `min .. min+domain-1`; the state stores
the raw `0..domain-1` offset. Arithmetic and comparisons are signed, and a write clamps the value
into the variable's range. The checker refuses (exit 1, "outside the certified fragment") two kinds of
machine it does not model: one where some expression could exceed 2^31-1 in magnitude, because
gsm's Go `int` would wrap there on 32-bit platforms; and one where a write could store a negative
value into a two-valued variable with min 0, because a gsm Bool stores `value != 0` there while
the model clamps to 0. The format carries no variable kinds, so that rule covers every two-valued,
min-0 variable (`check_binary_writes_exact` proves that on a certified machine the clamp and the
Bool write agree on every such write). `Registry.WriteMachineAST` emits exactly this for the fragment it
covers (any min; comparison/and/or/not predicates; Set/Add/Sub transforms; events with an optional
guard) and refuses anything outside it.

Both front ends validate input and exit 2 on anything malformed, because the extracted code is
only meaningful on well-formed values: integers must be decimal (no `0x`, `+` or `_`) and at most
2^31-1 in magnitude; state ids, variable indices and domains must be non-negative; the tables
file must hold exactly the entries its header announces, with `V >= 1`; declared pairs must name
existing events; every domain is at least 1; the product of the domains (the number of states)
is at most 2^24, 16 times gsm's largest machines; `mins` gives exactly one entry per variable;
every variable index names a declared variable.

The 2^24 cap bounds how many states the rules oracle enumerates. It does not bound its memory:
a machine at the cap is 16 times gsm's largest, and its tables can need several GB (for the
rules oracle as of #14, at 16 times its 2^20 figures, about 8 GB in OCaml and over 20 GB in
Go).

## Tests

`make test` runs `tests/run.sh`, which runs each case in `tests/cases.tsv` through its checker
and compares the exit code. The cases pin gsm's signed semantics (including the subtraction-guard
probe that the earlier `nat` semantics certified wrongly), `Build`'s property (declared pairs,
the zero state, invalid states, repair termination from every state) and the input validation
above. It then runs the large inputs at an 8 MiB stack, with time budgets for both oracles at
2^20 states and a memory budget for the rules oracle, and `astdiff`, a test tool (`ast_diff.ml`)
that compares the three rules oracles, `checkBuildC` (what `astchecker` runs), `checkBuildT` and
`checkBuild`, on every well-formed machine case, on
the profiled machine shapes, on 60000 small random machines and on 400 with 16 to 20 events and 256 to about 2000 states, accepted and rejected ones, including
machines the front end refuses (domains of 0, variable indices and declared pairs out of range).
`ast_front.ml` holds the reader that `astchecker` and `astdiff` share. CI runs them on every push.

## Scope

The `checker` certifies **convergence of the emitted tables** for the declared pairs; it operates on the finite table
gsm produces, so it shares Build's global-enumeration ceiling (compositional machines have no
global tables to export). The `astchecker` certifies **convergence of the rules** over the whole
valuation box, so it likewise enumerates that box, but it never trusts gsm's tables or
normalization: it recomputes from the declarations. Together they pin gsm's verdict from two
independent, machine-checked angles. Extracted code and compiled binaries are build artifacts
(see `.gitignore`); regenerate with `make`.
