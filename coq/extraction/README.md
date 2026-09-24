# Verified convergence checkers (extracted oracles)

Two runnable checkers, both **extracted from the machine-checked Coq proof** and proven
axiom-free, that independently certify a governed machine converges. Because the checking logic
is extracted from Coq, a bug in gsm's hand-written Go verification cannot make a non-convergent
machine pass here.

- **`checker`** (the TABLE oracle, from `../Checker.v`): certifies a machine's emitted step
  tables converge, i.e. the per-event step functions commute and stay in range, so applying the
  same events in any order reaches the same state. Proven axiom-free via `checked_converges`,
  `check_commuting_sound`.
- **`astchecker`** (the RULES oracle, from `../AstChecker.v`): certifies a combinator machine
  straight from its **rules** (the expression-tree AST), not its output tables. It recomputes
  each event's step function by evaluating the AST (apply the event, then normalize by iterated
  repair) and confirms every event preserves validity and every pair commutes on every valid
  valuation. So it does not trust gsm to have enumerated or normalized anything: it re-derives
  convergence from the declarations themselves. Proven axiom-free via `check_sound_converges`,
  `check_sound_commute`.

These are the **differential-testing oracles** for gsm: gsm builds and verifies a machine in Go,
then emits either its tables (`Machine.WriteConvergenceTables`) or its rules
(`Registry.WriteMachineAST`); the matching checker re-certifies from a different, verified
implementation. If they ever disagree, one of them has a bug, and it is not this one.

## Build and demo

Requires `coqc` (Rocq/Coq) and OCaml (`ocamlfind ocamlopt`).

```
make          # extract to OCaml and compile ./checker and ./astchecker
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

**Tables** (`checker`): whitespace-separated integers `V nE`, then `nE` rows of `V` next-state
ids, where entry `(e, s)` is the normalized state reached by applying event `e` in state `s`.
gsm emits only the valid states, remapped to `0..V-1`.

**Machine rules** (`astchecker`): S-expressions, one form per top-level line.

```
(doms 5 5 2)                          ; domain size of each variable
(mins 2 0 0)                          ; logical minimum of each variable (optional; default 0s)
(inv (le (var 0) (lit 5))             ; invariant: a predicate ...
     (do (set 0 (lit 5))))            ;   ... and its repair transform
(ev     (do (set 1 (add (var 1) (lit 1)))))          ; unguarded event
(evwhen (lt (var 0) (lit 6))                          ; guarded event (no-op when guard is false)
        (do (set 0 (add (var 0) (lit 1)))))
```

with `expr ::= (var i) | (lit n) | (add e e) | (sub e e)`,
`pred ::= (le e e) | (lt e e) | (eq e e) | (and p...) | (or p...) | (not p)`, and
`xform ::= (do (set i e)...)`. A variable's values live in `min .. min+domain-1`; the state stores
the raw `0..domain-1` offset. `Registry.WriteMachineAST` emits exactly this for the fragment it
covers (any nonnegative min; comparison/and/or/not predicates; Set/Add/Sub transforms; events with
an optional guard) and refuses anything outside it.

## Scope

The `checker` certifies **convergence of the emitted tables**; it operates on the finite table
gsm produces, so it shares Build's global-enumeration ceiling (compositional machines have no
global tables to export). The `astchecker` certifies **convergence of the rules** over the whole
valuation box, so it likewise enumerates that box, but it never trusts gsm's tables or
normalization: it recomputes from the declarations. Together they pin gsm's verdict from two
independent, machine-checked angles. Extracted code and compiled binaries are build artifacts
(see `.gitignore`); regenerate with `make`.
