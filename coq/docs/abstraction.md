# Abstraction: check relationships between values, not the values

Detailed results for the abstraction reduction over integer-valued state (roadmap item 8, step 2;
gsm roadmap item 1b), its gsm instantiation, the difference-constraint fragment with saturating
writes ([below](#difference-constraints-differenceabstractionv)), and its extension to events with
integer parameters ([below](#difference-constraints-with-event-parameters-differenceparamsv)). Each module's one-line summary is in the
[module index](../README.md#modules-by-regime). This is a reduction for checking, not a regime:
it does not change any gap in [REGIME-AUDIT.md](../../REGIME-AUDIT.md).

## Integer-valued registries (`AbstractionCutoff.v`)

**When it applies.** Rules whose variables and event parameters are integers. Two fragments:

- **Order-invariant:** rules only compare and copy values ("stock is at least the quantity
  ordered"), against each other and a finite set of declared constants ("cap 5", "balance < 0").
- **Linear:** rules also add, subtract and multiply by literals ("balance minus amount stays
  non-negative").

Axiom-free.

**The model.** A state is a list of `n` integers (the variables). An event is `(k, p)`: a kind `k`
and a list `p` of `m` integer parameters. Events outside the declared kinds, or with the wrong
number of parameters, do nothing. The rules are apply `ap`, a repair step `rp` that leaves valid
states alone, and an invariant `vd`. This is an instance of `Governance.v`'s rewrite system with
free delivery, so `cc_exact_from` applies.

Repair is bounded: `TermK` says `K` repair steps reach a valid state from every state. The
governed step is then `govK e s = rp^K (ap e s)`. `un_bounded`: under `TermK`, every buffer from
every state has a unique normal form iff CC1 and CC2 hold at every state. `un_at` refutes unique
normal forms from a given start by one CC1 failure there.

### The order-invariant fragment: a finite representative domain

`OIso C X f` says that `f` preserves the order (`Z.compare`) on the values `X` together with the
declared constants `C`, and fixes every constant. `OrdInv` says that apply, repair and the
invariant commute with every such `f` on the values involved. So the rules see only the order
pattern of those values relative to the constants.

`reps N C` is the representative domain: `C`, the `N` integers above each constant, and the `N`
integers below the least constant (or `0 .. N-1` when `C` is empty).

- `reps_length`: `|reps N C| = |C| * (N + 1) + N`.
- `compress`: for any finite list `X` of integers, `cmp C X` is an order isomorphism on `X` and
  `C` that fixes `C` and maps `X` into `reps |X| C`.

In plain terms, any finitely many integers can be moved next to the constants without changing
how they compare to each other or to the constants.

| Condition | Representatives `N` | Domain size | Theorem |
|---|---|---|---|
| Repair within `K` steps (`TermK`) | `n` | `\|C\|(n+1) + n` | `term_abs` |
| WFC (a potential decreasing under repair) | `n` | `\|C\|(n+1) + n` | `wfc_abs` |
| CC2 | `n + m` | `\|C\|(n+m+1) + n + m` | `cc2_abs` |
| CC1 | `n + 2m` | `\|C\|(n+2m+1) + n + 2m` | `cc1_abs` |
| Unique normal forms for every start and buffer (`cc_exact_from`) | `n + 2m` | as CC1 | `un_abs`, `abs_check_exact` |

Each row is an iff, for every `N` at least the bound. The condition holds over all integer states
and parameters iff it holds over the states in `reps N C` with parameters in `reps N C`. The
`reps` count is an upper bound on distinct values: representatives coincide when constants are
closer together than `N`.

- `abs_check K N`: the finite boolean check (states `tup (reps N C) n`, events `evD N`, one no-op
  event for everything outside the declared kinds). `abs_check_spec`: it decides the three
  representative conditions. `abs_check_exact`: for `N >= n + 2m`, it passes iff `TermK` holds and
  every buffer from every integer state has a unique normal form. `abs_check_sound`: the pass
  direction.
- **One check per order type.** `cc1_order_type` and `cc2_order_type`: a CC1 or CC2 instance has
  the same truth value as every instance with the same order type. So a checker may also visit one
  tuple per order type instead of every tuple over `reps N C`. The number of order types is not
  mechanized (for `k` values and no constants it is the ordered Bell number: 1, 3, 13, 75 for
  `k` = 1 to 4).
- **No fresh values.** `closure_ap` and `closure_rp`: order invariance forces apply and repair to
  output only input values and constants. So the representative domain is closed under the rules.
- **The bound cannot drop below `n`.** `copy_tight`: with `x := y` and `y := x`, the check over one
  representative passes and the check over two fails, as it must, because the registry diverges
  at `(0, 1)`.

### The fragment, decided

`AbstractionCutoff.v` has a rule language: variables, integer literals, `+`, `-`, `*`,
if-then-else, and comparisons with connectives. A program `prog` gives, per event kind, the new
value of each variable over the state and the parameters; the repair, as the new value of each
variable; and the invariant. `wf` checks arities and variable indices.

- `ord_frag C P`: a boolean check that `P` only compares and copies variables and constants in
  `C` (no arithmetic, no undeclared literal).
- `ord_frag_sound`: a well-formed program in the fragment is `OrdInv`.
- `prog_shaped`: every well-formed program has the shape the cutoff needs.
- `build_sound`: `wf`, `ord_frag` and `abs_check` imply unique normal forms over all of Z.

### The linear fragment: formulas whose validity is the condition

Order patterns alone do not decide additive rules (`triangle_*` below). For a program in the
language, `AbstractionCutoff.v` generates the conditions as quantifier-free formulas over
`n + 2m` integer variables: the state, the first event's parameters, then the second event's.
The construction is symbolic execution by substitution:

- `symA`: an event of kind `k` with symbolic parameters.
- `symR`: the repair, as a per-variable if-then-else on the invariant.
- `symG`: `K` repairs after the event.
- `eqL`: equality of two symbolic states.

The formulas:

- `phi_term = inv(symR^K(x))`
- `phi_cc1 k1 k2 = (symG k2 (symG k1 x) == symG k1 (symG k2 x))`, for every pair of kinds,
  including the no-op kind `nkP`
- `phi_cc2 k = inv(x) \/ (symG k x == symG k (symR x))`

`FValid phi`: `phi` is true for every assignment of integers.

- `phi_term_exact`, `phi_cc1_exact`, `phi_cc2_exact`: for a well-formed program, `TermK`, CC1
  and CC2 over all integers hold iff the corresponding formulas are valid. Each is an iff, so a
  falsifying assignment is a real failure.
- `lin_exact`: given a valid `phi_term`, unique normal forms from every integer state and buffer
  hold iff all `phi_cc1` and `phi_cc2` are valid. `lin_sound`: the pass direction.
- `lin_frag P`: a boolean check that multiplication only takes a literal operand.
  `lin_frag_linear`: then every generated formula is linear. The formulas are Presburger
  (QF_LIA with if-then-else), a decidable theory.

What this does and does not give: the reduction to formula validity is mechanized and exact.
Deciding validity is left to an external SMT solver, which is the trusted step. No finite
representative set is claimed for the linear fragment as a whole. For its difference-constraint
part (increments, decrements, copies with an offset, guards on differences), with gsm's saturating
writes, `DifferenceAbstraction.v` gives one: [Difference constraints](#difference-constraints-differenceabstractionv). The repair must reach validity within a
declared bound `K`, which is checked by `phi_term`. A repair that needs a number of steps that
depends on the values (decrement until valid) is outside this form.

### Boundaries

- **Undeclared exact test** (`exact13_passes`, `exact13_diverges`, `exact13_refused`,
  `exact13_declared`). The rule is Pay(amount, tag): if amount = 13 then last := tag, with no
  constants declared.
  - The representative check over `reps 5 []` (values 0 to 4) passes.
  - Over the integers, Pay(13, 1) and Pay(13, 2) from last = 0 diverge.
  - `ord_frag []` refuses the rule.
  - With 13 declared, the rule is in the fragment, and the check over `reps 5 [13]` fails, as it
    should.
- **Additive rule** (`triangle_passes`, `triangle_diverges`, `triangle_refused`,
  `triangle_formula_refuted`). The variables are `(x, y, z)` and the guard is `x < y < z < x + y`.
  Event A sets x := y under the guard; event B sets y := x under it.
  - The order-pattern check over `0, 1, 2` passes: the only strictly increasing triple there is
    `(0, 1, 2)`, where `z = x + y + 1 > x + y`.
  - At `(2, 3, 4)` the guard holds, and A and B diverge.
  - `ord_frag` refuses the rule (it adds), and its CC1 formula is refuted at `(2, 3, 4)`.
- **The bound `n`** (`copy_tight`), above.

### Non-vacuity

- **Capped inventory, order fragment** (`capped_frag`, `capped_reps`, `capped_check`,
  `capped_un`, `capped_repair_fires`).
  - Stock, with Restock(level) setting stock := max(stock, level); invariant stock <= 5; repair
    clamps to the declared cap 5.
  - `reps 3 [5]` is `{2, ..., 8}`: 7 representatives.
  - The check passes, so every integer state and buffer has a unique normal form, and the repair
    fires at stock 7.
- **Wallet, linear fragment** (`wallet_frag`, `wallet_formulas`, `wallet_un`,
  `wallet_repair_fires`).
  - Balance and an overdrawn flag; Deposit(a) adds a and Withdraw(a) subtracts it; the invariant
    is "overdrawn = 1 exactly when balance < 0"; repair recomputes the flag.
  - The program is outside the order fragment for every constant set, and inside the linear one.
  - All 13 generated formulas (1 term, 9 CC1 over three kinds counting the no-op, 3 CC2) are proved
    valid in Coq by case splitting on the innermost comparisons, standing in for the solver.
  - Through `lin_sound`, every integer balance and buffer converges.

### Composed with symmetry

`sym_abs`: for a keyed collection of order-invariant items (`SymmetryCutoff.v`'s lift), one item
passing `abs_check` gives unique normal forms for every collection of any size. The proof runs
through `un_cutoff`, with the potential from `TermK`. `capped_catalog`: a catalog of capped items
of any size, checked through one item over 7 representatives.

### For gsm

The reduction gsm needs (gsm roadmap item 1b):

1. **Declaration.**
   - A field is declared as an integer type (`Int`, `Int64`) or as an ordered type that embeds in
     the integers with order kept (bounded integers, ordered enums).
   - Constants are declared per registry (`const Cap = 5`) or collected from the literals that the
     rules compare against. In the representative route, every literal a rule compares or copies
     must be a declared constant.
   - The repair bound `K` defaults to 1 and may be declared.
2. **Build, representative route** (all rules pass `ord_frag`).
   - Compute `N = n + 2m` (variables plus twice the largest event arity) and `D = reps N C`, of
     size at most `|C|(N+1) + N`.
   - Run the existing checks on states over `D` and event parameters over `D`, plus one no-op
     event: repair within `K` steps (or WFC), CC1 and CC2.
   - A pass is unique normal forms over all integers (`abs_check_exact`, `build_sound`). A failure
     is a real failure: the representative witness is itself an integer state.
   - gsm may instead enumerate one tuple per order type (`cc1_order_type`, `cc2_order_type`).
   - gsm's `Build` as implemented checks CC1 at the valid states only and normalizes before
     applying; the theorems for that are in [gsm instantiation](#gsm-instantiation-abstractiongsmv).
3. **Build, formula route** (rules use `+`, `-` or multiplication by a literal: `lin_frag`).
   - Generate `phi_term`, `phi_cc1 k1 k2` for every pair of kinds (no-op included) and `phi_cc2 k`
     for every kind, as defined in `AbstractionCutoff.v`.
   - Send the negation of each to an SMT solver as QF_LIA.
   - Every "unsat" means valid, and `lin_exact` turns all of them into unique normal forms over
     all integers.
   - A "sat" model is a concrete state and event parameters where the condition fails
     (`phi_cc1_exact`), so a real divergence (`un_at`).
   - The solver is the trusted step. gsm's formula generator must match the Coq construction; a
     differential test against an extraction of `phi_*` closes that gap.
   - The formulas are over mathematical integers. 64-bit wrap-around is not modeled, so gsm either
     evaluates with unbounded integers or adds the range guards to the formulas.
4. **Refusal.**
   - An expression outside both fragments (a product of two variables, division, modulo) is
     refused, naming the rule and the operation.
   - In the representative route, a literal that is not a declared constant ("if amount = 13")
     fails `ord_frag`. gsm names the rule and offers two fixes: declare the constant, or use the
     formula route. Refusal is required: `exact13_diverges` passes the undeclared check and
     diverges.
   - An additive rule is never sent to the representative route (`triangle_diverges`).
5. **Report lines.**
   - "Verified by abstraction over Stock (rules compare values only; constants {5}; 7
     representatives)".
   - "Verified by linear arithmetic over Balance (13 formulas valid by solver; repair within 1
     step)".
   - Over a bounded integer type, a pass is still sound, because its states are among the integer
     states and the rules create no new values. A failure witness outside the type's range is
     reported as such.

| Step | Theorem |
|---|---|
| Fragment check, representatives | `ord_frag_sound`, `prog_shaped` |
| Representative check is exact | `abs_check_exact`, `term_abs`, `wfc_abs`, `cc1_abs`, `cc2_abs`, `un_abs` |
| One tuple per order type | `cc1_order_type`, `cc2_order_type` |
| Formula generation is exact | `phi_term_exact`, `phi_cc1_exact`, `phi_cc2_exact`, `lin_exact` |
| Formulas are linear | `lin_frag_linear` |
| Failure is a real divergence | `un_at` |
| Refusals justified | `exact13_diverges`, `triangle_diverges` |
| With symmetry | `sym_abs` |

## gsm instantiation (`AbstractionGsm.v`)

**What gsm checks.** gsm's `Build` on a registry declared with `Abstract` does not run
`abs_check`. Over the states built from `reps N C` it checks that repair reaches a valid state
within `K` steps (`TermD K N`, with `K` the deepest repair chain it finds), CC1 for the checked
event pairs at the **valid** representative states only (not CC2), and which events are
idempotent at the valid representative states. Its runtime `Apply` normalizes every invalid
input first, the zero state included, then applies the event and normalizes. gsm's events take no
parameters (`m = 0`), so its cutoff is `N = n`. Every statement below is for general `m` and
specializes to `m = 0`. Axiom-free.

**The conditions.** `InSig e`: `e` is an event of the registry (kind below `nk`, `m` parameters).
`I` is a relation on event kinds (gsm's checked pairs; every pair by default).

- `CC1VZ K I`: for every integer state `s` with `vd s = true` and all events `(k1, p1)`,
  `(k2, p2)` of the registry with `I k1 k2`,
  `govK (k2, p2) (govK (k1, p1) s) = govK (k1, p1) (govK (k2, p2) s)`.
  This is gsm's CC1 as `verifyCC` and `absWitness` compute it: `step[j][step[i][s]]` against
  `step[i][step[j][s]]`, where each step applies the event (a no-op when its guard fails) and then
  repairs to validity.
- `CC1VD K N I`: the same over states in `tup (reps N C) n` and parameters in `tup (reps N C) m`.
- `IdemVZ K k`: for every valid integer state `s` and parameters `p`,
  `govK (k, p) (govK (k, p) s) = govK (k, p) s`. `IdemZ K k`: the same at every state.
  `IdemVD`, `IdemD`: over the representatives.
- `apR K`: the repair-first registry, `apR K e s = ap e (rp^K s)` for an event of the registry
  (and `s` otherwise). Its governed step `govK (apR K) e s = rp^K (ap e (rp^K s))` is gsm's runtime
  `Apply`.

**The transfers.** Each is an iff, for registries in the order-invariant fragment (`Shaped`,
`OrdInv`).

| Condition | Representatives `N` | Theorem |
|---|---|---|
| CC1 for `I` at every valid state | `n + 2m` | `cc1_valid_abs` |
| Idempotence of kind `k` at every state | `n + m` | `idem_abs` |
| Idempotence of kind `k` at every valid state | `n + m` | `idem_valid_abs` |
| Idempotence of gsm's runtime step, from every integer state (given `TermD`) | `n + m` | `idem_runtime_abs` |

- `cc1v_order_type`, `idem_order_type`: one check per order type, as `cc1_order_type`.
- `cc1v_check`, `idemv_check`: the finite boolean checks; `cc1v_check_spec`, `idemv_check_spec`:
  each passes iff its representative condition holds.

**Idempotence transfers.** "Event `k` is idempotent at every valid state" holds over the integers
iff it holds at the valid representative states (`idem_valid_abs`). So gsm can compute
`NotIdempotent` from the representatives, and the list is exact for every integer state: a listed
event has an integer witness (the representative state itself), and an unlisted event is
idempotent at every valid integer state, so the at-least-once results apply to it
(`AtLeastOnce.v`, `AtLeastOnceDeclared.v`). Deduplicating every event is not needed.

**Fragment preservation.** `OIMap g`: `g` keeps `n` variables and commutes with every order
isomorphism of its input that fixes `C`.

- `oimap_closed`: an order-invariant map outputs only input values and constants.
- `oimap_comp`: the composition of order-invariant maps is order invariant. `oimap_id`,
  `oimap_itr`: so is the identity and every iterate.
- `oimap_rp`: the repair of an `OrdInv` registry is one.
- `oi_ap_after`: an event applied after an order-invariant map is order invariant.
- `derived_shaped`, `derived_ordinv`: the repair-first registry `apR K` stays in the fragment.

**The derived-registry argument, mechanized.** gsm's docs justified the CC1 transfer in prose:
`cc1_abs` applied to the registry whose events first repair to validity, whose CC1 at every state
is gsm's CC1 at the valid states. Both steps are now theorems.

- `cc1_derived_valid`: under `TermK`, CC1 at every state of `apR K` iff `CC1VZ K` for every pair.
- `cc1_valid_derived_abs`: under `TermK`, `CC1VZ K` for every pair iff `CC1D` of `apR K` over
  `reps N C`, `N >= n + 2m` (through `derived_shaped`, `derived_ordinv` and `cc1_abs`).

`cc1_valid_abs` proves the transfer directly instead, for any relation `I` and without `TermK`.

**gsm's guarantee.** It is the guarantee of the table oracle (`TableCheck.check_tables_converges`):
event sequences that differ only by reordering adjacent independent events reach the same state.
Both rest on `Trace.run_tequiv`. `RunConvZ K I`: from every valid integer state, any two sequences
of events of the registry related by `tequiv` (trace equivalence for `I`) reach the same state
under `govK`.

- `gsm_abs_exact`: given `TermD K N` over the representatives (`N >= n + 2m`),
  `CC1VD K N I <-> RunConvZ K I`. The converse is the two-event case.
- `gsm_abs_sound`: given `TermD K N` and `CC1VD K N I`, gsm's runtime step `govK (apR K)` gives the
  same state for trace-equivalent sequences from every integer state of length `n`, the zero
  state included.
- `gsm_abs_sound_all`: with every pair checked, any permutation.

**Non-vacuity.**

- Capped inventory, `m = 1` (`capped_term`, `capped_cc1v_check`, `capped_idemv_check`,
  `capped_cc1_valid`, `capped_idem`, `capped_derived`, `capped_runtime`): every statement
  instantiated over the 7 representatives of `reps 3 [5]`. Restock is idempotent at every valid
  integer stock, and every permutation of restocks converges at run time from every integer stock.
- gsm's documented example, `m = 0` (`inventory_frag`, `inventory_reps`, `inventory_term`,
  `inventory_cc1v_check`, `inventory_idemv_check`, `inventory_runtime`, `inventory_idem`): stock,
  ship_a, ship_b; receive_a and receive_b copy a shipment level into stock when it is higher; cap 5.
  `N = n = 3`, 343 representative states. Every permutation of receive events converges from every
  integer state, and both events are idempotent at every valid integer state.
- A failure (`swapxy_frag`, `swapxy_check_fails`, `swapxy_not_idem`): `(x, y) := (y, x)` is in the
  fragment and not idempotent; the representative check reports it, and `(0, 1)` is an integer
  witness.

**Boundary.** `idem13_passes`, `idem13_diverges`, `idem13_refused`: "if z = 13 then swap x and y"
with 13 undeclared is idempotent at every representative state of `reps 3 []` and not at the
integer state `(0, 1, 13)`. `ord_frag []` refuses it; with 13 declared it is in the fragment and the
representative check fails, as it should.

| gsm step | Theorem |
|---|---|
| CC1 at the valid representative states, for the checked pairs | `cc1_valid_abs` |
| Runs converge from every integer state | `gsm_abs_sound`, `gsm_abs_sound_all` |
| The check is exact for runs from valid states | `gsm_abs_exact` |
| `NotIdempotent` from the representatives | `idem_valid_abs`, `idem_runtime_abs` |
| The repair-first registry is in the fragment | `derived_ordinv`, `oimap_comp` |
| The prose route | `cc1_derived_valid`, `cc1_valid_derived_abs` |

## Difference constraints (`DifferenceAbstraction.v`)

**When it applies.** The most common business arithmetic: "balance - amount >= 0",
"stock + restock <= cap", "reserved <= stock". The rules compare differences of two variables
against small constants, compare a variable against a constant, and write increments,
decrements, copies with an offset and constants. Every write saturates at the declared bounds,
as gsm's `Int` writes do. The result is a finite representative cutoff (route A): each condition
gsm checks holds over the full declared ranges iff it holds over a finite set of representative
states, whose size depends on the number of variables, the constants and the repair bound, not on
the widths of the ranges. Axiom-free.

**The model is gsm's.** A registry `dprog` has `n` integer variables, variable `i` declared in
`[lo_i, hi_i]`.

- Rules are gsm's combinators: expressions `V`, `Lit`, `Add`, `Sub`; comparisons `Le`, `Lt`, `Eq`,
  `Ne`, `Ge`, `Gt`; `And`, `Or`, `Not`.
- An event is a guard and a list of assignments applied left to right; it is a no-op when the guard
  is false. Events take no parameters.
- An invariant is a predicate and a repair transform. One repair step applies the first violated
  invariant's repair (`drepair`).
- Every write saturates at the target's bounds (`clampZ`, gsm's `SetInt`).
- The governed step `dgov K k` is the event followed by `K` repair steps. gsm's runtime step
  `drun K k` normalizes first. The states are the lists in range (`InBox`).

**The fragment** (`dfrag P A gam mu`, a boolean check). `norm` reads an expression as a difference
term `x_p - x_q + c` (at most one variable with each sign), or fails.

- Every comparison `a op b` reads as `(a - b) op 0`, and must normalize to one of:
  - `x_i - x_j op c` with `|c| <= gam`;
  - `x_i op a` with `a` an anchor (a constant in `A`);
  - a comparison of constants.
- Every write is `x_k := x_j + c` (increment, decrement, copy with an offset) or `x_k := a` with
  `a` an anchor.
- The offsets one transform adds sum to at most `mu`.
- Every bound `lo_i`, `hi_i` is an anchor. A saturating write compares `x_j + c` with a bound, so
  bounds act exactly like constants.

**The region relation.** Two states, together with the anchors, are related at threshold `W`
(`RelS W A`) when every pairwise difference of their values (anchors included) is either equal in
both states, or above `W` in both, or below `-W` in both. This is region equivalence for
difference-bound matrices, over the integers, with the anchors as fixed clocks.

- A guard whose constants have size at most `W` evaluates the same on related states (`atom_same`,
  `pred_same`).
- A write `x := x_j + c` keeps the relation with `W` lowered by `|c|` (`near_shift`). A saturating
  write is a comparison with an anchor first, so it does the same (`clamp_near`, `write_rel`).
- A governed step lowers `W` by `(K + 1) mu` (`dgov_rel`).
- The two sides of a CC1 instance run as one joint relation over both runs, so equality of the two
  final states transfers (`eq_transfer`, `cc1_pair`).

**Compression** (`compress_d`). Every state in range is related at `W` to a representative state:
a state in range with every variable within the radius `n(W + 1)` of some anchor (`RepS`,
`RepS_spec`). The proof is by pigeonhole (`pigeon`, `shift_step`): a variable farther than the
radius from every anchor sits in a block of values with no anchor, with `W + 1` free integers below
and above it. That block moves down by one, which keeps the relation. The sum of the values
decreases, so the moves stop at a representative.

| Condition | Threshold `W` (any larger `W` works) | Theorem |
|---|---|---|
| Validity | `gam` | `valid_pair` |
| Repair within `K` steps (`DTermBox`) | `gam + K mu` | `dterm_abs` |
| Idempotence of kind `k` at every valid state | `gam + 3(K + 1) mu` | `didemv_abs` |
| CC1 for the pairs of `I` at every valid state (gsm's CC1) | `gam + 4(K + 1) mu` | `dcc1v_abs` |
| CC1 for the pairs of `I` at every state | `gam + 4(K + 1) mu` | `dcc1_abs` |

Each row is an iff: the condition holds at every state in the declared ranges iff it holds at
every state of `RepS P A W`.

**Domain size.** `|RepS|` is the product over the variables of the number of values in
`[lo_i, hi_i]` that lie within `n(W + 1)` of an anchor (`RepS_length`). Each factor is at most
`|A| (2n(W + 1) + 1)` (`dom_length`). Every representative is a state in range, so a failure at a
representative is a failure of the declared machine. The witness is never outside the ranges, as
it can be in the comparison route.

**gsm's guarantee.**

- `dgsm_exact`: given repair within `K` steps over the representatives, CC1 for `I` at the valid
  representatives holds iff, from every valid state in range, trace-equivalent sequences of events
  reach the same state.
- `dgsm_sound` and `dgsm_sound_all`: the same for gsm's runtime step, from every state in range.
- `dbuild_sound`, end to end: from `dfrag`, `dterm_check` and `dcc1v_check` at `W = wcc1 gam mu K`,
  gsm's runtime converges from every state in range. The three boolean checks have exact
  specifications (`dterm_check_spec`, `dcc1v_check_spec`, `didemv_check_spec`).
- `dcheck_fail_real`: a failing check refutes CC1 over the ranges.

**The comparison fragment, recovered.** With no arithmetic (`gam = mu = 0`), every threshold is 0.

- `near0_compare`, `rel0_oiso`: at threshold 0 the relation is exactly the order type.
  `RelS 0 A s s'` holds iff some `f` with `OIso A s f` (`AbstractionCutoff.v`'s order isomorphisms
  fixing the constants) maps `s` to `s'`.
- The radius is `n`, the cutoff of `term_abs` and `cc1_abs` for `m = 0`, made two-sided around
  every constant. `reps_in_dom`: `reps n C` lies in the domain.
- `inventory_d_*`: gsm's documented example over `[0, 10^9]^3` at threshold 0, with `13^3`
  states.

**The threshold must cover chained increments** (`granularity_needs_chain`). In a registry with
`x, y, z` in `[0, 100]`, event A adds 3 to `x` twice (offset 6 in one event), and event B sets
`z := z + 1` when `x = y`.

- The states `(0, 6, 0)` and `(0, 7, 0)` are related at threshold `5 = 2 * 3 - 1`.
- CC1 of A and B fails at the first state and holds at the second.
- So a threshold below the chained offset does not transfer CC1: two increments by `c` need
  representatives `2c` apart.

`4(K + 1) mu` is a sufficient threshold. The least one is not mechanized.

### Boundaries

- **A difference guard fools the order-pattern check; this check reports it** (`gap_frag`,
  `gap_check_fails`, `gap_diverges`, `gap_order_check_passes`).
  - The rule: `x, y` in `[0, 10^9]`; A sets `x := y` when `y - x >= 2`; B sets `y := x` under the
    same guard.
  - In `AbstractionCutoff.v`'s language, the order-pattern check over `reps 2 [] = {0, 1}` passes,
    because the guard never holds there. The rule is outside `ord_frag`, and over the integers it
    diverges at `(0, 2)`.
  - The rule is in the difference fragment (`gam = 2`). The check over `RepS` at threshold 2
    fails, and `(0, 2)` is a state in range where A and B diverge.
- **`triangle_diverges` here** (`tri_not_difference`, `tri_refused`, `tri_diverges`).
  - The guard `x < y < z < x + y` compares `z` with a sum of two variables, which is not a
    difference constraint.
  - `dfrag` refuses the registry for every anchor set and threshold.
  - It diverges at `(2, 3, 4)`.
  - The reduction never reports it as converging. gsm can verify it only by enumerating a bounded
    range.
- **Outside the fragment: a sum of two variables** (`sum_refused`, `sum_check_passes`,
  `sum_diverges`).
  - The rule: `x, w` in `[0, 10^9]` and `y` in `[1000, 10^9]`. A sets `x := y + y`; B sets
    `x := x + 1` when `x = w`.
  - `dfrag` refuses it.
  - The representative check at the threshold the formula would give (4, counting the sum as an
    offset-free write) passes over the anchors `{0, 1000, 10^9}`.
  - The registry diverges at `(0, 1000, 2000)`, where every value is far from every anchor: a sum
    moves a value to a place no difference relation predicts.
  - Multiplication of variables is not in gsm's combinators at all.

### Non-vacuity

All examples are over ranges up to `10^9`, and all checks run by `vm_compute`.

- **Wallet** (`wallet_frag`, `wallet_reps`, `wallet_checks`, `wallet_deposits_converge`,
  `wallet_withdraw_diverges`, `wallet_repair_fires`).
  - Balance in `[-1000, 10^9]`, with -1000 the overdraft floor.
  - Events: deposit 5, deposit 20, withdraw 10 when balance >= 10, and a fee of 3. Invariant
    balance >= 0; repair balance := 0.
  - Anchors `{-1000, 10^9, 0, 10}`, `gam = 0`, `mu = 20`, `K = 1`, threshold 160: 657
    representatives.
  - The deposits converge, in any order, from every balance in range.
  - Deposit against withdraw is a real divergence, which the check reports. At balance 5, deposit
    then withdraw gives 0, and withdraw then deposit gives 10 (the guard fails first).
  - The fee overdraws at balance 1, and the repair restores 0.
- **Capped inventory** (`capinv_frag`, `capinv_reps`, `capinv_checks`,
  `capinv_restocks_converge`, `capinv_ship_diverges`).
  - Stock in `[0, 10^9]` with cap `10^6` (invariant stock <= 10^6, repair to the cap).
  - Events: restock 3, restock 7, and ship 2 when stock >= 2.
  - Threshold 56: 233 representatives.
  - The restocks converge. Restock against ship diverges one below the cap.
- **Reservations** (`reserve_frag`, `reserve_reps`, `reserve_checks`, `reserve_converges`,
  `reserve_release_diverges`).
  - `(stock, reserved)` in `[0, 10^6]^2`, invariant reserved <= stock, repair reserved := stock.
  - Events: restock 3, reserve 2, reserve 3, release 1 (saturating at 0), and reserve 1 when
    reserved < stock.
  - Threshold 24: `102^2` representative states.
  - The two reserves converge, and so do restock and release.
  - Reserve against release diverges when everything is reserved, at `(5, 5)`; so does the guarded
    reserve against release.

Under saturation, an increment and a decrement of the same variable never commute near a bound,
and guarded decrements never commute with each other near the guard. These pairs need ordering
(declared-only pairs, or the escrow results of `LocalTokenBalance.v`). The check finds them with a
witness in range.

### For gsm

The arithmetic route that gsm deferred, without a solver. This route is now modeled with
saturation and checked over a finite domain.

1. **Declaration.**
   - `Registry.Abstract()` as today. A registry whose rules use `Add` or `Sub` of a variable and a
     literal takes the difference route.
   - Constants need not be declared: the anchors are computed. They are every bound `lo_i`, `hi_i`,
     every literal a variable is compared against (`x op c`, also `x + d op c` as `c - d`), and
     every literal written (`x := c`).
   - The repair bound `K` is the least `K` up to a cap for which repair reaches validity within
     `K` steps over the representatives. Each `K` is exact (`dterm_abs`), and a larger `K` needs a
     larger threshold.
2. **What Build checks.**
   - `dfrag` on the combinator trees.
     - Normalize each comparison `a op b` as `a - b`: two variables with opposite signs and a
       constant, one variable and a constant (the constant becomes an anchor), or constants.
     - Normalize each assignment: a variable plus a constant, or a constant.
     - Compute `gam` (the largest `|c|` in a two-variable comparison) and `mu` (the largest sum of
       `|offset|` over one event's or one repair's assignments).
   - `W = gam + 4(K + 1) mu`; the radius is `R = n(W + 1)`.
   - The domain of variable `i` is the values of `[lo_i, hi_i]` within `R` of an anchor. Enumerate
     the product (`RepS`).
   - Run the existing checks over it, with the rules evaluated exactly as at run time, saturation
     included:
     - repair within `K` (`dterm_check`);
     - CC1 for the checked pairs at the valid representatives (`dcc1v_check`);
     - idempotence at the valid representatives (`didemv_check`; `gam + 3(K + 1) mu` suffices, so
       the same domain serves).
   - A pass is gsm's guarantee from every state in range (`dbuild_sound`).
   - A failure has a witness in range (`dcheck_fail_real`), so `AbstractWitness.InRange` is always
     true on this route.
3. **Representative-set size.**
   - `Π_i |D_i| <= (|A| (2R + 1))^n`. It does not depend on the widths of the ranges.
   - The wallet over `[-1000, 10^9]` has 657 states, and two variables over `[0, 10^6]` have
     `102^2`.
   - gsm's existing limit of `2^20` representative states applies; a larger domain is refused with
     its size.
   - Compositional checking (`CompositionalCheck.v`) splits footprint components first. Each
     component's `n` is what enters `R`.
4. **Refusals** (an `*AbstractionError` naming the rule).
   - A sum of two variables, or a variable with a negative sign in a write (`x := y + z`,
     `x := y - z`, `x := 5 - y`): `sum_diverges`.
   - Two variables with the same sign in a comparison (`z < x + y`): `tri_refused`,
     `triangle_diverges`.
   - Go closures, as today.
   - A representative domain over the limit.
5. **Report line.** "Verified by abstraction over balance (difference constraints; anchors
   {-1000, 0, 10, 1000000000}; threshold 160; 657 representatives)".
6. **Saturation.**
   - It is modeled exactly (`clampZ`), so the range-containment restriction that the comparison
     route needs ("a copied variable's range lies inside its target's") is not needed here.
   - The bounds are anchors, and the saturation comparisons are difference comparisons against
     them.
   - Values stay within the ranges plus `mu` during a step, so 64-bit arithmetic does not wrap
     for ranges within `±(2^62)`.
7. **Theorem per step.**

| gsm step | Theorem |
|---|---|
| Fragment check | `dfrag`, `norm_eval`, `frag_parts` |
| Representatives: every state in range compresses to one | `compress_d`, `RepS_spec`, `RepS_length`, `dom_length` |
| Repair within `K` over the ranges | `dterm_abs` |
| CC1 at the valid states, for the checked pairs | `dcc1v_abs` |
| `NotIdempotent` exact | `didemv_abs` |
| Runs converge from every state in range | `dgsm_exact`, `dgsm_sound`, `dgsm_sound_all`, `dbuild_sound` |
| Failure is real, witness in range | `dcheck_fail_real`, `RepS_spec` |
| Saturation | `clamp_near`, `write_box` |
| Refusals justified | `sum_diverges`, `tri_refused`, `gap_order_check_passes` |
| Threshold covers chained offsets | `granularity_needs_chain` |

## Difference constraints with event parameters (`DifferenceParams.v`)

**When it applies.** Events that carry integer arguments: "withdraw amount", "reserve qty",
"book n rooms", "set the cap to c". Each event kind declares its parameters, each with a range.
The difference route of the previous section extends to them, with one boundary that decides
which rules fit: a parameter added to a value must be **exact**, read as each of its values, and
its range is paid in the threshold. Axiom-free.

**The model.** `DifferenceAbstraction.v`'s registries, with parameterized events (`pprog`).

- Event kind `k` declares `m` parameters, parameter `j` in `[lo_j, hi_j]`. In its guard and
  effect, `DV i` reads variable `i` for `i < n` and parameter `i - n` for `n <= i < n + m`.
- Parameters are read-only. Writes saturate at the variable's bounds, as before.
- `pgov K k ps s`: event `k` with arguments `ps`, then `K` repair steps. `prun` normalizes first
  (gsm's runtime). The invariants read the variables only.
- `PInBox P s`: the state is in range. `PArgs P k ps`: every argument is in its declared range.

**The joint state.** A check of one event runs on `s ++ ps` (`n + m` coordinates); a CC1 check of
two events runs on `s ++ ps1 ++ ps2` (`n + m1 + m2`). `joint P l` places the events of `l` in the
joint state as an unparameterized registry of `DifferenceAbstraction.v`: each event reads its own
block of parameters (`jev`), and the invariants read only the variables (`clipI`). The joint
registry computes the parameterized one exactly (`jcc1`, `jidem`, `jvalid`, `jitr`), so every
transfer of the previous section applies to it.

**Does `balance := balance - amount` fit?** Not with `amount` as a coordinate, and yes with
`amount` exact.

- **As a coordinate, no, at any threshold.** `x + p` is a sum of two coordinates. The region
  relation compares differences of two values, and a sum moves a value to a place no difference
  predicts. `addw_no_threshold`: in a registry with `A(p)`: `x := x + p` when `x <> w`, and `B`:
  `z := 1` when `x = w`, for every threshold `W` the joint states `(W + 1, 2W + 2, 0; p = W + 1)`
  and `(W + 1, 2W + 3, 0; p = W + 1)` are in range and related at `W`. CC1 of `A` and `B` fails at
  the first and holds at the second. The representative check run that way passes and the
  registry diverges (`addp_check_passes`, `addp_diverges`).
- **As an exact parameter, yes.** A comparison or a write that is not a difference constraint
  with the parameters as coordinates (`fbA`, `fbW`: `x := x + p`, `x := x - p`,
  `reserved + q <= stock`) reads its parameters as their values. For each value it is then a
  difference constraint with a constant offset, in `dfrag`, and the value counts in `mu` (in a
  write) or in `gam` (in a comparison). The parameters it reads are the exact ones (`mask`).
- **Why exact is sound.** Related joint states agree on every coordinate whose range has width at
  most `2W` (`exact_eq`): its distances to both bounds cannot both exceed `W`. So a state and its
  representative carry the same exact arguments, and one unparameterized registry (`hat`, the
  exact values substituted) covers both.
- **The price.** The threshold must reach the exact parameter's magnitude. With amounts in
  `[1, 3]` and a balance in `[-1000, 10^9]`, the domain is independent of the balance's range.
  With amounts in `[0, 10^9]` the parameter is refused (`addw_refused`: accepted only if
  `2 (gam + mu)` covers the range). Below the range, related states differ on CC1
  (`exact_needs_width`).

Every other use of a parameter costs nothing: guards `x - p op c`, `p op a`, `x op p`, and copies
`x := p + c` keep the parameter a coordinate, abstract, with a range of any width.

**The fragment** (`pfrag P A gam mu`, a boolean check).

- `dfrag` holds for the registry without its events (`base P`).
- Every event writes only variables (`tgt_ok`).
- Every exact parameter has a range of width at most `2 (gam + mu)` (`exok`).
- For every value of the exact parameters (`sigs`), the joint registry of every event and of every
  pair of events is in `dfrag`, with the parameter bounds among the anchors.

**The transfers.** Each is an iff: the condition over all states and all arguments in the declared
ranges, against the joint representatives `RepS (jb P [k1; k2]) A W`, every coordinate (variables
and parameters) within `(n + m1 + m2)(W + 1)` of an anchor.

| Condition | Threshold `W` | Joint coordinates | Theorem |
|---|---|---|---|
| Repair within `K` steps | `gam + K mu` | `n` | `pterm_abs` |
| Idempotence of kind `k`, the same arguments twice, at every valid state | `gam + 3(K + 1) mu` | `n + m` | `pidemv_abs` |
| CC1 for the pairs of `I`, all arguments, at every valid state | `gam + 4(K + 1) mu` | `n + m1 + m2` | `pcc1v_abs` |

**Domain size.** `pcc1_domain_size`, `pidem_domain_size`: at most `(|A| (2R + 1))^N` with `N` the
number of joint coordinates and `R = N(W + 1)`. It does not depend on the width of any range,
the abstract parameters' included. `room_setcap_domain`: the pair (setcap, cancel), with
`c` in `[0, 10^9]`, has 4 coordinates and radius 76 at threshold 18.

**gsm's guarantee.** An event occurrence is a kind with its arguments.

- `pgsm_exact`: given repair within `K` steps over the representatives, CC1 for `I` at the valid
  joint representatives iff, from every valid state, trace-equivalent sequences of events with
  arguments in range reach the same state.
- `pgsm_sound`: gsm's runtime, from every state in range.
- `pbuild_sound`, end to end from `pfrag`, `pterm_check` and `pcc1v_check` at `W = wcc1 gam mu K`.
  `pbuild_perm`: with every pair checked in one orientation (`k1 <= k2`), any permutation
  (`tequiv_sym_cover`). `pidem_build`: idempotence from `pidemv_check`.
- The checks have exact specifications (`pterm_check_spec`, `pcc1v_check_spec`,
  `pidemv_check_spec`), and a failure is a real failure (`pcheck_fail_real`): its witness is a
  state and arguments in range.

**The special cases.**

- **No parameters.** `embed` reads a registry of `DifferenceAbstraction.v` as one whose events take
  no arguments. `embed_frag`: `dfrag` gives `pfrag`; `embed_cc1_box`, `embed_cc1_rep`,
  `pgov_embed`: the conditions coincide. `m0_special`: `dcc1v_abs` is `pcc1v_abs` with no
  parameters.
- **Threshold 0** (comparisons and copies only). `pradius0`: the radius of the joint box of two
  events is `n + m1 + m2`, which is `n + 2m` for `m` parameters each: the cutoff of `cc1_abs` and
  `cc1_valid_abs`. For one event it is `n + m`, the cutoff of `idem_valid_abs`. `preps0_in_dom`:
  `reps (n + 2m) C` lies in the domain, and at threshold 0 the relation is the order type
  (`rel0_oiso`), parameters included.

### Boundaries

- **`x := x + p` with `p` a coordinate** (`addw_no_threshold`, `addw_refused`, `addp_check_passes`,
  `addp_diverges`, `addp_refused`).
  - No threshold transfers CC1 (above).
  - `addp`: `x` in `[1000, 10^9]`, `w` in `[0, 10^6]`, `p` in `[1000, 10^6]`. With `p` a
    coordinate, the check of `(A, B)` at threshold 0 passes over 7600 joint representatives:
    `x + p = w` needs `w` near 2000, far from every anchor. At `(1000, 2000, 0)` with `p = 1000`
    the orders give `z = 1` and `z = 0`.
  - `pfrag` makes `p` exact and refuses it unless `2 (gam + mu) >= 10^6 - 1000`.
- **A sum of two parameters** (`sum2_check_passes`, `sum2_diverges`, `sum2_refused`):
  `x := p + q`, `p, q` in `[1000, 10^6]`. The check over 241920 joint representatives passes; at
  `(0, 2000, 0)` with `p = q = 1000` the registry diverges. `p + p` behaves the same.
- **An exact parameter's range is paid** (`exact_needs_width`): `x := x + p`, `p` in `[0, 15]`.
  The joint states `(20, 27, 0; 7)` and `(20, 27, 0; 8)` are related at threshold 6, and CC1 fails
  at the first and holds at the second. The registry is in the fragment with `mu = 15`.
- A sum of two variables, and a comparison of two same-signed variables, are refused as in the
  previous section.

### Non-vacuity

All over ranges up to `10^9`, checks by `vm_compute`.

- **Wallet, direct** (`wallet_p_frag`, `wallet_p_reps`, `wallet_p_checks`, `wallet_p_converges`,
  `wallet_p_set_idem`, `wallet_p_diverges`).
  - Balance in `[-1000, 10^9]`. Events: deposit(a), withdraw(b) when balance >= b, fee(f), amounts
    in `[1, 3]` (exact); set(v), `v` in `[-1000, 10^9]` (abstract). Overdraft repair to 0.
  - `gam = 0`, `mu = 3`, `K = 1`, threshold 24; 2754 joint representatives for two deposits;
    24964 for set at threshold 18.
  - Two deposits converge, and two fees converge, from every balance and all amounts. set is
    idempotent at every valid balance and every `v`.
  - The other pairs diverge at real states, which the check reports: the guard (balance 1,
    deposit 1, withdraw 2: 0 against 2); saturation at the upper bound (balance `10^9 - 1`,
    deposit 3, withdraw 3: `10^9 - 3` against `10^9 - 1`); the repair at the lower bound
    (balance 0, deposit 1, fee 3: 0 against 1); two withdrawals (balance 3, withdraw 2 and 3: 1
    against 0).
- **Wallet, events record facts, invariants derive outcomes** (`facts_frag`, `facts_reps`,
  `facts_checks`, `facts_converges`, `facts_flag`).
  - deposited and requested in `[0, 10^9]`, flag in `[0, 1]`. deposit(a): deposited += a;
    withdraw(b): requested += b; amounts in `[1, 2]`. Invariants: requested <= deposited or
    flag = 1; deposited < requested or flag = 0; each repair sets the flag.
  - 242208 joint representatives per pair at threshold 16. Every pair converges, so every
    permutation of deposits and withdrawals, any amounts, converges from every state.
  - The overdraft is an outcome the invariants derive, not a decision an event takes, so no
    pair needs ordering. Saturation at `10^9` loses the excess but commutes.
- **Inventory** (`stock_frag`, `stock_checks`, `stock_converges`, `stock_reserve_diverges`).
  - Stock and reserved in `[0, 10^9]`. restock(q): stock += q. reserve(q): reserved += q when
    reserved + q <= stock (a comparison of a sum: `q` exact, the guard reads
    `reserved - stock <= -q`). Invariant reserved <= stock. `q` in `[1, 2]`.
  - Restocks converge (97344 joint representatives). Two reserves diverge when stock runs short;
    reserve and restock diverge at an empty stock.
- **Room booking under a capacity** (`room_frag`, `room_checks`, `room_converges`,
  `room_diverges`, `room_setcap_domain`).
  - booked and cap in `[0, 10^9]`. book(n) when booked + n <= cap; cancel(n), saturating at 0;
    `n` in `[1, 2]`; setcap(c), `c` in `[0, 10^9]` abstract. Invariant booked <= cap.
  - Cancellations converge (97344 joint representatives). Two bookings diverge one room below the
    cap; booking and cancelling diverge at a full house; lowering the cap and cancelling diverge.

### For gsm

Events with arguments on the difference route.

1. **Declaring parameters.**
   - Each event kind declares its parameters by name and range: `Param("amount", 1, 3)`. A range is
     required, as for a variable. Rules read a parameter through a combinator `P("amount")`, which
     gsm compiles to the index `n + j`.
   - Invariants and repairs do not read parameters.
2. **Applying an event with arguments.**
   - `Apply(state, kind, args)`. gsm validates every argument against its declared range and
     rejects an out-of-range argument (the guarantee covers arguments in range: `PEv`).
   - The rules evaluate with the arguments read-only, writes saturate at the variables' bounds, then
     `K` repair steps, as for parameterless events (`pgov`, `prun`).
3. **What Build checks.**
   - Classify each parameter. Normalize every comparison and write with the parameters as
     variables. A parameter that occurs in one that is not a difference constraint is **exact**
     (`mask`); the others are **abstract**.
   - An exact parameter's range must be within `2 (gam + mu)`. The comparisons and writes it occurs
     in are normalized once per value of the exact parameters (`sigs`); `gam` and `mu` are the
     maxima over the values.
   - Anchors: the bounds of every variable and every parameter, and the literals, as before.
   - `W = gam + 4(K + 1) mu`. For each checked pair `(k1, k2)`: the joint domain over
     `n + m1 + m2` coordinates, each within `(n + m1 + m2)(W + 1)` of an anchor and inside its range
     (`RepS (jb P [k1; k2])`). Run CC1 at the valid joint representatives (`pcc1v_check`). For
     idempotence, the joint domain of one kind over `n + m` coordinates (`pidemv_check`). Repair
     within `K` over the variables alone (`pterm_check`).
   - A pass is gsm's guarantee for every sequence of events with arguments in range
     (`pbuild_sound`). A failure has a witness in range, state and arguments (`pcheck_fail_real`).
   - The joint domain grows with the number of coordinates, so compositional checking matters
     more here. A pair whose kinds touch disjoint footprints needs no joint check
     (`CompositionalCheck.v`).
4. **Refusals** (an `*AbstractionError` naming the rule and the parameter).
   - An exact parameter with a range wider than the threshold allows: "amount in [0, 10^9] is added
     to balance in withdraw; an added parameter is checked value by value; declare a narrower
     range" (`addw_no_threshold`, `addw_refused`, `addp_diverges`). The formula route of
     `AbstractionCutoff.v` takes such rules over unbounded integers, with a solver.
   - A sum of two parameters with a wide range, `x := p + q` or `x := p + p` (`sum2_diverges`,
     `sum2_refused`).
   - A sum of two variables, as before (`sum_diverges`, `tri_refused`).
   - A joint domain over gsm's limit, reported with its size.
5. **Report line.** "Verified by abstraction over balance (difference constraints with
   parameters; amount exact in [1, 3], v abstract in [-1000, 1000000000]; anchors {-1000, 0, 1, 3,
   1000000000}; threshold 24; 2754 joint representatives for deposit/deposit)".
6. **Theorem per step.**

| gsm step | Theorem |
|---|---|
| Joint state computes the parameterized rules | `jcc1`, `jidem`, `jvalid`, `jitr`, `tx_eval`, `txP_eval` |
| Exact parameters, substituted by value | `mask`, `hat_agree`, `hat_sigs`, `exact_eq` |
| Fragment check | `pfrag`, `pfrag_one`, `pfrag_two`, `base_parts` |
| Repair within `K` | `pterm_abs` |
| CC1 at the valid states, checked pairs, all arguments | `pcc1v_abs` |
| `NotIdempotent` exact, per kind and arguments | `pidemv_abs`, `pidem_build` |
| Runs with arguments converge from every state | `pgsm_exact`, `pgsm_sound`, `pbuild_sound`, `pbuild_perm` |
| Failure is real, witness in range | `pcheck_fail_real` |
| Domain size independent of the ranges | `pcc1_domain_size`, `pidem_domain_size`, `RepS_size` |
| Parameterless registries unchanged | `m0_special`, `embed_frag` |
| Refusals justified | `addw_no_threshold`, `addp_diverges`, `sum2_diverges`, `exact_needs_width` |
