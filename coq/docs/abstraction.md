# Abstraction: check relationships between values, not the values

Detailed results for the abstraction reduction over integer-valued state (roadmap item 8, step 2;
gsm roadmap item 1b), and its gsm instantiation. Each module's one-line summary is in the
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
representative set is claimed for the linear fragment. The repair must reach validity within a
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
