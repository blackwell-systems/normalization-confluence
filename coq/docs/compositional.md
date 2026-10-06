# Compositional checking: check each footprint component, conclude for the registry

Detailed results for compositional checking by default (roadmap item 8, step 3; gsm roadmap item
1c). Each module's one-line summary is in the [module index](../README.md#modules-by-regime). This
is a reduction for checking, not a regime: it does not change any gap in
[REGIME-AUDIT.md](../../REGIME-AUDIT.md).

## Footprint components (`CompositionalCheck.v`)

**When it applies.** Every rule reads and writes a known set of variables, and the variables split
into components so that each rule's footprint (reads plus writes) lies in one component. This is
what gsm's `BuildCompositional` computes by union-find. Axiom-free.

**The model.** A registry over states `St` with variables `X`:

- `get s x` reads a variable. `mix C s t` takes `s` on `C` and `t` elsewhere. States are equal when
  they agree on every variable (`StateOK`).
- Events `A e` are guarded effects: a disabled event is the identity.
- Invariants `(chk i, rep i)` come in a declared order. One repair step `rho` fires the first
  violated invariant, as gsm does. `valid` holds when every invariant holds.
- Each variable has a component `blk x`. Each event and invariant has a component, `bE e` and
  `bI i`. A set `sh` of shared variables is allowed (see below); gsm's current model has none.

Footprints are separate read and write sets. An event has `RE e` and `WE e`. An invariant has a
check read set `RC i`, and its repair has `RR i` and `WR i`. `Local R W f` says that `f` changes
only `W`, and that its values on `W` depend only on `R`. `Inside k R W` says that `R` lies in
component `k` or the shared variables, and that `W` lies in `k` and is not shared. A guarded
event's read set includes its guard's reads, and also its write set, because a disabled event
leaves its write set as it was. `Hyps` bundles `StateOK`, `Local` and `Inside` for every event,
check and repair.

**gsm's guarantee.** gsm runs eager compensation. From a valid state, event `e` steps to
`G e s = N (A e s)`, where `N` repeats `rho` up to a repair bound `B`. That bound is
`BuildCompositional`'s `repairBound` (`WFCb B`: `B` steps reach a valid state from every state).
The guarantee, `Conv B`, is that every permutation of a list of events from a valid state reaches
the same state. This is the conclusion of `Checker.run_perm_invariant` over valid states, as in
`AstChecker.check_sound_converges`. gsm checks WFC and CC1 on valid states, not CC2
(gsm docs/theory.md, sections 6.5 and 9.3). `conv_iff_cc1`: `Conv B` holds iff CC1 holds at every
valid state, so the two checks gsm runs are exactly what its guarantee needs. `N_indep` and
`conv_indep`: neither `N` nor the guarantee depends on the bound, once it is one.

**The restriction to a component `k`.**

- `Sub k` is the set of states that agree with a background state `z` outside `k` and the shared
  variables. gsm holds the other variables at zero.
- `restrict k s` is the state in `Sub k` that agrees with `s` on `k` and the shared variables.
- The component's registry keeps only the invariants of `k` (`invK k`), with first-violated
  repair `rhoK k`, validity `validK k`, normalization `NK` and step `GK`.
- Its conditions over `Sub k` are `TermK`, `WFCk`, `CC1K` and `ConvK`.

### Decomposition

| Condition | Exact statement | Theorems |
|---|---|---|
| One repair step | a step of the registry is a step of exactly one component; the others are unchanged | `rho_step`, `iter_proj` |
| Termination from a state | terminates from `s` iff each component terminates from `restrict k s` | `term_iff`, `term_proj` |
| WFC | the registry terminates from every state iff every component does from every state of `Sub k` | `wfc_iff`, `wfcb_iff` |
| Repair bound | component bounds `d k` give the registry the bound `sum d k` (gsm's `repairBound`) | `bound_sum` |
| Raw effects, different components | commute at every state | `raw_cross_commute` |
| CC1, different components | holds at every valid state, with no check | `cc1_cross` |
| CC1, same component | holds at `s` iff the component's CC1 holds at `restrict k s`; over valid states iff over the valid states of `Sub k` | `cc1_same_iff`, `cc1_component` |
| gsm's guarantee | `Conv B` iff `ConvK k B` for every component | `compositional_exact`, `compositional_gsm` |

In plain terms:

- `compositional_gsm`: if every component terminates within `d k` repair steps from every state of
  its subspace, then the registry terminates within the sum. Every order of every list of events
  from a valid state then reaches one state iff, in every component, every order of that
  component's events from a valid state of its subspace does.
- `cc1_cross`: a pair of events in different components needs no check at valid states. At an
  invalid state it can fail (`Calculus.v`, `calc_components_cc1_iff`). gsm never applies an event
  to an invalid state, because `Machine.Apply` normalizes first.
- `term_iff` holds per state, and `wfc_iff` per registry. Only the components that have
  invariants (the list `Ks`) take part.

**The cost.** `comp_check` is a boolean check. For each component `k` in `Ks`, it enumerates
`Sub k` (`enumSub`): every assignment of the component's own and shared variables, with the
background elsewhere. Over those states it checks:

- that `d k` repair steps reach validity (`wfc_check`);
- CC1 for every ordered pair of the component's events at every valid state (`cc1_check`).

The results:

- `comp_check_exact`: `comp_check d` passes iff every component terminates within `d k` and
  `Conv (sum d)` holds.
- `wfc_check_exact`, `cc1_check_exact`: each check decides its condition.
- `enum_length`: component `k` costs `|D|^(n_k)` states, where `n_k` counts its variables. The
  total is the sum over components, not `|D|^|X|`.

**gsm's literal check.** gsm checks a component with global rules on states whose other variables
are zero, and it requires the zero state to be valid.

- `gsm_literal`: with no shared variables and a valid background, global validity and repair on
  `Sub k` are the component's.
- `gsm_literal_iter`, `gsm_literal_step`: so are repair runs and steps.

So `verifyComponentWFC` and `verifyComponentCC` compute `WFCk` and `CC1K` exactly. The theorems
above do not assume a valid background; the component's own validity is enough.

### Shared variables

A variable may be shared by several components when no event and no repair writes it. `Inside`
requires write sets to avoid `sh`, and each component's subspace includes the shared variables.
Every theorem above holds as stated with shared read-only variables. Writing a shared variable is
not allowed (`sw_diverges` below), and the exact requirement is that the writer and the readers
are checked together: in gsm terms, their components merge.

### Combinator rules: footprints extracted and proved

Over `AstChecker.v`'s grammar, which models gsm's combinators:

- `readsE`, `readsP`, `readsT` and `writesT` extract the variables that an expression, predicate
  or transform reads, and the variables that a transform writes. They are gsm's `vars`, `readVars`
  and `writeVars`.
- `evalE_reads` and `evalP_reads`: an expression or predicate depends only on its extracted reads.
- `applyT_writes`: a transform writes only its targets.
- `applyT_reads`: a transform's values on a read-closed set depend only on that set. Assignments
  are sequential, so a later assignment may read an earlier one's target.
- On valuations of a fixed length, `ast_event_local`, `ast_check_local` and `ast_repair_local`
  give `Local` and `PLocal` for guarded events, checks and repairs. The read set of a guarded
  event is the guard's reads plus the effect's reads plus its writes.
- `ast_hyps`: the decidable `blocks_ok` checks a component assignment against the extracted
  footprints. If it passes, the induced registry `astReg` satisfies `Hyps`. gsm can run the same
  check on its union-find result.
- `ast_rho_repair1`, `ast_N_normalize`: `astReg`'s repair and normalization are `AstChecker`'s
  `repair1` and `normalize`, the verified rules oracle's.
- `ast_demo`: a two-component machine that `blocks_ok` accepts.

**Trust boundary.** Closures are opaque. gsm tests their footprints by perturbation (one and two
outside variables, at every value, from every state of the component), and the caller opts in with
`TrustClosureFootprints`. That test is not proved here and cannot detect a joint dependence on
three or more outside variables. For closures, the hypotheses of the decomposition are tested, not
proved, as gsm's report states (`AssuranceOracleComponentsTested`).

### Boundaries

Each counterexample breaks one hypothesis while all the others hold. In each, the boolean
per-component check passes, every component's `WFCk` and `ConvK` hold, and the registry diverges.

- **Writes-only footprints, the pay/ship pattern** (`ws_other_hyps`, `ws_ship_not_local`,
  `ws_check_passes`, `ws_components_pass`, `ws_wfc`, `ws_diverges`).
  - Setup: pay writes `paid`, and ship (guarded on `paid`) writes `shipped`. Each footprint is its
    write set, so they sit in separate components.
  - Result: from the zero state, pay then ship ships, while ship then pay does not.
  - The broken hypothesis is ship's locality, because its guard reads `paid`.
  - `ws_true_footprint`: with the read in the footprint, ship is local, the split no longer fits,
    and `inside_merge` forces `paid` and `shipped` into one component. This is why reads must be
    in the footprint.
- **Repair crossing components** (`rc_other_hyps`, `rc_repair_not_local`, `rc_check_passes`,
  `rc_components_pass`, `rc_wfc`, `rc_diverges`).
  - Setup: an invariant on `stock` ("not 2") is declared in stock's component, but its repair also
    sets `reserved`, in the other component.
  - Result: from the zero state, raising stock and then setting `reserved := 2` ends with
    `reserved = 2`. The other order ends with `reserved = 1`.
  - This is why repair must stay inside its component. gsm's `verifyFootprints` checks it.
- **A shared variable written** (`sw_other_hyps`, `sw_pay_writes_shared`, `sw_check_passes`,
  `sw_components_pass`, `sw_diverges`).
  - Setup: `paid` is shared. Ship reads it, so its footprint is local and inside its component,
    but pay writes it.
  - Result: the same divergence as pay/ship.
  - This is why shared variables must be read-only.

### Non-vacuity

The store (`shop`) has two components and an optional shared flag.

- **Orders:** status and paid. Pay sets paid. Ship sets status to shipped. The invariant
  "shipped implies paid" is repaired by charging.
- **Inventory:** stock, reserved and a backorder flag. Reserve and restock are capped increments.
  The invariant "flag = reserved > stock" is repaired by recomputing the flag.
- **The shared flag:** with `g = true`, ship and reserve are guarded on a store-open flag. Both
  components read it, and no event or repair writes it.

What the module proves:

- `shop_hyps`, `shop_fin`: the hypotheses hold for both variants.
- `shop_check`: the boolean check passes.
- `shop_converges`: WFC within 2 steps, and gsm's guarantee.
- `shop_repair_fires`: shipping unpaid, and reserving beyond stock, both violate an invariant.
- `shop_cost`: 9 + 27 states without the flag, or 27 + 81 with it, instead of the 729 of the
  product.
- `shop_gsm_literal`: without the flag, gsm's literal component check is the component check.
- `shop_shared_read`: with the flag, the shared variable is read by both components and written by
  none.

### Not covered

- CC2 and unique normal forms of the governance rewrite system (`cc_exact_from`). gsm does not
  check CC2, and its runtime does not need it.
- Declared independence: the CC1 decomposition (`cc1_cross`, `cc1_same_iff`) holds for each pair,
  so a check restricted to declared pairs decomposes too. The permutation guarantee is stated for
  all pairs.
- Composition with symmetry and abstraction is not mechanized here. Each component is an ordinary
  registry over `Sub k`, so steps 1 and 2 apply to a component whose model fits them, but no
  combined theorem is stated.

### For gsm

The reduction gsm needs (gsm roadmap item 1c):

1. **Default path.**
   - `Build` computes components first, by union-find over each rule's footprint (reads plus
     writes, as now).
   - With more than one component, and each component within the size limit, it runs the
     per-component check. Otherwise it runs today's global enumeration.
   - The reduction is exact (`compositional_exact`, `comp_check_exact`). So a pass is the
     guarantee, and a failure in a component is a failure of the registry.
   - The component's witness `t` is a valid state of the registry when the background is valid.
     In general the witness is `N t` (the proof of `cc1_component`).
2. **Conditions per component.**
   - WFC from every state of the component's subspace, recording the deepest chain `d k`
     (`wfc_iff`). The machine's repair bound is the sum (`bound_sum`), which is today's
     `repairBound`.
   - CC1 for every pair of events in the component, at the valid states of the subspace
     (`cc1_component`).
   - No check for pairs in different components (`cc1_cross`).
   - No CC2, as today.
3. **Footprints.**
   - An event's footprint is its reads (guard and effect) plus its writes. An invariant's
     footprint is its check's reads plus its repair's reads and writes.
   - For combinators, gsm can derive the event footprint as `readsP` plus `readsT` plus `writesT`
     instead of refusing an event whose reads fall outside `Writes`. Either way the union-find
     sees the reads. The extraction is proved (`ast_event_local`, `ast_check_local`,
     `ast_repair_local`), and `blocks_ok` certifies the component assignment (`ast_hyps`).
   - Closures stay behind `TrustClosureFootprints`, tested by perturbation and not proved.
4. **Validity per component** (optional). gsm now requires the zero state to be valid and checks
   global rules on the zero background, which is exact (`gsm_literal`). Checking each component
   with its own invariants instead (`validK`, `rhoK`) gives the same results and drops the
   zero-state precondition. The decomposition theorems do not assume a valid background.
5. **Shared read-only variables** (optional extension). A variable that no event and no repair
   writes can be read by several components without merging them. Include it in each reading
   component's subspace and use per-component validity. A write to a shared variable merges the
   components (`sw_diverges`).
6. **Refusals.** Each refusal has a counterexample behind it, and gsm names the rule.
   - A rule whose reads are not in its footprint (`ws_diverges`).
   - A repair or effect that writes outside its footprint (`rc_diverges`). gsm checks this in
     `verifyFootprints`.
   - A write to a shared variable, if the extension is adopted (`sw_diverges`).
   - A closure without `TrustClosureFootprints`.
   - A component over the size limit: fall back to `Build` or report it.
7. **Report line.** Two examples:
   - "Verified compositionally: 3 components (largest 2^9 states; 1,536 states checked instead of
     2^30); 41 cross-component pairs need no check (disjoint footprints, reads included);
     footprints checked exactly (combinators)."
   - With closures, the same line ending "footprints tested by perturbation
     (TrustClosureFootprints)".

| Guarantee | Theorem |
|---|---|
| WFC from per-component WFC; the repair bound | `wfc_iff`, `bound_sum` |
| Cross-component pairs need no check | `cc1_cross` (raw: `raw_cross_commute`) |
| Same-component pairs checked on the component | `cc1_same_iff`, `cc1_component` |
| The guarantee is CC1 on valid states | `conv_iff_cc1` |
| Registry iff components | `compositional_exact`, `compositional_gsm` |
| The enumerating check is exact, and its cost | `comp_check_exact`, `enum_length` |
| gsm's zero-background check is the component check | `gsm_literal`, `gsm_literal_step` |
| Combinator footprints are sound | `ast_event_local`, `ast_check_local`, `ast_repair_local`, `ast_hyps` |
| Refusals justified | `ws_diverges`, `rc_diverges`, `sw_diverges`, `inside_merge` |
