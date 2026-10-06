# Symmetry: check one item, conclude for all

Detailed results for the symmetry reduction over keyed collections (roadmap item 8, step 1; gsm
roadmap item 1a). Each module's one-line summary is in the
[module index](../README.md#modules-by-regime). This is a reduction for checking, not a regime:
it does not change any gap in [REGIME-AUDIT.md](../../REGIME-AUDIT.md).

## Independent, identically governed items (`SymmetryCutoff.v`)

**When it applies.** The state is a collection of items (per product, per customer, per account)
governed by the same rules, and an event on one item reads and writes only that item. Axiom-free.

**The model.** An item registry is `(a, r, v, Phi)`: a per-item event `a e`, a repair step `r`,
an invariant `v` and a WFC potential `Phi`, with repair leaving valid items alone (`r_fix`). The
collection registry over `n` items, the lift, has states `l : list A` of length `n` (position `k`
is the item with key `k`), events `(k, e)` ("`e` at `k`") acting on item `k` only (`aL`), repair
acting on every item by the same `r` (`rL`), and the invariant the conjunction of the item
invariants (`validL`). Both registries are instances of `Governance.v`'s rewrite system with free
delivery, so `cc_exact_from` applies to each. Write `g e = rho* . a e` for the governed item step.

### Cutoffs

| Condition | Cutoff | Theorems |
|---|---|---|
| WFC (repair terminates) | 1 | `wfc_cutoff` |
| CC2 | 1 | `cc2_cutoff`, `cc2_cutoff_uniform` |
| CC1 alone (events in range) | 2, tight | `cc1_cutoff`, `cc1_cutoff_one`, `cc1_cutoff_uniform2`; tightness `cc1_cutoff_tight` |
| CC1 and CC2, so unique normal forms (`cc_exact_from`) | 1 | `cc_lift_iff`, `un_cutoff`, `un_cutoff_uniform`, `un_cutoff_global`; from in-range buffers `un_in_to_item` |
| At-least-once convergence; commutation and idempotence at reachable states | 1 | `alo_cutoff`, `alo_cutoff_exact`, `alo_cutoff_uniform`; governed steps from a valid start `alo_gov_cutoff` |
| Idempotence; declared independence | 1 | `idem_reduces`, `declared_cutoff` |
| Federation C1 and C2, morphism mapping items pointwise | 1 | `c1_cutoff`, `c2_cutoff` |

In plain terms, for a start `l0` with items `l0[k]`:

- `un_cutoff`: every event buffer from `l0` has a unique normal form iff, for every `k`, every
  event buffer from `l0[k]` has one in the one-item registry. `un_cutoff_uniform`: from
  `repeat s0 n` (`n >= 1`), iff from `s0`. `un_cutoff_global`: from every start, iff from every
  item state.
- `wfc_cutoff`: for `n >= 1`, the collection's repair has a WFC potential iff the item's does (the
  sum of item potentials, and conversely the potential of `repeat s n`).
- `cc1_cutoff`: CC1 for the collection (events with keys below `n`) iff, for every item, CC1 and,
  when `n >= 2`, `CC2star`: `g e (rho* s) = g e s` at every reachable `s` (repair then event equals
  event alone). So CC1 alone has the same truth value at every `n >= 2` (`cc1_cutoff_uniform2`) and
  at `n = 1` is the item's CC1 (`cc1_cutoff_one`). `cc1_cutoff_tight`: an item whose CC1 holds at
  one item and fails at two (and whose CC2 fails, which is what the second item exposes).
- `cc_lift_iff`: CC1 and CC2 together hold for the collection iff they hold for each item, because
  item CC2 implies `CC2star` along the repair (`cc2_star`). So the conjunction, and with it unique
  normal forms, has cutoff 1.

### Why cross-item pairs need nothing

- `same_item_reduces`: two events on the same item commute in the collection at `l` iff they commute
  in the item registry at `l[k]`.
- `cross_item_reduces`: events on different items `k1 <> k2` commute at `l` iff
  `g e1 (rho* l[k1]) = g e1 l[k1]` and `g e2 (rho* l[k2]) = g e2 l[k2]`: one state-descent
  obligation per item, no condition relating the two items.
- `cross_valid_commute`: at every valid state they commute with no hypothesis. At a reachable
  invalid state the obligation is the item's own CC2 (`cc2_star`).
- `cross_commute`: for the lifted run step (at-least-once), events on different items commute at
  every state.

### The hypotheses, made checkable

For an arbitrary registry `(aG, rG, vG)` over lists of length `n`:

- `IdGov` (independent and identically governed): an event at `k` writes only `k` (`ig_write`) and
  reads only `k` (`ig_read`); repair at `k` reads and writes only `k` (`ig_rread`); the rules are
  invariant under exchanging two keys (`ig_perm`, `ig_rperm`; transpositions generate every
  permutation); the invariant is the conjunction of the item invariants (`ig_valid`; aggregates fail
  it).
- `idgov_lift`: for `n >= 1`, `IdGov` iff the registry is the lift of its one-item restriction
  (`xa`, `xr`, `xv`: the registry on `repeat s n`, read at position 0). `lift_idgov`: every lift
  satisfies `IdGov`.
- `symcheck_decides`: on finite descriptions (enumerated item states and events) the boolean
  `symcheck` decides `IdGov`: sound and complete (`symcheck_spec`).
- `symmetry_sound`: if `IdGov` holds and the one-item restriction satisfies `r_fix` and has a WFC
  potential, the registry has unique normal forms from `l0` for every buffer of in-range events iff
  the one-item registry has them from each `l0[k]`. The transfer is `un_agree` (the registry and
  the lift have the same steps on in-range configurations).

### Boundaries

- **Aggregates** (`aggregate_diverges`, `agg_item_un`, `agg_one_item`, `agg_not_idgov`,
  `itemwise_converges`). Reserve adds one reservation to an item; the invariant is "total reserved
  across items is at most 1"; repair cancels a reservation on every positive item. On one item
  these are the item's rules (`agg_one_item`), and the one-item registry has unique normal forms
  from every state (`agg_item_un`). On two items, the buffer `[Reserve@0; Reserve@0; Reserve@1]`
  from `[0; 0]` reaches `[0; 0]` and `[1; 0]` (`aggregate_diverges`). `IdGov` fails at `ig_valid`
  (`agg_not_idgov`), so the check refuses the reduction. With the per-item invariant ("each item at
  most 1") the same events and item repair converge at every `n` (`itemwise_converges`). A
  cross-item invariant forces repair to touch items that are valid on their own, which is what
  `r_fix` and `ig_rread` exclude.
- **Different rules per item** (`nonidentical_misleads`, `nonidentical_not_idgov`). Item 0
  ignores its events; item 1 is set to 1 or 2. Checking item 0 says "converges"; the collection
  diverges from `[0; 0]` with `[(1, true); (1, false)]`. `IdGov` fails at `ig_perm`.
- **CC1 alone needs two items** (`cc1_cutoff_tight`), as above.

### Non-vacuity

Per-product inventory (`inventory_item_un`, `inventory_any_n`, `inventory_repair_fires`,
`inventory_idgov`): item state (stock, reservations, releases, backordered), events Restock,
Reserve and Release, invariant "backordered iff reservations exceed stock plus releases", repair
recomputes the flag. The item has unique normal forms from every state and buffer; through
`un_cutoff_global` so does a catalog of any size from any start; repair does fire (a Reserve with
no stock leaves the flag stale); the collection passes `IdGov` at every `n >= 1`.

### For gsm

The reduction gsm needs (gsm roadmap item 1a):

1. **Declaration.** A per-item registry template (variables, events, invariants, repairs of one
   item) and a key type (`Collection[ProductID](template)`); events are addressed as `e @ key`.
   Rules written in the template see one item only, so the lift is `IdGov` by construction
   (`lift_idgov`).
2. **Build.** Checks the one-item registry: WFC (`wfc_cutoff`), `r_fix` (repair leaves a valid item
   unchanged), and CC1 and CC2 as today. Unique normal forms for every catalog size follow
   (`un_cutoff_global`, `symmetry_sound`). A separate CC1-only report needs two items
   (`cc1_cutoff`); the at-least-once and declared-independence checks need one
   (`alo_cutoff_exact`, `declared_cutoff`).
3. **Refusal.** Any invariant, repair or event that reads more than one item (a sum, count, or
   comparison across keys) is an aggregate. gsm detects it syntactically in the declaration, and on
   finite descriptions semantically by `symcheck` at the declared size, and refuses the reduction,
   naming the rule (`aggregate_diverges`, `agg_not_idgov`).
4. **Report line.** "Verified by symmetry over ProductID (items independent; cutoff 1)", or
   "cutoff 2" when only the CC1 report is requested.
