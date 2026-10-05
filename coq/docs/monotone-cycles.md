# Monotone cycles

Detailed results for monotone cycles: the least fixed point and chaotic iteration, the paper's
hypotheses, exact validity and reachability of the lfp, and event order checked per event and per
edge. Each module's one-line summary is in the [module index](../README.md#modules-by-regime); the
status of each question in this regime is in
[REGIME-AUDIT.md](../../REGIME-AUDIT.md#9-monotone-cycles-the-repair-normal-form), sections 9 and
10.

Two monotone-cycle modules share a section with another module and are on that module's page:
`ChaoticACC.v` (chaotic and Kleene iteration under ACC) with `GovernanceWF.v` in
[single-registry.md](single-registry.md#finiteness-only-for-checking-governancewfv-chaoticaccv),
and `FederationEventsCycles.v` (the global condition `GC` and gsm's cyclic normalizer) with
`FederationEventsConverse.v` in
[federation-events.md](federation-events.md#monotone-cycles-and-the-exact-converse-federationeventscyclesv-federationeventsconversev).

## Federated convergence (`Federation.v`)

The federated paper's deepest result (Thm. "Monotone Convergence Despite Cycles") says a
monotone federated repair operator on a product of complete lattices has a least fixed point
reached by Kleene iteration from bottom, on any topology including cycles. `Federation.v`
mechanizes the constructive, finite-lattice core the paper relies on ("the ascending chain
stabilizes for a finite lattice"), axiom-free:

- `iter_ascending` / `iter_below_fixed`: Kleene iteration from bottom is an ascending chain
  bounded by every fixed point.
- `kleene_lfp`: once the iteration stabilizes, the stable value **is** the least fixed point
  (the federated normal form) - existence and Kleene-reachability.
- `lfp_unique`: the least fixed point is unique, i.e. the limit is order-independent.

A concrete finite lattice (`bool`) with a monotone operator witnesses non-vacuity, with the
least fixed point computed (`bool_lfp_true`, `bool_lfp_value`). Deliberately avoids the
impredicative arbitrary-meet form of Knaster-Tarski, which would require excluded middle or
propositional extensionality, so the development stays axiom-free.

## Chaotic (asynchronous) iteration (`Chaotic.v`)

The other half of the monotone-cycles theorem: not only does the least fixed point exist, but
every FAIR ASYNCHRONOUS schedule of component updates from bottom converges to it, regardless of
order. That is the classical convergence of chaotic iteration (Cousot 1977), and it is what
"converges regardless of application order" means for a distributed system with no global clock.
`Chaotic.v` mechanizes it constructively, axiom-free, by reframing a chaotic schedule as a
PRODUCTIVE-update rewrite relation (a step that changes the state):

- `chaotic_terminates`: below the least fixed point a monotone update only moves up, so
  productive steps strictly increase a rank and are finite (the relation is strongly normalizing).
- `normal_is_lfp`: a state with no productive step is a fixed point of the whole operator, hence
  the least fixed point.
- `chaotic_reaches_lfp` / `chaotic_from_bot`: from bottom, any sequence of productive updates
  reaches the least fixed point.
- `chaotic_limit_unique`: every reachable normal form is the least fixed point, i.e. the
  destination is schedule-independent. This is the order-independence itself.

A concrete two-value instance (`bool_chaotic_reaches_lfp`) discharges every hypothesis and shows
the iteration from `false` reaches the fixed point `true`, axiom-free. The productive-step
reframing is what makes "every fair schedule" tractable without modeling infinite schedules: any
maximal run of productive updates terminates at the same unique fixed point.

## Monotone cycles against the paper's hypotheses (`MonotoneFederation.v`)

Completes the federation paper's "Monotone Cycles" section (PAPER-MAP rows F22, F23, F24, F27,
F31), axiom-free:

- F22, the repair operator built from a network: component states are (shared, local) pairs, a
  source keeps its own shared value, a target applies its resolver to its sources' current states
  (a single-source morphism is a one-source resolver). `fed_def_lattice_shared_cyclic_hyps`: if
  that `Phi` is monotone, every hypothesis of `FederationEventsCycles`' cyclic normalizer holds.
- F23, validity of the least fixed point. FALSE AS STATED: `fed_thm_monotone_cycles_lfp_invalid`
  is a 2-cycle of identity morphisms on `bool` (valid iff the flag is set) meeting every hypothesis
  of `thm:monotone-cycles` (complete lattice, `Phi` monotone, M1/R2, components WFC, CC vacuous),
  whose least fixed point is not federally valid; the cyclic normalizer even moves the valid state
  to it. M1/R2 transport validity but bottom need not be valid. Corrected with "every component is
  valid with bottom shared values": `net_iter_valid`, `net_sweep_valid` (any finite schedule),
  `net_lfp_valid` (under ACC), `net_Ncyc_correct` and `net_Ncyc_idem` (which discharges the
  former assumption `lfp_valid` of `cyc_N_idem`); non-vacuity `fed_valid_corrected_instance`.
- F23, the formula `s* = sup_k Phi^k(bot)`. FALSE without continuity:
  `fed_thm_monotone_cycles_kleene_formula_fails` on the complete chain `0 < 1 < ... < w < w+1`
  (`w_complete_nn`, completeness read classically as a double negation). Corrected:
  `kleene_sup_lfp`, `kleene_sup_valid`, non-vacuity `kleene_sup_instance`.
- F23, "all processors converge": `fed_thm_monotone_cycles_events_refuted` restates
  `cyc_counterexample` with `Phi` built from the network and every paper hypothesis discharged;
  `net_events_converge_iff` and `fed_thm_monotone_cycles_events_corrected` give the exact
  condition (GC).
- F24: `negation_not_monotone`; the corollary holds for the repair normal form only.
- F27, infinite lattices and widening: `kleene_sup_instance` (a continuous operator whose least
  fixed point is never reached in finitely many steps), `widening_sound` (a post-fixed point bounds
  every iterate and the least fixed point), `widening_not_normal_form` (a widened result need not
  be a fixed point, so it is not the federated normal form).
- F31, remark "Convexity and the monotone regime". FALSE AS STATED: `fed_rem_convexity_refuted`
  (a one-registry sub-federation whose repair is trivially monotone, while `rho_Fed^J` is the
  component's non-monotone normalizer). Corrected: `fed_rem_convexity_corrected` (phase 1 monotone
  and `Phi` monotone in the locals too), non-vacuity `convexity_corrected_instance`.

## Monotone cycles: exact validity and exact reachability of the lfp (`MonotoneExact.v`)

Closes the two section-9 rows of REGIME-AUDIT that had only sufficient conditions, on the network
model of `MonotoneFederation.v` (Phase-1 locals `l` fixed, `Phi l` the repair built from morphisms
and resolvers, `R2` and valid locals where stated). Axiom-free.

- Validity of the least fixed point, exact. `lfp_valid_iff_reached`: if the lfp `m` is reached by
  Kleene iteration (`m = Phi^K(bot)` for some `K`), then `m` is federally valid iff SOME Kleene
  iterate is valid. `lfp_valid_exact`: the same under ACC with no reachability hypothesis;
  `Ncyc_valid_exact`: for gsm's cyclic normalizer, per input `t`, the normal form is federally
  valid iff some Kleene iterate at `t`'s Phase-1 locals is valid. `fixed_valid_iff_images`: a fixed
  point is federally valid iff every target's image at that fixed point's own source states is
  valid (no R2, no monotonicity). The former sufficient condition (bottom valid) is the case
  `k = 0`: `net_lfp_valid_recovered`. It is not necessary: `bottom_validity_not_necessary`.
  The reachability qualifier is needed: `lfp_valid_iff_needs_reach` (on the chain `w+2`, R2 holds
  and every iterate is valid, but the lfp `w` is never reached and is invalid).
- gsm's check, stated exactly. `GsmCheck` is `verifyMonotoneVisited`'s validity test: for every
  target, every combination of visited source states and every visited target state, the target
  with the image written is valid, where a component's visited states are its valid local parts
  with any shared value (its valid states when no morphism writes it), `Vis`.
  `gsm_check_fixed_valid`: `GsmCheck` makes EVERY fixed point federally valid (valid locals; no
  R2, monotonicity or reachability needed), hence the lfp (`gsm_check_lfp_valid`) and gsm's
  normal form (`gsm_check_Ncyc_valid`, with no bottom-validity hypothesis). It is sound and not
  necessary: `gsm_check_not_necessary` (gsm rejects, bottom valid, lfp valid). Bottom validity and
  `GsmCheck` are incomparable (the two instances). The exact check is `ImageValidAt l m` at the
  computed lfp `m`, for every valid local combination `l`.
- Finite reachability, exact. `kleene_reach_exact` (given the stabilization test): the lfp is
  reached at a finite stage iff the Kleene chain is eventually constant iff productive Kleene steps
  from bottom are strongly normalizing (`SN kstep bot`) iff there is no infinite strictly ascending
  chain along the Kleene chain (`Acc chain_asc bot`); `kleene_reaches_iff` for a given lfp;
  constructive form without decidability `kleene_reach_nn`. Corollaries: `kleene_reach_of_acc`,
  `kleene_reach_of_acc_below` (ACC below any fixed point), `kleene_reach_of_finite_height`.
  Neither ACC nor ACC below the lfp is necessary: `acc_not_necessary`. `kleene_sup_not_sn`: the
  never-reached lfp of `kleene_sup_instance` fails the exact condition.
- Chaotic iteration on the network. `chaotic_reach_exact`: some finite chaotic schedule reaches the
  lfp iff Kleene reaches it iff gsm's round-robin sweeps reach it; `rounds_reach_by_kleene`: the
  round-robin needs no more rounds than Kleene needs steps. "Every schedule terminates" (strong
  normalization of productive coordinate updates) is strictly stronger:
  `chaotic_sn_strictly_stronger` (Kleene and the round-robin reach the lfp in two steps, while
  updating one coordinate alone climbs forever).

## Event order on monotone cycles, checked per event (`FederationEventsCyclesCheck.v`)

`FederationEventsCycles.v` ([federation-events.md](federation-events.md)) leaves `GC` global on a cycle. This file proves that a per-event condition
implies it, so a cyclic federation's event order can be checked without enumerating normal forms.

**Why it works.** gsm's `normalizeCyclic` resets every shared variable to bottom before the sweeps,
so the shared part of a normal form is a function of the locals alone. An event's writes to shared
variables are erased; only its effect on locals survives (`cyc_check_step`). Events therefore
commute after re-normalization as soon as their local outcomes do not depend on which image value
the shared part holds, and same-registry declared pairs commute on locals.

**Model.** Registries of any type with decidable equality; a federated state is (locals, shared
values) with per-registry lenses; `comp k s` is registry `k`'s component; `sig e` is the component
step (`Machine.Apply`), preserving component validity; `cev e` replaces registry `reg e`'s component
by `sig e` of it (locals and shared values); the normal form is `(fst (rho1 t), Lsh (fst (rho1 t)))`,
which is `Ncyc_with` of `FederationEventsCycles.v` for `Lsh l = kleene l js K bot`. `Hs j` is any set
of shared values for registry `j` containing every normal form's (for gsm: the images of the
morphisms into `j` over valid source states).

- **C1cyc**: for every event `e` of registry `j`, every valid component state `(x, h)` of `j` with
  `h` in `Hs j`, and every `h'` in `Hs j`, the locals of `sig e (x, h')` equal the locals of
  `sig e (x, h)`. This is gsm's C1, `ow(rho_B(e(ow(b, v'))), v') = ow(rho_B(e(b)), v')` for every
  image `v'` and valid consistent `b`: the final overwrite fixes the shared part on both sides, so
  the equation says exactly that the locals agree.
- **C2cyc**: for every declared-independent pair `a`, `b` of registry `j` and every valid `(x, h)`
  with `h` in `Hs j`, the locals of `sig a (locals of sig b (x, h), h)` and of
  `sig b (locals of sig a (x, h), h)` agree. This is the local part of gsm's C2 (both sides
  repaired with the same image `z`).

Results:

- `cyc_check_gc`, `cyc_check_converges` (headline): C1cyc and C2cyc imply `GC s0` and convergence of
  all trace-equivalent sequences, for every `s0` in the image of the normalizer. Hypotheses: phase 1
  fixes valid states, normal forms are valid (gsm checks this at run time), `Hs` contains the
  normal forms' shared values.
- `cyc_check_gc_lfp`: the same for gsm's Kleene normalizer `Ncyc_with` on a monotone cycle (the
  hypotheses of `cyc_N_lfp`), with `Hs j` any set containing the repair's output into `j` from valid
  states; "`Hs` contains the normal forms' values" is discharged from the least-fixed-point property.
- `footprint_c1`: the plain read footprint (an event's local outcome ignores shared values) implies
  C1cyc for every `Hs`. Writing shared variables is never a problem (the reset erases the writes).
- `lfp_commute_gc`: the global variant `N o ev e o N = N o ev e`, plus raw commutation of
  independent events, implies `GC`. Sufficient but not per edge (it quantifies over all raw states
  and runs `N`); the latch fails it.
- `cyc_check_instance` (non-vacuity): the two-registry cycle of `cyc_instance` with raise and clear
  events, plus `PingA`, which also writes A's shared flag, declared independent of `RaiseA`. Every
  hypothesis of `cyc_check_gc_lfp` is discharged, and `PingA; ClearA` from the bottom state ends at
  the bottom state (the shared write is erased).
- `check_rejects_latch`: `cyc_counterexample`'s federation is this model (`cev = xstep`
  pointwise), and for every `Hs` containing the normal-form shared values C1cyc fails at `LatchA`.
  The global variant of `lfp_commute_gc` fails too, and `GC xs0` fails.

Counterexamples to the other natural candidates:

- `monotone_c2_insufficient`: "monotone events plus C2 commutation" is false. `LatchA` is a monotone
  map on the component lattice, C2cyc holds (no declared same-registry pairs), each registry's own
  CC holds, and `GC` fails.
- `c1_localcc_insufficient`: "C1 plus each registry's own CC" is false, so C2cyc cannot be dropped.
  A genuine monotone cycle (A's shared flag fed by B, B's fed by A, every hypothesis of `cyc_N_lfp`
  discharged) where B has a shared slot whose only image is `false`. `Swap` exchanges B's local slot
  with the shared slot, `Audit` records their xor. C1cyc holds, the two events commute on B's full
  state, C2cyc fails, and `Audit; Swap` and `Swap; Audit` (one allowed swap apart) diverge from a
  normal form. Both events read a shared variable, so C1cyc is strictly weaker than the read
  footprint.

So candidate A of roadmap item 6 holds, with the qualification that matters: C1 and C2 must be
evaluated with the shared part ranging over a set that contains every normal form's shared values.
Images over valid source states (what gsm's C1 enumerates) satisfy this. The values the Kleene
iteration visits also contain them, so a check over visited states is sufficient too, but it is
stronger than needed (it adds non-image values such as bottom and can reject federations the image
check accepts). Neither condition is necessary: `GC` remains the exact one.

**What gsm has to check on an `AllowMonotoneCycles` network.** Nothing beyond its acyclic C1/C2
enumeration, with three requirements:

1. `H_j`, the image set of target `j`: for each edge into `j`, the morphism (or resolver) image of
   every valid source component state. Cost: one map evaluation per valid source state per edge.
   On a cycle the source's valid states must be enumerated in full (no topological restriction).
2. C1, per event `e` of `j`: for every local part `x` of a valid component state of `j` whose shared
   part is in `H_j`, the locals of `rho_j(e(x, v'))` are the same for every `v'` in `H_j`. Cost:
   `|E_j| x |X_j| x |H_j|` evaluations, `X_j` the distinct such locals. This is gsm's existing C1
   (`b` times `v'`). A C1 or C2 failure on a cycle means event order is not certified there, and the
   report should say so.
3. C2, per declared-independent pair on `j`: for every valid component state `(x, h)` with `h` in
   `H_j`, the two orders "event, overwrite with `h`, event" agree on locals. Cost: four evaluations
   per state per pair. This is gsm's existing C2.

Per-registry state spaces only, never the product: no normal form is enumerated. The exact
alternative (checking `GC` itself) enumerates the image of `N` (the product of the local spaces)
times every independent pair. Regression test: the `cyc_counterexample` latch federation must fail
C1 (`check_rejects_latch`). For a target with several incoming edges, gsm's per-edge C1 checks
overwrite each edge's variables separately; with M1 (overwrites preserve validity) they compose
into C1cyc for the target's whole shared part, one edge at a time. That composition step is not
mechanized here: the file treats each registry's shared part as one block. It is mechanized in
`FederationEventsCyclesMulti.v` (next section).

## Multi-edge targets: per-edge C1 composes (`FederationEventsCyclesMulti.v`)

**Model.** Registry `k`'s shared part is a product of components, one per incoming edge `p`
(`tgt p = k`), each with a lens `hget p` / `hset p` (get-set laws between distinct components of the
same target; two shared parts of `k` agreeing on every component of `k` are equal). `Hp p` is the
image set of component `p`: the image of edge `p`'s morphism over valid source states, or of a
resolver (below). `ProdImg k h` says every component of `h` lies in its image set; it plays the
role of `Hs k` in `FederationEventsCyclesCheck.v`.

- **C1edge p** (gsm's per-edge C1): for every event `e` of `tgt p`, every valid `(x, h)` with
  `h` in `ProdImg`, every `v` in `Hp p`: the locals of `sig e (x, hset p v h)` equal those of
  `sig e (x, h)`. Only component `p` varies; the others stay at their image values in `h`.
- **M1** (the validity hypothesis): for every `p`, valid `(x, h)` with `h` in `ProdImg` and `v` in
  `Hp p`, the state `(x, hset p v h)` is valid. Overwriting one component with one of its images
  preserves validity.

Results:

- `multi_edge_c1` (headline): `C1edge p` for every edge `p`, plus M1, imply C1cyc with
  `Hs = ProdImg`. The proof goes from `h` to `h'` one component at a time (`chainW`, `upd_full`);
  M1 keeps every intermediate state valid so the next per-edge check applies to it.
- `m1_necessary`: M1 cannot be dropped. Two components with full image sets, the only valid shared
  part is `(false, false)`, the local outcome is "both components are true". Every per-edge C1
  holds (one overwrite from `(false, false)` makes at most one component true), M1 fails, and
  C1cyc fails at `h = (false, false)`, `h' = (true, true)`.
- `multi_edge_c1_free`: the alternative without M1. If the per-edge check is run for every local
  part `x` (valid or not) with `h` in `ProdImg`, it implies C1cyc with no validity hypothesis.
- `resolver_joint_c1`: a component written by a resolver `r` from two sources with image sets
  `Im1`, `Im2`. Its image set is `R = { r a b | a in Im1, b in Im2 }` (or the image of `r` over the
  joint image of the source pair, a subset), and C1 for that component must range over `R`. It
  decomposes only through `r`: vary `a` over `Im1` with `b` fixed, then `b` over `Im2` with `a`
  fixed, every check evaluating the locals of `rho_j(e(x, r a b))` on the full input tuple, plus
  validity preserved by the first step (`Mr1`). Checking each source edge against its own
  morphism image is not sufficient.
- `resolver_edge_insufficient`: `r = plus`, `Im1 = Im2 = {0, 1}`, an event whose local outcome is
  "the component equals 2". C1cyc holds over `{0, 1}` (each edge's own image set), `2` is in `R`
  but in neither edge's image, C1cyc over `R` fails, and the per-input check through `r` fails
  (`0 + 1` to `1 + 1`).
- `resolver_instance` (non-vacuity): `Im1 = {0}`, `Im2 = {0, 1}`, the same event: every hypothesis
  of `resolver_joint_c1` holds, and the event reads the component (no read footprint).
- `multi_edge_gc`, `multi_edge_converges`: per-edge C1 for every edge, M1, C2cyc over `ProdImg`,
  and "every normal form has each component in its image set" imply `GC s0` and convergence for
  every `s0` in the image of the normalizer (`cyc_check_gc` with `Hs = ProdImg`).
- `multi_edge_instance` (non-vacuity): a cycle A <-> B in which both targets have two incoming
  edges. A's components are fed by B's two locals; B's by A's first local and by a closed slot
  (image `{false}`). `RaiseA1`, `RaiseA2` are declared independent, `PingA2` writes both of A's
  components, `ReadB` reads B's closed slot (so the read footprint fails). Every per-edge C1, M1,
  C2cyc and the normal-form hypothesis hold; `GC` and convergence follow.

**What gsm must check for a multi-edge target `j`.**

1. Per incoming edge `p` with its own morphism: `H_p`, the morphism image over valid source states.
   Per resolver component: `R`, the resolver applied to the joint images of its inputs (the
   product of the per-source images is a sufficient superset). The resolver's output set, not
   any single source's image, is that component's image set.
2. C1, per event `e` of `j` and per component `p` of `j`: for every valid component state `(x, h)`
   of `j` whose every component lies in its image set (all combinations, not only the components
   gsm enumerates for `p`), and every `v` in `p`'s image set, the locals of `rho_j(e(x, h[p := v]))`
   equal those of `rho_j(e(x, h))`. For a resolver component, `v` ranges over `R` (equivalently,
   one input of `r` at a time with the others fixed, evaluating `r` on the full tuple).
3. M1 for `j`: each such overwrite `h[p := v]` of a valid state stays valid. If gsm does not
   establish M1, it must instead run check 2 for every local part `x`, valid or not
   (`multi_edge_c1_free`).
4. C2 over the same set: for each declared-independent pair on `j` and each valid `(x, h)` with
   every component of `h` in its image set, the existing C2 check.

Without M1 the per-edge checks do not compose (`m1_necessary`); with it, they imply the whole-block
C1cyc and, with C2, `GC` on the image of `N`.
