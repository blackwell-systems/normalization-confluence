# Canonical execution (experimental)

> **Experimental: validation in progress.** This page records a research experiment. Do not cite
> these results yet. Nothing here changes what [REGIME-AUDIT.md](../../REGIME-AUDIT.md) or the
> papers state; the modules only rederive existing exact theorems through a common kernel and
> record where that works and where it does not.

Modules: `CanonicalExecution.v` (the generic kernel), `CanonicalInstances.v` (the six
validation criteria) and `CanonicalLocality.v` (the P layer, interaction locality, and the rerun
of criterion D). All three are axiom-free and in `verify.sh`'s gate. The module index rows are in
the [infrastructure table](../README.md#infrastructure-docsinfrastructuremd).

## The hypothesis under test

Convergence of governed execution decomposes into three layers:

- **E, effective canonicalization**: the dynamics settles (Settlement), and the settled
  configurations it reaches are the canonical ones designated by a canonicalizer `N`
  (CanonicalFidelity).
- **S, state descent**: an event's canonical outcome does not depend on whether it acts on a raw
  state or on its canonical form, `N (act e s) = N (act e (N s))`.
- **H, history descent**: the canonical semantics is constant on the semantic equivalence classes
  of executions.

A fourth, compositional layer **P** has two halves: state gluing (`SheafGluing.v`, a separate
module) and interaction locality (`CanonicalLocality.v`, [below](#the-p-layer-interaction-locality-canonicallocalityv)).

## The kernel (`CanonicalExecution.v`)

Canonicalizers. `N` idempotent, `canon_equiv x y := N x = N y`.

- `state_descent_iff_respects_canon`: `StateDescent` (for all `e`, `s`,
  `N (act e s) = N (act e (N s))`) iff every `act e` respects `canon_equiv`.
- `normalization_descent`: `StateDescent -> N (rawrun w s) = grun w (N s)`, where `grun` runs the
  governed step `gact e s := N (act e s)`; `normalization_descent_from` needs `StateDescent` only
  at the states the raw run reaches from `s0`.
- `state_descent_iff_cc2`: with `N := rho*` built from WFC (`RhoStar.v`), `StateDescent` is
  exactly CC2. This is `RhoStar.strong_absorption_iff_cc2` read in the new vocabulary.

Rewrite presentations. A step relation `R` and a start `c0`.

- `peak_exact`: `SN R c0 -> (CR R c0 <-> every peak at a configuration reachable from c0 is
  joinable)`. This is Newman's Lemma localized to the reachable part, by
  `GovernanceConverse.newman_on`, in the form `EnabledAfterComp.cr_iff_critical` proves for the
  governance rewrite system.
- `classified_peak_exact`: a classifier assigns each reachable non-trivial peak a kind
  (`StatePeak`, `HistoryPeak`, `StructuralPeak`); if the classifier is complete,
  `SN R c0 -> (CR R c0 <-> StatePeaks join /\ HistoryPeaks join /\ StructuralPeaks join)`.
  `empty_kind_joins` drops a kind with no member.

Execution equivalence. Admissible executions are elements `t` of an execution type with `Adm t`
(for example, a delivery order together with the fact that it is causally consistent). Generators
`G` relate admissible executions. `AC` is the reflexive, symmetric and transitive closure of `G`
in which every vertex is admissible: there is no context rule and no free word.

- `history_descent_exact`: under presentation adequacy (on admissible executions, the semantic
  equivalence is exactly `AC`), a semantics is constant on semantic classes iff it is constant
  across each generator edge. Semantic values are compared up to any equivalence relation.

Effective canonicalization. A configuration system with raw actions (each one an event, or an
internal action that preserves `N`), admissible action words, flush words, a settledness predicate,
a canonicalizer `N` and a history equivalence `EqH` on event words; the canonical semantics runs
the governed step from `N s0`.

- `canonical_execution_exact`: under Settlement, (every settled run agrees with the canonical
  semantics, and settled runs with `EqH`-equivalent events agree) iff CanonicalFidelity and
  StateDescentR (state descent at every reachable configuration) and HistoryDescentC.
- `esh_exact`: Settlement and agreement and convergence iff `E /\ S /\ H`.
- `esh_sufficient`: the backward direction needs no Settlement.

## The six criteria (`CanonicalInstances.v`)

Line counts are for the instance's own proofs; "glue" is the instance-specific material the kernel
does not supply.

| | Existing result | Kernel theorem used | Outcome | Evidence |
|---|---|---|---|---|
| A | `GovernanceConverse.jc_exact`, `EnabledAfterComp.jcg_exact` | `classified_peak_exact` | PASS | `jc_exact_kernel` (14-line proof), `jcg_exact_kernel` (12-line proof). Event/compensation peaks are StatePeaks, distinct event/event peaks HistoryPeaks, compensation/compensation trivial, StructuralPeak empty. Shared glue (about 65 lines): the classifier and its completeness (`gov_complete`, a case analysis on the two rules), and two class-join lemmas (`gov_state_joins`, `gov_history_joins`) that translate JC's repaired form (`rho*` after each event) into joins of the raw peak. `jc_exact` additionally needs `enabled_after_comp` to reach JC's comparison target; `jcg_exact` does not. |
| B | `GovernanceConverse.causal_exact` | `history_descent_exact` | PASS | `causal_exact_kernel` (4-line proof). Generators: adjacent concurrent swaps at a causally consistent prefix (`cswap`). Adequacy `causal_adequate` (8 lines) from `CausalReplay.causal_tequiv`, `GovernanceConverse.tequiv_causal` and `causal_swap` via `swaps_connect`; the generator condition is CCR (`causal_gen_iff`, 12 lines). |
| C | `AtLeastOnceExact.alo_exact`, `causal_alo_exact`, `causal_alo_exact_idem` | `history_descent_exact` | PASS (the adequacy proof is the cost) | `causal_alo_exact_idem_kernel` and `causal_alo_exact_kernel` (3-line proofs), `alo_exact_kernel` (5 lines, the instance `hb` empty). Generators: the swaps of B plus one duplicate generator at its legal landing point. `dup_idem`: a copy right after its first delivery, which ends an exactly-once causal prefix; its edge condition is exactly `IdemAt` (`gen_idem`). `dup_abs`: a copy at the end of an exactly-once causal run that holds it and none of its causal successors; its edge condition is exactly `AbsorbAt` (`gen_abs`). The swap edge condition is exactly `CCRon` (`gen_swap_ccron`). Adequacy (`alo_adequate` and its lemmas, about 250 lines, proved once for any generator set containing the swaps plus a one-redelivery closing obligation) is pure word combinatorics with no semantics: `abs_close` closes a redelivery with one edge, `idem_close` first moves the earlier copy right past concurrent events (`move_right`), the combinatorial shadow of the semantic lemma `idem_absorb`. A naive `aa = a` generator at every prefix does not work: its edge condition is idempotence at prefixes with duplicates, which is not the published local condition and reduces to it only through the absorption argument the generator was meant to replace. |
| D | `FederationEventsConverse.fed_exact` | `history_descent_exact` | PARTIAL in the first run; PASS on the rerun with the P layer (see [below](#criterion-d-rerun)) | `fed_exact_kernel` (7-line proof). The history layer goes through the kernel: trace convergence iff commutation at each reachable independent swap (`fed_adequate`, `fed_gen_iff`, using `FederationEvents.runF_ext`). C1R1 is reachable state descent of the overwrite canonicalizer `N_{j,z} := f j z` (`c1r1_state_descent`; `N_{j,z}` is idempotent on valid states, `overwrite_canonicalizer`), and C2R is the one-swap history condition of the local governed run (`c2at_history`). The glue the kernel cannot supply is the split of a swap's commutation into C1R1 and C2R: that is the model's locality lemma `FederationEventsConverse.gc_iff_reach` (via `pair_commute`, about 100 lines of topological solving), used as is. See "The leak" below. XU, `XUat` (so XUR) and XUc are state descent on larger exposure domains: `xu_state_descent` (every valid target state), `xuat_state_descent` (stale distributed states), `xuc_state_descent` (cycle states, `N := Nc`). |
| E | `StreamExact.pjc_exact`, `stream_exact`, `stream_exact_free` | `classified_peak_exact`, `history_descent_exact` | PASS | `pjc_exact_kernel` (10-line proof). The processor discipline applies an event only from a valid state, so the StatePeak (an event step against a compensation step) has contradictory premises: `stream_state_peaks_empty`. Confluence is the HistoryPeak condition PJC alone. `stream_exact_kernel` (15 lines) is `stream_exact` with `pjc_exact` replaced by the kernel route; the processor-to-reduction glue (`stream_agree_set_function`, `sx_un_cr`, `sx_nf_empty_progress`) is reused from `StreamExact.v`. Under free delivery, `stream_free_history`: stream agreement iff history descent of the governed run from `rho* s0` over duplicate-free reorderings (PCC is the swap edge condition, `pcc_gen_iff`). This last one rereads `stream_exact_free` rather than rederiving its processor half. |
| F | `DistributedCyclesExact.flush_fed_iff` and the ghost family | `esh_exact` | PASS | `flush_fed_iff_kernel` (5-line proof): Settlement is FlushR, CanonicalFidelity is NoGhostR, StateDescentR is XUcR, HistoryDescentC is `FMConv (Nc s0)`. The glue is six translation lemmas (`d_settle`, `d_fidelity`, `d_state_descent`, `d_history`, `d_agree`, `d_conv`), each a few lines from `Nc_fst`, `fst_Nc`, `Nc_idem`, `quiet_normal`, `Nc_eq`. The kernel route needs none of the order, rank or cover hypotheses of `DistributedCyclesExact`'s section (the content was already order-free in `DistributedCycles.quiet_agree_iff`). Ghost family: `flip_esh` (Settlement fails alone), `ghost_esh` (CanonicalFidelity fails alone), `conv_ghost_esh` (H and convergence hold without E: Fidelity fails, so agreement fails), `copy_xu_esh` (S fails alone), `fm_conv_esh` (H fails alone); each failure of agreement is derived through `flush_fed_iff_kernel`, not cited. `raise_only_esh`: all three layers hold together (non-vacuity). |

## The leak (criterion D, first run)

This section records the first run. The P-layer theorem it asks for is now in
`CanonicalLocality.v`; the rerun is [below](#criterion-d-rerun).

The kernel's state descent is for one canonicalizer `N` over one state space. In a federation the
canonicalizer is a family `N_{j,z} := f j z` indexed by the target registry `j` and the image `z`
of its sources, and an event changes one component and then every downstream component is
re-solved. Whether a cross-registry swap commutes at a reachable state is then equivalent to state
descent of the target's local canonicalizer (`C1at`) at that state, but proving this needs:

1. locality: an event on `j` changes nothing outside `j` and the registries after `j`;
2. topological solving: the re-normalized state is the unique solution of the component equations
   (`solve_unique`), so two solutions agree when they agree component by component.

Neither is expressible in E/S/H: they are statements about how a global canonicalizer `N`
decomposes into local canonicalizers along a dependency order, which is the compositional layer
P. Proposed fix: add to the P layer a gluing theorem of the form "for a component-wise system with
local canonicalizers `N_{j,z}`, solved in a topological order, a swap of events on different
components commutes at a reachable state iff each target's local state descent holds there, and a
swap on one component commutes iff the one-swap history condition of its local governed run
holds" (`FederationEventsConverse.reach_commute_iff` as the instance). With that theorem in the
kernel, D would be: kernel history layer, then the P-layer split, then the two definitional
identifications above.

## The P layer: interaction locality (`CanonicalLocality.v`)

The topology is kept out of the generic theorem. It is a factorization of global obligations
through a composition boundary; the acyclic federation is one instance, and there the topology
(acyclicity, topological solving) is what proves the instance's obligation.

### The generic theorem (section `Factorization`)

There are three kinds of ambiguity, each with an "exposed" predicate (the ones a run can reach)
and a "resolved" predicate: global ambiguities `g` (`GAmb`, `RG`), local ambiguities `l` inside
one component (`LAmb`, `RL`), and interface ambiguities `i` across the boundary (`JAmb`, `RJ`).
A decomposition `DL g l`, `DJ g i` lists the local and interface ambiguities a global one is made
of. Write `GlobalRes`, `LocalRes`, `InterfaceRes` for "every exposed ambiguity of that kind is
resolved", and `Components g` for "every component of `g` is resolved".

- `LCExposed`: a component of an exposed global ambiguity is exposed.
- `LCSound`: an exposed global ambiguity whose components are all resolved is resolved.
- `LC` (locality completeness) is `LCExposed /\ LCSound`.
- `Realizable`: every exposed local (interface) ambiguity is forced by an exposed global one: some
  exposed `g` has `RG g -> RL l` (`RG g -> RJ i`).
- `Reflects`: for exposed `g`, `RG g -> Components g`. `reflects_realizable`: `Reflects` plus
  `Covered` (every exposed local or interface ambiguity is a component of some exposed global
  one) gives `Realizable`.

Results, in plain math:

- `factor_sound`: `LC -> LocalRes -> InterfaceRes -> GlobalRes`.
- `factor_complete`: `Realizable -> GlobalRes -> LocalRes /\ InterfaceRes`.
- `factor_exact`: `LC -> Realizable -> (GlobalRes <-> LocalRes /\ InterfaceRes)`.
- `factor_pointwise`: `LCSound -> Reflects -> forall g, GAmb g -> (RG g <-> Components g)`.
- `factor_needs_sound`: `LCExposed`, `Realizable`, `LocalRes` and `InterfaceRes` hold and
  `GlobalRes` fails. `factor_needs_realizable`: `LC` and `GlobalRes` hold and `LocalRes` fails.

The theorem is logically thin, by design: like `history_descent_exact` (whose content is
presentation adequacy), its content is the obligation it names. Here the obligation is `LC`, and
for each instance the proof of `LC` is where the composition argument lives. The resolution
predicates are arbitrary, so the same theorem reads `GlobalH <-> LocalH /\ InterfaceH`,
`GlobalS <-> LocalS /\ InterfaceS`, or a mix; in the federation it is the mix
`GlobalH <-> LocalH /\ InterfaceS`.

### The acyclic federation as an instance (section `FedFactor`)

Hypotheses: `FederationEvents.Common` (repairs read only their sources, a topological order of
the registries, M1, absorption, the component normalizer fixes valid states, events preserve
validity and sit on registries of the order) and a valid, morphism-consistent start `s0`. These
are exactly the hypotheses of `FederationEventsConverse.pair_commute`.

- Global ambiguities: an independent pair `(a, b)` (different registries, or declared
  independent) at a state `s` reachable from `s0`; resolved when `applyF b (applyF a s)` and
  `applyF a (applyF b s)` agree (so `GlobalRes` is `GCF s0`, `fed_global`).
- Local ambiguities (the H shape): a declared-independent pair on one registry `j` at a reachable
  `s`; resolved when the local governed run of the overwrite canonicalizer `N_{j,s} := f j s`
  commutes on the pair, `grun (f j s) sig [a; b] (s j) = grun (f j s) sig [b; a] (s j)` (so
  `LocalRes` is `C2R s0`, `fed_local`).
- Interface ambiguities (the S shape): an event `e` on `j` and an event `a` on another registry
  at a reachable `s`; resolved when `e`'s action descends along the local canonicalizer of the
  source environment `a` changed, `StateDescentAt (f j (applyF a s)) sig e (s j)`, that is
  `f j z (sig e (s j)) = f j z (sig e (f j z (s j)))` with `z := applyF a s`: `s j` is
  canonical for the old environment and stale for `z` (so `InterfaceRes` is `C1R1 s0`,
  `fed_interface`).
- Decomposition: a same-registry pair is its own local ambiguity; a cross-registry pair is its
  two interface ambiguities, one per direction.

`LCSound` is `pair_commute` (`fed_lc_sound`) and `Reflects` is `pair_commute_nec`
(`fed_reflects`): the locality and topological-solving argument (`solve_unique`, `frun_solves`,
the `upL` lemmas of `FederationEventsConverse.v`) is exactly the proof of `LC` for this instance.
`LCExposed` and `Covered` are a few lines each.

Corollaries:

- `gc_iff_reach_P`: `GCF s0 <-> C1R1 s0 /\ C2R s0` (`gc_iff_reach`).
- `reach_commute_iff_P`: `reach_commute_iff`, by `factor_pointwise` at the start `s` with every
  pair declared independent (independence plays no role pointwise).
- `fed_exact_P`: `TraceConv s0 <-> C1R1 s0 /\ C2R s0` (`fed_exact`).
- `fed_exact_full_P`: the same with `C1R s0` (`fed_exact_full`).
- `fed_gc_sites`: the per-site form. `GCF s0` iff for every registry `j`: for all reachable `s`
  and declared-independent `a, b` on `j`,
  `grun (f j s) sig [a; b] (s j) = grun (f j s) sig [b; a] (s j)`; and for all reachable `s`,
  every `e` on `j` and every `a` on another registry,
  `StateDescentAt (f j (applyF a s)) sig e (s j)`.
- `fed_factor_supply`: non-vacuity. On the supply chain of `FederationEvents.v`, from every valid
  consistent start, `LC` and `Realizable` hold and all three resolutions hold.

### Acyclicity is needed for LC (`cyclic_lc_fails`)

A two-registry cycle `0 <-> 1` whose morphisms copy the other registry's value, with two events
on registry 1 (`CyNeg` negates, `CyOn` sets), declared independent. Every field of `Common` holds
except the topological order (proved not to hold). From the all-false start, which is valid and
consistent, every exposed local and interface ambiguity is resolved (`C1R1` holds vacuously,
`C2R` holds because the local canonicalizer of registry 1 overwrites the whole value), but
`CyNeg; CyOn` and `CyOn; CyNeg` leave registry 1 at `true` and `false`, so `GCF` fails and with it
`LCSound`. The local canonicalizer `f 1 s` reads registry 0, which reads registry 1: on a cycle
the event's own write comes back through its sources, so the environment of the local
canonicalizer is not fixed by the event's registry. This is the generic theorem's point of
contact with the monotone-cycle results: there the global condition `GC` is exact
(`FederationEventsCycles.gc_iff`), and per-edge checks go through `cyc_check`.

### The cyclic instance, soundness half (`cyc_factor_sound`)

On the monotone-cycle model of `FederationEventsCyclesCheck.v` (normal form `(l, Lsh l)`),
`commute_nf` proves `LCSound` for the decomposition whose local ambiguities are the `C2cyc`
witnesses and whose interface ambiguities are the `C1cyc` witnesses, every global ambiguity (an
independent pair at a normal form) decomposing into all of them (`cyc_lc`). This is a static
decomposition, not a pointwise one. `factor_sound` then gives `GC` on the image of the
normalizer from `C1cyc /\ C2cyc` (`cyc_factor_sound`; `cyc_check_gc_lfp` is the same for gsm's
Kleene normalizer). Realizability of the static witnesses is not proved, so the cyclic instance
is the soundness half only; the static witnesses are not realizable in general, as
`FederationEventsConverse.naive_converse_fails` shows in the acyclic case.

### State gluing and interaction locality (an observation, not a claim)

P has two halves in this development:

- P_state, `SheafGluing.v`: gluing of local canonical states over a cover.
  `sheaf_iff_refines`: gluing holds on a cover for every federation satisfying R1 iff the cover
  refines the constraints (every constraint inside the union, a target together with its
  sources, lies inside one member).
- P_interaction, this module: gluing of local execution laws. `factor_exact`: global history
  descent iff local and interface resolution, under `LC` and realizability.

They look like the object and morphism halves of a descent condition: P_state descends
canonical states (objects) along a cover; P_interaction descends the commutation of steps
(morphisms of the execution) along a composition boundary. What is proved about the relation:

- One hypothesis is shared, and proved shared: `common_r1` shows that `Common`'s `c_local` (a
  repair reads only its sources), the locality hypothesis behind `LC` in the federation
  instance, is `SheafGluing.R1` for the repair read at any fixed target values.
- `Refines` (every constraint's footprint inside one member) has no counterpart hypothesis in
  `factor_exact`. Where `Refines` asks that no constraint cross a member boundary, the
  factorization lets constraints cross the boundary and makes each crossing an interface
  ambiguity (the C1 shape). Read with the cover by single registries, `Refines` fails exactly at
  the edges, and those edges are where the interface obligations sit; this correspondence is
  stated here informally and is not mechanized.

What is not proved: no single theorem combines the two halves (for example, "global convergence
iff gluing on a cover and locality across it"); the two halves are stated on different models
(`SheafGluing` on resolver presheaves, the federation instance on `FederationEvents.Common`), and
no categorical descent statement (a stack or descent datum) is formalized. The precise combined
statement the mechanization supports is: on an acyclic federation satisfying `Common` (hence R1),
state gluing holds on refining covers (`sheaf_iff_refines`), and interaction convergence is
exactly local history descent plus interface state descent (`fed_gc_sites` with `fed_exact_P`).

## Criterion D, rerun

| | Existing result | Kernel theorems used | Outcome | Evidence |
|---|---|---|---|---|
| D | `FederationEventsConverse.fed_exact`, `fed_exact_full`, `gc_iff_reach`, `reach_commute_iff` | `history_descent_exact` (H), `factor_exact` and `factor_pointwise` (P) | PASS | `fed_exact_P` (6-line proof body): the kernel history layer (`history_descent_exact` with the adjacent-swap generators of the first run, `fed_adequate`, `fed_gen_iff`), then `gc_iff_reach_P` (2-line proof body: `factor_exact` plus the three identifications). `gc_iff_reach` itself is not used. `reach_commute_iff_P` (16-line proof body, mostly unfolding the two identifications both ways), `fed_exact_full_P` (14 lines, of which the multi-event move is the model's `conv_c1_runs`, as in the original). Instance glue (about 85 non-comment lines): the ambiguity definitions, `freach_ok`, `fed_lc_exposed`, `fed_covered`, the identifications `fed_global`, `fed_interface`, `fed_local` (definitional up to symmetry), and `LC` itself, `fed_lc_sound` and `fed_reflects` (6 and 5 lines), which call `pair_commute` and `pair_commute_nec` (about 100 and 27 lines of `FederationEventsConverse.v`). |

The rubric is the one of the first run: glue is either an obligation the kernel names or reused
model semantics. `LC` is now an obligation the kernel names, and its proof is the model's
locality lemma, reused. Interface resolution is literally kernel state descent
(`StateDescentAt`) and local resolution literally the kernel's governed run (`grun`), so the two
definitional identifications of the first run are now the definitions.

## Findings beyond the pass/fail table

- **Generators must sit at their legal landing points.** In B and C, the generator edges that
  make the edge condition equal the published local condition (CCR, CCRon, IdemAt, AbsorbAt) are
  the ones whose prefix is an exactly-once causally consistent run. Free words with a context rule
  would quantify the local condition over unreachable or duplicated prefixes.
- **Adequacy carries the combinatorics.** In C the whole at-least-once argument becomes a
  semantics-free statement about words plus one-edge local lemmas; the semantic absorption lemmas
  of `AtLeastOnceExact.v` are not used.
- **E and S can be vacuous by discipline.** For stream processors the dynamics normalizes before
  every event, so the StatePeak class is empty and only H remains.
- **flush_fed_iff is order-free.** Its kernel derivation uses only that `Nc` reads the locals and
  is idempotent.

## Recommendation

The abstraction is supported for single-state-space regimes: A, B, C, E and F rederive the
existing exact theorems through the three kernel theorems, with glue that is either an obligation
the kernel names (peak classification, presentation adequacy, the E/S/H translation) or reused
model semantics. With the P layer, D passes under the same rubric: the federated regime is
history descent (H) composed with the interaction-locality factorization (P), whose obligation
`LC` is the model's locality lemma. So E, S, H and P now rederive all six criteria. Two limits
remain and argue for keeping the experiment uncited: the P layer's exact form is proved for the
acyclic federation only (on monotone cycles only the soundness half, with a static
decomposition), and the relation between P_state and P_interaction is an observation with one
shared hypothesis, not a combined theorem.
