# Canonical execution (experimental)

> **Experimental: validation in progress.** This page records a research experiment. Do not cite
> these results yet. Nothing here changes what [REGIME-AUDIT.md](../../REGIME-AUDIT.md) or the
> papers state; the modules only rederive existing exact theorems through a common kernel and
> record where that works and where it does not.

Modules: `CanonicalExecution.v` (the generic kernel) and `CanonicalInstances.v` (the six
validation criteria). Both are axiom-free and in `verify.sh`'s gate. The module index row is in
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

A fourth, compositional layer **P** (spatial descent and gluing) is out of scope here; it is the
subject of the sheaf-gluing development (`SheafGluing.v`, a separate module).

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
| D | `FederationEventsConverse.fed_exact` | `history_descent_exact` | PARTIAL | `fed_exact_kernel` (7-line proof). The history layer goes through the kernel: trace convergence iff commutation at each reachable independent swap (`fed_adequate`, `fed_gen_iff`, using `FederationEvents.runF_ext`). C1R1 is reachable state descent of the overwrite canonicalizer `N_{j,z} := f j z` (`c1r1_state_descent`; `N_{j,z}` is idempotent on valid states, `overwrite_canonicalizer`), and C2R is the one-swap history condition of the local governed run (`c2at_history`). The glue the kernel cannot supply is the split of a swap's commutation into C1R1 and C2R: that is the model's locality lemma `FederationEventsConverse.gc_iff_reach` (via `pair_commute`, about 100 lines of topological solving), used as is. See "The leak" below. XU, `XUat` (so XUR) and XUc are state descent on larger exposure domains: `xu_state_descent` (every valid target state), `xuat_state_descent` (stale distributed states), `xuc_state_descent` (cycle states, `N := Nc`). |
| E | `StreamExact.pjc_exact`, `stream_exact`, `stream_exact_free` | `classified_peak_exact`, `history_descent_exact` | PASS | `pjc_exact_kernel` (10-line proof). The processor discipline applies an event only from a valid state, so the StatePeak (an event step against a compensation step) has contradictory premises: `stream_state_peaks_empty`. Confluence is the HistoryPeak condition PJC alone. `stream_exact_kernel` (15 lines) is `stream_exact` with `pjc_exact` replaced by the kernel route; the processor-to-reduction glue (`stream_agree_set_function`, `sx_un_cr`, `sx_nf_empty_progress`) is reused from `StreamExact.v`. Under free delivery, `stream_free_history`: stream agreement iff history descent of the governed run from `rho* s0` over duplicate-free reorderings (PCC is the swap edge condition, `pcc_gen_iff`). This last one rereads `stream_exact_free` rather than rederiving its processor half. |
| F | `DistributedCyclesExact.flush_fed_iff` and the ghost family | `esh_exact` | PASS | `flush_fed_iff_kernel` (5-line proof): Settlement is FlushR, CanonicalFidelity is NoGhostR, StateDescentR is XUcR, HistoryDescentC is `FMConv (Nc s0)`. The glue is six translation lemmas (`d_settle`, `d_fidelity`, `d_state_descent`, `d_history`, `d_agree`, `d_conv`), each a few lines from `Nc_fst`, `fst_Nc`, `Nc_idem`, `quiet_normal`, `Nc_eq`. The kernel route needs none of the order, rank or cover hypotheses of `DistributedCyclesExact`'s section (the content was already order-free in `DistributedCycles.quiet_agree_iff`). Ghost family: `flip_esh` (Settlement fails alone), `ghost_esh` (CanonicalFidelity fails alone), `conv_ghost_esh` (H and convergence hold without E: Fidelity fails, so agreement fails), `copy_xu_esh` (S fails alone), `fm_conv_esh` (H fails alone); each failure of agreement is derived through `flush_fed_iff_kernel`, not cited. `raise_only_esh`: all three layers hold together (non-vacuity). |

## The leak (criterion D)

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
model semantics. It is not yet validated for federated regimes: D needs the P-layer locality
theorem described above. Keep the experiment uncited until that theorem is added and D is rerun.
