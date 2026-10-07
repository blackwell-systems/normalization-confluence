# Compositional collapse

Detailed results for compositional collapse: sub-federations as effective registries. Each module's
one-line summary is in the [module index](../README.md#modules-by-regime); the status of each
question in this regime is in [REGIME-AUDIT.md](../../REGIME-AUDIT.md#14-compositional-collapse),
section 14.

## Compositional collapse: sub-federations as effective registries (`Collapse.v`)

ROADMAP item 7, work package WP8 (rows F28 to F30, C4 and C5 of `PAPER-MAP.md`): the federation
paper's `thm:collapse` and `cor:modular`, the categorical paper's Theorem 2 collapse claim and its
port refinement. Built on `FederationEvents.v` and `FederationGRS.v` (WP5): the primary corrected
form is the GUARDED federation (events fire only at federally valid states) under C1 and C2.
Axiom-free.

The model. A sub-federation `J` is a membership predicate `inJ`; the data-flow graph has an edge
`k -> j` when `k` is a source of `j` (`path`). `Convex` is `def:subfed`'s convexity. The effective
registry `R_J` (`def:effreg`) has compensation `rhoJ` (phase 1 on the members, then the internal
repairs along `blk`, the members in topological order), member validity `InvJ` and internal
morphism invariants `ConsJ`; its events are the events of the members, `applyJ e = rhoJ o e`. The
contracted network `N'` is `srcC` / `orderC` (graph: `J` replaced by one vertex `c`) and `Ncol`
(normalizer: `J` run as one node), with `grhoC`, `gvalidC`, `genabC` its federated GRS on lists.

| Label | Status | Coq |
|---|---|---|
| proof of `thm:collapse` (c): "a topological order visits a convex `J` as a contiguous block" | refuted ("every order"); corrected ("some order") | `collapse_every_order_refuted`; `collapse_block_order` |
| `thm:collapse` (c): `N'` acyclic if `N` is | exact | `collapse_contract_topo`, `collapse_contract_acyclic` (`topoF_acyclic`); convexity needed: `collapse_convexity_needed` |
| `thm:collapse` (a), WFC | exact (one round) | `collapse_a_wfc` |
| `thm:collapse` (a), CC | refuted; corrected (C1 + C2 on `J`'s events); exact | `collapse_a_refuted`; `collapse_a_guarded`, `collapse_a_guarded_perm`; `collapse_a_guarded_exact` |
| `thm:collapse` (b) | exact with M1 against member validities; refuted with M1 against `R_J`'s federal validity; corrected | `collapse_b_import_iff`, `collapse_b_export_iff`; `collapse_b_import_refuted`, `collapse_b_export_refuted`; `collapse_b_import_corrected`, `collapse_b_export_corrected` |
| `thm:collapse` (c): normal forms agree | exact | `collapse_nf_agree`, `collapse_nf_factor` |
| `thm:collapse` (c): `N` converges iff `N'` does | exact (FedMachine runs, guarded and unguarded GRS) | `collapse_c_runs_agree`, `collapse_c_traceconv`, `collapse_c_exact`; `collapse_c_guarded_iff`, `collapse_c_unguarded_iff`, `collapse_c_guarded_exact`, `collapse_c_guarded_c1_c2` |
| `cor:modular` | exact (corrected hypotheses) | `collapse_modular_c1`, `collapse_modular_c2`, `collapse_modular_converges`; nesting `collapse_regroup`, `collapse_hierarchical`; product case `collapse_product_convex` |
| categorical `thm:two`, "collapses to an effective registry" | exact | `collapse_nf_agree`, `collapse_a_wfc`, `collapse_c_guarded_iff` |
| categorical Section 4, port refinement | mechanized; sealed write refuted | `port_c1_transfer`, `port_c2_transfer`, `port_interior_certificate`, `port_interior_invariant`; `port_sealed_write_refuted` |

Corrected statements (H: `J` convex, its members' morphisms satisfy M1/R2, its components WFC and
CC, the network acyclic):

- (a) `rho_J` reaches `R_J`-validity in one application from any state with valid import ports,
  leaves every non-member unchanged and fixes every `R_J`-valid state (WFC). H does not give `R_J`
  CC: the audit federation (`J` = all of it) satisfies H and two of its events do not commute
  through `R_J` at an `R_J`-valid state. With C1 and C2 for the events of `J`'s members,
  federally independent events commute through `R_J` at every `R_J`-valid state, and (every
  same-registry pair declared independent) every two orders of `J`'s events agree; exactly, `R_J` converges from an `R_J`-valid state iff C1 and C2
  hold at the witnesses reachable inside `J`.
- (b) With M1 posed against the product of the members' validities, an import into a member (or
  an export out of `J`) satisfies M1 for `R_J` iff it does in `N`. With M1 posed against `R_J`'s
  federal validity (member validities and internal invariants), the import direction fails (an
  import overwrites a port and breaks an internal copy) and so does the export converse (an export
  that is M1 on internally consistent sources only). What holds: an import followed by `rho_J`
  lands in `R_J`'s federal validity; M1 of an export in `N` implies it for `R_J`.
- (c) Contracting a convex `J` keeps the network acyclic (convexity is needed); `N'`'s normalizer
  equals `N`'s, and factors as "registries before `J`, then `rho_J`, then the rest"; every event run
  of `N'` equals the run of `N`, so `N'` converges iff `N` does, for the guarded and the unguarded
  GRS. Under C1 and C2 (checked per block) `N'` converges; exactly, iff C1 and C2 hold at the
  reachable witnesses.
- `cor:modular`: C1 and C2 split by the event's registry (`J` and the rest), so verifying `J`'s
  certificate once and the rest once gives `R_J`'s guarded CC and the convergence of `N'`; any
  block decomposition whose flattening is a topological order computes `rho_Fed`, and regrouping
  consecutive nodes changes nothing, so the construction nests. A `J` with no edge leaving it
  (the product case) is convex.
- Port refinement: if the embedding changes the sources and repair only of ports (sealed members
  keep theirs), C1 and C2 at sealed members transfer verbatim, the subsystem's certificate plus the
  seam re-check at the ports is `J`'s full certificate in the embedding, and every federally valid
  state of the embedding satisfies the sealed members' certified repair equations. A write to a
  sealed member breaks that guarantee (`port_sealed_write_refuted`).

Not covered here: the cyclic-with-monotone-repair variant of `thm:collapse`'s hypothesis is
`CompositionBlocks.v`'s (below, gap 5), and the remark "Convexity and the monotone regime" is
`MonotoneFederation.v`'s (`fed_rem_convexity_refuted`). Non-vacuity: `chain_collapse_instance` (a chain `0 -> 1 -> 2`, `J = {0, 1}`: Common, C1, C2,
convexity, the block order, the contracted network, and the guarded convergence of `N'`
instantiated); the counterexamples `collapse_b_import_refuted` and `port_sealed_write_refuted`
satisfy `Common`.

## Composition of blocks of any engines (`CompositionBlocks.v`)

REGIME-AUDIT.md gap 19 (cells A14, B11, B13 of [COVERAGE.md](../../docs/COVERAGE.md)) and gap 5.
`Collapse.v` is the acyclic case. This module asks what composition needs when the blocks of the
condensation use different engines (a monotone cycle, a rootless invertible network, a
non-monotone block), when `J` is a monotone cycle, and when `J`'s propagation interleaves with
outer events in the distributed model. Axiom-free.

### The interface theorem (any engines)

The condensation of a network into strongly connected blocks is acyclic, so every finite DAG of
blocks is built by composing an upstream system `A` with one block `B` that reads it, over and over.
A system is a state type with an equivalence, actions with a predicate selecting the network's own,
and a deterministic step per action. `B`'s step reads `A`'s current state (`stepB x b y`), and the
composite on `X * Y` interleaves the two freely. `Quiet` is a normal form (no allowed action changes
the state). `Conv`: from every start some schedule reaches a quiet state, and every schedule that
reaches one reaches the same one. This is the form of `net_unique_normal_form_iff`. `Lk xs` is the
equivalence on `B`'s states generated by `B`'s steps at inputs from which `A` reaches `xs`.

| Statement | Status | Coq |
|---|---|---|
| The composite converges iff `A` does, `B` reaches a quiet state from every start at every quiet input `xs` of `A`, and two quiet states of `B` at `xs` related by `Lk xs` are equal | exact; each conjunct necessary | `compose_exact`; `compose_needs_A`, `compose_needs_wn`, `compose_isolated_refuted` |
| Each block converging in isolation (`A` from every start, `B` at every fixed input from every start) is not enough | refuted | `compose_isolated_refuted`: the sticky block (`y` takes the input while `y = 0`) |
| `B` is constrained only at `A`'s quiet inputs | non-vacuity | `compose_transient_free` (no normal form at a transient input; the composite converges) |
| The composite's normal form is the block-by-block one, `B` started from the original state at `A`'s normal form | exact, under the conjuncts | `compose_collapse` |
| Interface: each block has an equivalence `K` its steps preserve (its own inputs: locals, root values), and settles (every start reaches a quiet state; quiet states related by `K` are equal) | closed under composition, exactly | `interface_closed`, `settles_conv`, `interface_lk` |

By `interface_closed` the interface holds for any finite DAG of blocks that meet it, whatever their
engines; by `interface_lk` a block that meets it satisfies `compose_exact`'s third conjunct.

### Engines

| Engine | Statement | Coq |
|---|---|---|
| Rootless invertible network (`RootlessNetworks.v`) | converges iff `has_section` and (`authority_cover` or the group is trivial): `net_unique_normal_form_iff` read as `Conv` | `rootless_conv_lhs`, `rootless_conv_iff`; feeding any block, `mixed_rootless_exact` |
| Monotone cycle (`DistributedCycles.v`), locals fixed | meets the interface with `K` everything iff its repair has one fixed point (through `q1_unique_iff`) | `mono_block_interface_iff`; fed by any system, `mixed_mono_iff` |
| Mixed instances | a rootless block (`rootless_source_feeds_cycle`'s network, over Z/2) feeding a reader, and feeding a monotone 2-cycle with one fixed point at every local: both converge. Feeding the flag cycle of `FederationEventsCycles.v`: the rootless block converges, a transient alarm lifts the cycle to its ghost, and the composite has two normal forms | `mixed_instance`, `mixed_mono_instance`, `mixed_ghost_refuted` |

### Gap 5: a cyclic monotone `J` (FedMachine)

The FedMachine of a monotone network computes the least fixed point of the repair (`cyc_N_lfp`).
Split the shared values into an upstream block and a downstream block (either one is `J`; nesting
the split gives any decomposition along the condensation). Then the repair is triangular,
`F l (x, y) = (FA l x, FB l x y)`.

| Statement | Status | Coq |
|---|---|---|
| Blockwise least fixed points are the least fixed point (Bekic's principle; finite height on `Y`) | exact | `bekic_lfp`, `lfp_below_prefixed` |
| `N'` (`J` normalized as one effective registry, by its own least fixed point at its inputs) and `N` have the same normal form | exact | `mono_collapse_nf` |
| `N'` converges iff `N` does, both iff GC | exact | `mono_collapse_runs_agree`, `mono_collapse_converges_iff`, `mono_collapse_exact` |
| Non-vacuity: a root feeding the flag cycle, the flattened side gsm's `normalizeCyclic` | instance | `mono_collapse_instance` |

### The distributed model: collapse when `J` interleaves with events

In the collapsed distributed network `N'`, `J` propagates as one effective registry: one action
runs `J`'s internal repair to completion, its block in order. Words are lists of atoms.

| Statement | Status | Coq |
|---|---|---|
| Any atom set with every event, propagation words and a flush: convergence over its words iff XU at the states they reach and C2 at states reachable from the flushed start | exact; `dist_exact` recovered | `dist_atoms_exact`, `dist_exact_recovered` |
| `N'`: the same, over `N'`'s words | exact | `dist_collapse_exact` |
| `N` converges -> `N'` converges | sound | `dist_collapse_sound` |
| `N` converges iff `N'` converges and XU holds at every state `N` reaches (`XUR`, `J` half-propagated included) | exact; each conjunct necessary | `dist_collapse_iff`; `dist_collapse_refuted`, `dist_collapse_needs_c2` |
| `collapse_c`'s "`N'` converges iff `N` does" in the distributed model | refuted | `dist_collapse_refuted`: the chain `0 -> 1 -> 2`, `J = {1, 2}`, `Common`, `J` convex; an event on 1 propagated to 2 before 1 is repaired is a combination no `N'` run produces |
| Under static XU (gsm's `ProjectionSafe`) | `N` converges iff `N'` does | `dist_collapse_xu` |

Not covered: a cyclic `J` in the distributed model (the no-reset model of
`DistributedCyclesExact.v` and reset epochs), where `J`'s atom would be its own flush to
quiescence. That is gap 19's residue.

Literature. Bekic's principle (H. Bekic, "Definable operations in general algebras, and the theory
of automata and flowcharts", IBM Vienna 1969, reprinted in LNCS 177, 1984); Robert's decomposition
of discrete iterations along the strongly connected components of the interaction graph
(F. Robert, *Discrete Iterations*, Springer 1986); block-by-block attractor detection along the SCC
decomposition of Boolean networks (Mizera, Pang, Qu and Yuan, IEEE/ACM TCBB 16(1), 2019); attractors
of a network assembled from those of its modules driven by their upstream modules (Kadelka,
Wheeler, Veliz-Cuba, Murrugarra and Laubenbacher, J. R. Soc. Interface 20(207), 2023). The results
here are the exact conditions in this development's step model; no claim of priority is made.
