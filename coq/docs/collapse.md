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

Not covered: the cyclic-with-monotone-repair variant of `thm:collapse`'s hypothesis and the remark
"Convexity and the monotone regime" (the monotone cycle model is `FederationEventsCycles.v` /
WP6's). Non-vacuity: `chain_collapse_instance` (a chain `0 -> 1 -> 2`, `J = {0, 1}`: Common, C1, C2,
convexity, the block order, the contracted network, and the guarded convergence of `N'`
instantiated); the counterexamples `collapse_b_import_refuted` and `port_sealed_write_refuted`
satisfy `Common`.
