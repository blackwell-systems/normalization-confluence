# Paper-to-Coq map (ROADMAP item 7)

> **Status note.** The status columns below are a historical snapshot from the 254-theorem gate
> and predate later merges (work packages WP1 to WP9 and the exactness work after them; the gate is
> now 2067). Many rows marked NOT or PARTIAL are mechanized now. The tables are kept as written.
> [REGIME-AUDIT.md](../REGIME-AUDIT.md) is the current status, regime by regime; for the modules
> and their headline theorems, see the [module index](README.md#modules-by-regime).

An exact map from every numbered result in the three papers to the Coq development, written as the
first step of ROADMAP item 7 ("every result in the papers is mechanized"). Audited against `main`
at `0d16624` (gate: 254 theorems, items 1 to 4 done). Every Coq statement cited here was read; no
match is by name alone.

Papers:

- **Base**: `normalization_confluence_2026.tex` (single registry).
- **Fed**: `normalization_confluence_in_federated_registry_networks.tex` (restates Base sections 3
  to 7 and 9, then adds the federation sections).
- **Cat**: `categorical_structure_of_federated_convergence.tex`.

Results are identified by their LaTeX `\label` (or by name and section when unlabeled), because the
numbering shares one counter per section and is easy to misread.

## Status legend

| Status | Meaning |
|---|---|
| EXACT | A Coq theorem states the paper result (up to the abstraction the paper itself uses). |
| DIFF | Coq covers the substance in a different statement; the notes say what differs and whether the paper statement follows by a short argument. |
| PARTIAL | Part of the result is mechanized; the notes say which part is missing. |
| REFUTED | The paper statement is false, and a theorem already in the gate is a counterexample to it. A corrected statement is mechanized. |
| NOT | Not mechanized. |
| CITED | A result from the literature, not to be mechanized. |
| DEF | A definition, hypothesis or trivial remark with no content to mechanize. |

Flags in the notes: **FALSE AS STATED** (a counterexample is given in this document but is not yet
in Coq), **IMPRECISE** (true under a reading the paper does not pin down, or the paper's own witness
is wrong).

Gate status: every Coq theorem named in the tables is in the `verify.sh` gate except these, which
exist and compile but are not gated (most are dependencies of gated theorems, so their axioms are
checked transitively, but item 7's criterion asks for the named theorem in the gate):
`fixed_is_equalizer`, `retract_fixes_fixed`, `rhoL_idempotent`, `rhoL_image_iff_L`,
`rhoL_L_iff_fixed`, `rhoFold_sound`, `rhoFold_complete`, `rhoF_from_app`, `rA_idem`, `rB_idem`,
`agree_on_valid`, `disagree_as_normalizers`, `locally_confluent_step`,
`causal_locally_confluent_step`, `terminating`, `newman`, `confluent_of_SN`, `unique_normal_forms`,
`gstep_is_apply`, `gstep_commute`, `cvrdt_absorbs_duplicates`, `N_cons`, `N_inv`, `frun_solves`,
`solve_unique`, `evstep_off`, `nf_valid_empty`. Adding them is a one-line change each, best done in
the integration step after the packages below.

Difficulty for open work: **S** (an afternoon: one file, under about 150 lines, reuses existing
lemmas), **M** (one or two days: a new model or a bridge between two existing models), **L** (new
theory, or a mathematical decision is needed before proving).

## Summary

| Paper | Rows | EXACT | DIFF | PARTIAL | REFUTED | NOT | CITED | DEF |
|---|---|---|---|---|---|---|---|---|
| Base | 40 | 2 | 4 | 4 | 0 | 15 | 0 | 15 |
| Fed, new sections (6, 8.2) | 33 | 0 | 5 | 9 | 3 | 5 | 0 | 11 |
| Fed, restated from Base | 39 | 2 | 3 | 4 | 0 | 15 | 0 | 15 |
| Cat | 24 | 5 | 5 | 5 | 0 | 8 | 1 | 0 |

Fed restates every Base row except `cor:infinite` (Fed has no "Infinite Domains" subsection), with
the same statuses. Fed totals: 72 rows; 2 EXACT, 8 DIFF, 13 PARTIAL, 3 REFUTED, 20 NOT, 26 DEF.

## Main findings

### Paper statements that are false or imprecise

1. **The federated convergence theorems are false as stated (Fed `thm:fed-cc`,
   `thm:fed-convergence`, `thm:resolved-convergence`, `lem:authority` (c)).** They assume only
   component WFC and CC, M1 (or R1/R2) and a tree (or acyclic) network. `audit_counterexample`
   (`FederationEvents.v`, gated) is a two-registry tree in which every one of those hypotheses holds
   (Common: locality, topological order, M1, overwrite absorption; the target's own CC) and the two
   event orders end with `sold = 0` and `sold = 1`. `c2_counterexample` is a second one, with C1 also
   holding. The proofs fail at "each local component sees at most one event" and at "local
   components converge by component CC": a target event can read a shared variable the morphism
   overwrites. The corrected, mechanized statements need C1 and C2 (`fed_events_commute`,
   `fed_interleavings_converge`, `fed_permutations_converge`), and the exact condition is
   `fed_exact` / `fed_exact_full` / `acyclic_gc_iff`. Fed never mentions C1 or C2. The abstract,
   contributions 7 to 9 and the conclusion ("federated convergence requires only validity
   preservation of the morphisms") repeat the false claim. ROADMAP item 7 currently lists "the
   authority and resolution theorems as stated" as covered "in a different form"; that should read
   "refuted; corrected form mechanized".
2. **The last sentence of Fed `thm:monotone-cycles` is false** ("Consequently all processors
   consuming the same federated events converge"). `cyc_counterexample` (gated) is a monotone
   two-registry cycle meeting every hypothesis on which `LatchA; RaiseB` and `RaiseB; LatchA` diverge.
   The corrected statement is `cyc_events_converge_iff` (convergence iff GC). The first part of the
   theorem (least fixed point, chaotic iteration) is true and mechanized. The proof's claim that
   validity is preserved along the Kleene iteration "exactly as in" the acyclic lemma is also a gap:
   the iteration starts from bottom shared values, which need not be valid, and `cyc_N_idem` takes
   `lfp_valid` as a hypothesis.
3. **Base `thm:footprint-cc1` (footprint commutativity) is FALSE AS STATED.** With no invariants
   (`k = 0`) every footprint is empty, repair is the identity and repair locality is vacuous, so the
   theorem would make any two events commute (take `x := 1` and `x := 2`). It stays false even if
   the raw events are also required to commute: on states `{0,1,2,3}`, invariants
   `psi1 = psi2 = (s >= 2)`, repairs `r1 = r2 = (0 -> 2, 1 -> 2, 2 -> 2, 3 -> 3)`, events
   `a = (0,0,2,3)` (footprint empty, repair-local) and `b = (0,0,3,0)` (footprint `{1,2}`), the raw
   events commute but at state 0 the two sides of CC1 are 3 and 2. The proof's final "Equating" step
   moves `R_S1` past `A_e1`, which repair locality does not allow. `Gsm.disjoint_events_commute` is a
   different (true) statement about state-variable footprints. The Base remark "Machine-checked"
   says "footprint disjointness implies order-independent commutation" about that Gsm result, which
   reads as if this theorem were mechanized.
4. **Base remark "Practical import" (after `thm:footprint-cc1`)**: the order-fulfillment events do
   not have disjoint invariant footprints (one invariant; approve can falsify it and credit can
   restore it). FALSE AS STATED.
5. **Base 8.2 "Verifying CC", pattern 1** ("compensation to a canonical state: both CC1 and CC2 hold
   trivially") is FALSE AS STATED: on valid states compensation never fires, so two non-commuting
   valid-to-valid events violate CC1. Pattern 2 (lattice-structured compensation) is IMPRECISE ("join
   with the nearest valid state" is not defined). Both are repeated in Fed.
6. **Base 4 worked example, "Why Compensation Design Matters"**: IMPRECISE witness. Under the naive
   revert `rho(approved, b) = (pending, b)`, CC1 holds at `(pending, 0)` (both orders give
   `(pending, 1)`), contrary to the text. CC1 does fail at `(pending, 1)`: `(pending, 2)` versus
   `(approved, 2)`. The claim survives; the witness must change. (The held-stage registry itself
   satisfies CC1 and CC2; checked by hand over all 12 states for this audit.)
7. **"CC is necessary"** (Base abstract, conclusion, the remark after `prop:cc-necessary`; Fed
   likewise): IMPRECISE. `prop:cc-necessary` itself is existential and true, but CC as stated is not
   a necessary condition: `masked_cc1` shows CC1 failing at a reachable configuration under causal
   enabledness (the paper's own setting) with unique normal forms, and `rho_star_qualifier` shows
   the same with non-canonical repair. The exact converse is `cc_exact_from` (free delivery,
   canonical repair, reachable states) and `jc_exact` (any enabledness).
8. **Base 8.1 three-regime hierarchy**: "normalization confluence subsumes invariant confluence" is
   IMPRECISE. An I-confluent system needs no compensation but its operations need not commute, so it
   can violate CC1. Only the CRDT side is mechanized (`CRDT.v`, `compensation_free_exact`).
9. **Base `thm:necessity` and its remark ("R_infinity satisfies WFC and CC")**: IMPRECISE.
   `apply(e_n, sigma)` is defined only at `sigma = 0`, so CC for event sets with several events is
   not determined; `cor:infinite`'s paragraph relies on "R_infinity satisfies CC and converges".
10. **Cat `prop:minimal`**: "admits a coordination-free SEC convergent implementation iff `H^1 = 0`"
    needs two qualifiers the Coq development already records: the regular (torsor) action
    (`nonfree_holonomy_counterexample`: a non-identity holonomy acting on a non-torsor fiber still has
    a section, so "invertible fragment" with `G <= Sym(S)` is not enough), and an authority root for
    uniqueness (`copyback_without_authority`, `root_choice_matters`).
11. **Cat section 8, non-invertible case** ("the decomposition still holds (a cycle basis suffices,
    by the fixed-point form)"): suspected FALSE AS STATED. With non-invertible transports a tree
    need not carry a section: two tree edges `a -> c` and `b -> c` with constant maps 0 and 1 force
    `c = 0` and `c = 1`. It holds when every tree edge points away from the authority root (drive
    along the tree), which is what `CoordinatedCycles.v` does with inverses; without inverses only
    that orientation works. `noninvertible_balance_not_static` is related.
12. **Cat section 7, the paragraph on reading the diagnostic's result**: the claim that a
    non-convergent result is definitive ("an orbit exists, so the cycle cannot converge") is FALSE AS
    STATED for non-invertible or non-free loop
    composites. An orbit from one seed shows that seed does not settle, not that no fixed point
    exists (on `{0,1,2}`, `0 <-> 1` swapped and `2` fixed). `nonfree_holonomy_counterexample` is
    this situation.
13. **Cat `thm:obstruction`**: IMPRECISE. "Reachable fixed point" is not defined (reachable from
    what?). Without "reachable" the statement is the elementary fact that a section of a cycle is a
    fixed point of the loop composite at any vertex.
14. **Fed remark "Convexity and the monotone regime"**: "if the sub-federation's repair is monotone
    then so is `rho_Fed^J`" is unproven and doubtful: `rho_Fed^J` includes the components' phase-1
    normalizers, which need not be monotone.
15. **Fed remark "Infinite lattices and widening"**: IMPRECISE. "The convergence guarantee is
    unaffected" without ACC: the least fixed point exists (Knaster-Tarski) but finite chaotic
    iteration need not reach it. The mechanized results are under ACC (`ChaoticACC.v`).

### Mechanization claims in the papers

- **No paper states a theorem count**, so there is no outdated count. "Checked with Rocq 9.3"
  remains true (CI also runs Coq 8.18 and 8.20).
- **Every Coq name the papers cite exists.** Cited but not in the gate: `fixed_is_equalizer`,
  `rhoFold_sound`, `rhoFold_complete`, `rhoF_from_app` (the last three are dependencies of gated
  theorems, so the gate covers their axioms transitively; `fixed_is_equalizer` is not covered).
  `RetractionOntoConsistent` is a Section name, not a theorem; its theorems are `rhoL_idempotent`,
  `rhoL_image_iff_L`, `rhoL_L_iff_fixed` (all ungated).
- **Base remark "Machine-checked" (`sec:mechanization`)**: accurate for what it lists, with the
  footprint ambiguity in finding 3. It under-claims what landed since: `cor:infinite` is now
  mechanized (`governance_wf_confluent`, `zw_confluent`), CC1 on co-enabled pairs only
  (`causal_governance_confluent`) matches the paper's Axiom CC better than `Governance.v`'s all-pairs
  `cc1`, and the exact converses (`cc_exact_from`, `jc_exact`) refine the necessity section.
- **Fed remark "Machine-checked"**: accurate about the monotone core, but silent about
  `FederationEvents.v`, `FederationEventsCycles.v` and `FederationEventsConverse.v`, whose gated
  counterexamples refute Fed's federated theorems (finding 1, 2). This is the most outdated text in
  the three papers.
- **Cat**: the claims that Lemma 0, Proposition 1, Theorem 1 (retraction and order-independence) and
  Theorem 2 are mechanized are accurate for the operators Coq models, with three gaps the paper does
  not state: Proposition 1's `L_F` omits the "each component is a normal form" conjunct in Coq;
  Theorem 1's consistent set in Coq is the intrinsic `ConsistentList` (each position fixed by its
  step), not Proposition 1's `L_F`; and order-independence is proved in a different model
  (`FederationOrder.run` over `nat`-indexed states) from the retraction (`rhoFold` over positional
  lists), with no bridge between them. Cat's related-work claim that "the monotone regime coincides
  with state-based CRDTs (machine-checked)" overstates `cvrdt_SEC`, which proves only the semilattice
  direction.
- **ROADMAP item 7's known-gap list** should add findings 1 to 5 and 10 to 12: those statements need
  revising before they can be mechanized, so "every numbered result has a named Coq theorem in the
  gate" requires a paper revision as well as Coq work.

## Base: `normalization_confluence_2026.tex`

| # | Label | Statement (short) | Status | Coq | Notes |
|---|---|---|---|---|---|
| B1 | `def:registry` | Registry `(Sigma, I, V, rho)`, rho decreases a measure when invalid, fixes valid states | DEF | `Governance.v` parameters `apply`, `rho`, `valid`, `Phi` | Fed's version drops the measure clause and adds determinism. |
| B2 | `def:projection` | Semantic projection; apply is "apply then project" | DEF | none | Well-definedness is a hypothesis of the definition. |
| B3 | `rem:scope` | Finiteness of semantic states; at most `2^k` classes | DEF | none | Modeling remark. |
| B4 | `def:equiv` | Registry equivalence | DEF | none | |
| B5 | `lem:equiv-relation` | Registry equivalence is an equivalence relation | DEF | none | Trivial. |
| B6 | `ax:wfc` | WFC: `Phi : Sigma -> nat` decreases on invalid states | DEF | hypothesis `wfc` (`Governance.v`), generalized `wfc_wf` (`GovernanceWF.v`) | |
| B7 | `ax:ubc` | UBC: `Phi <= M` | DEF | none | Not used by any Coq theorem. |
| B8 | `lem:finite-implies-ubc` | Finite `Sigma` and WFC imply UBC | NOT | none | S. Needs a finiteness notion (listing of states). |
| B9 | `def:stream`, `def:causal-order` | Event stream; causality-respecting order | DEF | `CausalReplay.causal` | |
| B10 | `as:closure`, `def:config` | Causal closure; configuration; enabled iff `deps(e)` disjoint from `B` | DEF | abstract `enabled` with persistence hypotheses `enabled_after_remove`, `enabled_after_comp` | The deps-based enabledness discharging those hypotheses is not proved (S, in WP1). |
| B11 | `def:grs` | Governance rewrite system (apply, compensation) | DEF | `Governance.step`, `GovernanceCausal.step` | Buffer as list, `remove1`. |
| B12 | `def:rhostar` | `rho*` is `rho^m` for the least `m` reaching validity; exists by WFC, unique by determinism | NOT | `rho_star` is a parameter with `rho_star_reach` (and `rho_star_valid` in `GovernanceConverse.v`) as hypotheses | S. Construct `rho*` from WFC by well-founded recursion and discharge `rho_star_reach`, `rho_star_valid`, idempotence. Removes two hypotheses from every headline theorem. |
| B13 | `ax:cc` | CC1 (co-enabled independent pairs), CC2 (absorption at invalid states) | DEF | `cc1_coenabled`, `cc2` (`GovernanceCausal.v`); all-pairs `cc1` (`Governance.v`) | |
| B14 | `rem:crdt-comparison` | Operation commutativity implies CC; CC strictly weaker | DIFF | `cmrdt_governed_SEC`, `gstep_commute`, `witness_converges`, `witness_not_cmrdt`, `compensation_free_exact` | Coq states convergence and strictness, not "implies CC1" verbatim; follows in one line from `gstep_is_apply`. |
| B15 | `rem:absorption` | CC2 generalizes to `rho*(apply(e, s)) = rho*(apply(e, rho*(s)))` | NOT | none | S. Induction on the compensation chain; needs B12's `rho* = rho^m`. |
| B16 | `def:processor` | Stream processor: eventual delivery, causal application, incremental compensation | DEF | none | Not formalized; see WP4. |
| B17 | `sec:example` | Order fulfillment: WFC, UBC (`M = 1`), CC1 and CC2 hold; P1 and P2 reach `(approved, 2)`; naive revert violates CC1 | NOT | none | S. Finite (12 states), decidable. IMPRECISE witness for the naive revert (finding 6). |
| B18 | `lem:termination` | GRS terminates; under UBC at most `|E| + (|E|+1) M` steps | PARTIAL | `terminating` (`Governance.v`), `governance_wf_terminating`, `causal_governance_wf_terminating` | Step bound missing. S. |
| B19 | `lem:local-confluence` | GRS locally confluent under CC (three critical-pair cases) | EXACT | `causal_locally_confluent_step` (`GovernanceCausal.v`, CC1 on co-enabled pairs), `locally_confluent_step` (all pairs) | Enabledness persistence is a hypothesis the paper derives from causal closure (B10). Neither lemma is gated; their consumers are. |
| B20 | `cor:unique-nf` | WFC + CC give unique normal forms (Newman) | EXACT | `causal_governance_unique_normal_forms`, `governance_unique_normal_forms`, `newman`, `confluent_of_SN`, `unique_normal_forms`; non-vacuity `example_confluent` | |
| B21 | `thm:convergence` | Stream convergence: (a) validity after compensation, (b) order independence, (c) agreement on equal received sets | DIFF | `causal_governance_unique_normal_forms`, `causal_convergence`, `run_tequiv`; `nf_valid_empty` | The processor model (time-indexed received sets) is not formalized. (b), (c) follow from unique normal forms in a few lines once it is; (a) needs "normal form implies valid" (immediate from `st_comp`). M (WP4). |
| B22 | `rem:set-function` | `F(E) = nf(sigma0, E)` is a function of the event set | DIFF | as B20; `causal_convergence` | Follows from B20. |
| B23 | `cor:quiescent` | Finite stream: processors eventually agree forever | NOT | none | S once B21's model exists (WP4). |
| B24 | `rem:infinite-streams` | Perpetual agreement for infinite streams | DEF | none | Restates B21 (c). |
| B25 | `thm:necessity` | For every `M`, `R_infinity` on `Z` has a reduction with more than `M` compensation steps | NOT | `zw_any_overdraft_repairs` is related (a different, one-sided registry; no step count) | S. IMPRECISE about CC of `R_infinity` (finding 9). |
| B26 | remark "What Fails" (after `thm:necessity`) | `R_infinity` satisfies WFC and CC, violates UBC | NOT | none | S, with B25. Needs `apply(e_n, -)` defined off 0 for the CC claim. |
| B27 | `prop:cc-necessary` | A registry with WFC and UBC and two causal orders reaching different valid normal forms | PARTIAL | `cc1_fail_diverge`, `cc_exact_from`, `cc_exact_global` (generic); no instance | The 4-state table instance (A, B, C, D) is not in Coq. S: instantiate `cc1_fail_diverge`. |
| B28 | remark after `prop:cc-necessary` | "Each condition is independently necessary for its guarantee" | PARTIAL | `cc_exact_from`, `jc_exact`; qualifiers `masked_cc1`, `rho_star_qualifier` | IMPRECISE (finding 7). UBC side is B25. |
| B29 | `thm:complexity` | `O(n)` model cost, `O(n log n)` with a priority queue | NOT | none | Cost model claim. Recommend: mechanize only the per-event step bound (`<= M` compensation steps per event, with B18) and keep the asymptotics at paper level (they concern data structures, not the theory). |
| B30 | 8.1 three regimes (prose) | Op-commutativity implies CC; I-confluence needs no compensation; NC subsumes both | PARTIAL | `CRDT.v` (`cmrdt_SEC`, `cmrdt_governed_SEC`, `cvrdt_SEC`, `witness_*`), `compensation_free_exact` | IMPRECISE on I-confluence (finding 8). |
| B31 | 8.2 CC patterns (prose list) | Canonical-state compensation, lattice compensation, decomposable repair each give CC | NOT | none | Pattern 1 FALSE AS STATED, pattern 2 IMPRECISE (finding 5). S for the counterexample and a corrected pattern 1 (canonical repair plus commuting operations on valid states). |
| B32 | `cor:infinite` | Stream convergence holds on any state space given a well-founded measure | DIFF | `governance_wf_confluent`, `governance_wf_unique_normal_forms`, `causal_governance_wf_confluent`, `governance_lex_confluent`; instance `zw_confluent` | Rewrite-system level; the stream level follows with WP4. The paper's witness `R_infinity` is not the Coq instance (`zw` repairs one way to a floor). |
| B33 | `def:inv-vector`, `def:footprint`, `def:perinv`, `def:decomp`, `def:repair-locality` | Calculus definitions | DEF | none | |
| B34 | `thm:strong-absorption` | `N(A_e(s)) = N(A_e(N(s)))` for all `e, s` implies CC2 | NOT | none | S. Uses `N(s) = N(rho(s))` for invalid `s` (from B12). |
| B35 | `lem:repair-commute` | Repair-local `e` commutes with `R_J` for `J` disjoint from `F(e)` | NOT | none | S. True. |
| B36 | `lem:repair-idempotent` | `R_J` fixes `J`-valid states and is idempotent | NOT | none | S. True (a fixed point of `r_i` satisfies `psi_i`, so commutation keeps `psi_i`). |
| B37 | `thm:footprint-cc1` | Disjoint footprints and repair locality give CC1 | NOT | none (`Gsm.disjoint_events_commute` is a different statement) | FALSE AS STATED (finding 3). L: needs a corrected statement first (candidate: state-variable footprints with per-variable repairs, generalizing `disjoint_events_commute`). |
| B38 | remark "Practical import" | Order-fulfillment events have disjoint footprints | NOT | none | FALSE AS STATED (finding 4). |
| B39 | `def:product` | Product registry | DEF | none | |
| B40 | `thm:product` | Product of WFC + CC registries is WFC + CC; decomposability lifts | NOT | none | M (S for WFC, CC2; CC1 needs product enabledness). True given `rho` fixes valid states. |

## Fed: `normalization_confluence_in_federated_registry_networks.tex`

### Restated Base results (sections 3 to 7 and 9)

Every Base row B1 to B31 and B33 to B40 appears in Fed with the same statement and the same status
(diffed line by line for this audit). Differences: Fed's `def:registry` makes `rho` deterministic and
moves the measure into WFC; Fed's remark "Machine-checked" adds the monotone-cycles core (see the
mechanization-claims section); Fed has no `cor:infinite` (B32).

### New results (section 6 and 8.2)

| # | Label | Statement (short) | Status | Coq | Notes |
|---|---|---|---|---|---|
| F1 | `def:morphism` | Registry morphism with shared/local split; M1 (validity under overwrite) | DEF | `FederationEvents.Common.c_m1` | |
| F2 | remark after `def:morphism` | Factored validity reduces M1; M1 nonvacuous under WFC | DEF | none | Trivial. |
| F3 | `def:network` | Tree-shaped network | DEF | `topoF` (acyclic, more general) | |
| F4 | `def:fed-registry` | Federated registry: product state, local and morphism invariants | DEF | `FederationEvents.Cons`, `Inv`; `Categorical.Consistent` | |
| F5 | `def:fed-comp` | `rho_Fed`: phase 1 local normalization, phase 2 repair in topological order | DEF | `FederationEvents.N` | |
| F6 | `lem:authority` | In a federally valid state: (a) sources at their normal form, (b) target shared = morphism image, (c) target local converges by component CC | PARTIAL | (b): `N_cons`, `frun_solves`, `solve_unique`; (a): `evstep_off`, sources have `f = id` | (c) REFUTED by `audit_counterexample` (finding 1). (a) as phrased ("equals its single-registry normal form") is not stated in Coq. S for (a), (b). |
| F7 | `lem:fed-termination` | One application of `rho_Fed` gives a federally valid state | DIFF | `N_inv`, `N_cons` (`FederationEvents.v`); `rhoFold_sound` | Coq assumes component validity on input (`rho` only fixes valid states). From arbitrary states needs a hypothesis that `rho j` lands in valid states, then follows. S. |
| F8 | `thm:fed-cc` | Tree + component WFC and CC imply federated CC | REFUTED | counterexamples `audit_counterexample`, `c2_counterexample`; corrected `fed_events_commute` (C1 + C2), exact `reach_commute_iff` | Finding 1. |
| F9 | `thm:fed-convergence` | Tree + M1 + component WFC and CC: processors converge | REFUTED | counterexamples as F8; corrected `fed_interleavings_converge`, `fed_permutations_converge`, `dist_interleavings_converge`; exact `fed_exact`, `fed_exact_full`, `acyclic_gc_iff`, `static_c1_c2_gc`; non-vacuity `supply_instance`, `supply_converges` | Finding 1. Coq's model is FedMachine apply sequences, not the federated GRS with `rho_Fed` as compensation; WP5 adds the GRS bridge. |
| F10 | `cor:fed-nf` | Constructive normal form: sources, then propagate, then local CC | PARTIAL | `frun_solves`, `N_cons`, `solve_unique`; `rhoFold_retraction` | The propagation part is mechanized; "local component converges via component CC" inherits F6 (c). |
| F11 | remark "Compensation Compatibility is Derived" | `phi(rho_A*) = rho_B*(phi)` is not needed | DEF | none | No formal claim beyond M1. |
| F12 | remark "Relationship to Product Composition" | Product composition is the case `E` empty | DEF | none | |
| F13 | `prop:cycle-necessary` | A cyclic network (flip and identity) with WFC, CC, M1 whose compensation cycles | DIFF | `negation_one_coordinated` (second conjunct: copy plus negation 2-cycle has no consistent state), `flip_no_section`, `tri_flip_no_section` | Coq proves "no federally valid state" for the same holonomy (labels placed on the other edge); "compensation never terminates" follows in one step, and the paper's exact 4-step trace is not in Coq. S. |
| F14 | `prop:m1-necessary` | Acyclic network violating M1 oscillates | NOT | none | S. |
| F15 | `rem:multisource` | Several sources break the authority argument | DEF | none | |
| F16 | `def:resolver`, `def:resolved-network` | Resolution operator with R1 (source determinacy), R2 (validity preservation) | DEF | `Common.c_local` (R1), `c_m1` (R2), `c_absorb` | |
| F17 | `lem:resolved-termination` | One application of `rho_Fed` on a resolved network is federally valid | DIFF | as F7 (`FederationEvents.v` covers multi-source `f j` reading `src j`) | S, with F7. |
| F18 | `thm:resolved-convergence` | Acyclic resolved network + M1 + R1/R2 + component WFC and CC: convergence | REFUTED | as F9 (the single-source counterexample is a special case) | Finding 1. |
| F19 | `cor:resolved-nf` | Constructive resolved normal form | PARTIAL | as F10 | |
| F20 | remark "Verified, not assumed" | R1 and R2 decidable by enumeration | NOT | none | Belongs to ROADMAP item 5 (federation oracle); recommend excluding from item 7. |
| F21 | remark "Necessity of the resolution conditions" | Acyclicity still necessary; R2 necessary like M1; R1 necessary for well-definedness | NOT | none | S for R2 (instance of F14 with a resolver). The R1 claim is IMPRECISE ("well-definedness" of what). |
| F22 | `def:lattice-shared` | Ordered shared domains; federated repair operator `Phi` | DEF | `FederationEventsCycles` `F`, `u` (abstract) | The paper's `Phi` built from morphisms and resolvers is not instantiated (WP6). |
| F23 | `thm:monotone-cycles` | Monotone `Phi` on complete lattices: lfp exists, Kleene and every fair chaotic iteration reach it; hence processors converge | PARTIAL | `kleene_lfp`, `lfp_unique`, `kleene_acc_lfp`, `kleene_finite_height_lfp`, `chaotic_reaches_lfp`, `chaotic_limit_unique`, `chaotic_acc_reaches_lfp`; engine normalizer `cyc_N_lfp`, `cyc_N_unique`, `cyc_sweep_order_independent`, `cyc_N_idem`; corrected last clause `cyc_events_converge_iff`, `gc_iff` | Last sentence REFUTED by `cyc_counterexample` (finding 2). Missing: complete lattices without ACC; validity of the lfp (assumed as `lfp_valid`); `Phi` built from the network. M (WP6). |
| F24 | `cor:acyclicity-monotone` | Acyclicity and monotonicity are two independent routes to federated confluence | PARTIAL | normal-form existence: `frun_solves` (acyclic), `cyc_N_lfp` (monotone) | True for the repair normal form; false for event interleavings without C1/C2 or GC (findings 1, 2). |
| F25 | remark "Order-independence is chaotic iteration" | Order-independent convergence is chaotic-iteration convergence | DIFF | `Chaotic.v` (`chaotic_reaches_lfp`, `chaotic_limit_unique`) | Productive-step reframing, not infinite fair schedules. |
| F26 | remark "CRDTs are compensation-free monotone federations" | State-based CRDT is the special case | DIFF | `cvrdt_SEC`, `cvrdt_absorbs_duplicates` | Not stated as an instance of F23. |
| F27 | `rem:infinite-lattice` | Complete lattice may be infinite; ACC or widening for computation; convergence unaffected | PARTIAL | `ChaoticACC.v` (`kleene_acc_lfp`, `kleene_acc_lfp_nn`, `chaotic_acc_reaches_lfp`, `ole_no_rank`, `pl_chaotic_reaches_lfp`) | IMPRECISE (finding 15). Non-ACC existence needs a classical Knaster-Tarski; recommend rewording rather than mechanizing. |
| F28 | `def:subfed`, `def:effreg` | Sub-federation, boundary, convexity; effective registry | DEF | none | |
| F29 | `thm:collapse` | Convex internally convergent `J`: (a) `R_J` is WFC + CC, (b) boundary M1 iff, (c) `N` converges iff `N'`, normal forms agree | PARTIAL | `rhoFold_compositional`, `rhoF_from_app` (operator-level fold-append) | (a)'s CC part relies on F9 (REFUTED), so it needs C1/C2 or GC in its hypotheses. (b), contraction acyclicity under convexity, and the effective registry are not modeled. M (WP8). |
| F30 | `cor:modular` | Modular and hierarchical verification | PARTIAL | as F29 | |
| F31 | remark "Convexity and the monotone regime" | Monotone sub-federation gives monotone `rho_Fed^J` | NOT | none | Doubtful (finding 14). S to decide (likely a counterexample). |
| F32 | 6.x example (manufacturer and supplier) | Concrete federation; both orders reach `(active, listed)` | NOT | `supply_instance` is a related but different instance | S: discharge `Common`, C1, C2 and apply `fed_permutations_converge`. |
| F33 | 8.2 "Two Regimes for Federated Repair", `tab:regimes` | Monotone repair converges on any topology; non-monotone needs acyclicity | PARTIAL | as F24 | Correct about the repair normal form; the text reads as event convergence, which needs GC (findings 1, 2). |

## Cat: `categorical_structure_of_federated_convergence.tex`

| # | Label | Statement (short) | Status | Coq | Notes |
|---|---|---|---|---|---|
| C1 | `lem:zero` | Idempotent `rho`: valid set = image = Fix = `eq(id, rho)` | EXACT | `image_iff_fixed`, `fixed_is_equalizer` (ungated), `retract_into_fixed`, `retract_fixes_fixed`; instance `clamp3_*` | Equalizer universal property in its axiom-free fragment (`mediator_*`). |
| C2 | `prop:one` | `L_F = eq(g, h)`, a finite limit | DIFF | `consistent_iff_equalizer` | Coq's `Consistent` omits "each component is in `Phi_{R_i}`" and the limit-composition step. Follows by instantiating the abstract state type with the product of fixed sets (S). |
| C3 | `thm:one` | `rho_F` is the idempotent retraction onto `L_F`; independent of the topological order | DIFF | `rhoFold_retraction`, `rhoFold_image_iff_consistent`, `rhoFold_sound`, `rhoFold_complete` (ungated), `rhoL_*` (ungated), `rhoF_retraction`; order: `order_independent`, `bubble`, `step_comm`, `updates_commute` | Coq's consistent set is the intrinsic `ConsistentList`, not `L_F`; the bridge (under M1/R2 and local idempotence, `ConsistentList` = `L_F`) is missing, and order-independence lives in `FederationOrder.v`'s different model. M (WP7). |
| C4 | `thm:two` | Flat and staged normalizers agree; a verified sub-federation collapses to an effective registry | DIFF | `rhoFold_compositional`, `rhoF_from_app` | The fold-append law is exact; "collapses to an effective registry" is not formalized (WP8, with F29). |
| C5 | 4, port refinement (prose) | Input ports, sealed variables, seam re-check | NOT | none | Stated as paper-level. M, in WP8. |
| C6 | `ex:glue` | Same valid set, different normalizers: union is order-dependent | EXACT | `gluing_order_dependent`, `rA_idem`, `rB_idem`, `agree_on_valid`, `disagree_as_normalizers` | |
| C7 | 5, "certificates form a sheaf", "two regimes force agreement" (prose) | Local certificates agreeing as normalizers on overlaps glue | NOT | none | IMPRECISE: no presheaf or site is defined. L (WP10). |
| C8 | `prop:gluing` | R1 + R2 is the sheaf gluing axiom | NOT | none | Stated as paper-level. Recommend reformulating as concrete lemmas (R1: merged value is a function of the sources; R2: it lands in the valid set; agreement on the overlap gives a confluent union) before mechanizing. M after reformulation, L as stated. |
| C9 | `thm:obstruction` | A section around a cycle exists iff the loop composite has a reachable fixed point | NOT | `Cohomology.has_section` is defined as a fixed point of `loop_composite` | IMPRECISE (finding 13). S for the general-map version (section of a cycle iff fixed point of the composite). |
| C10 | `thm:completion` | Torsor fiber: section iff the cocycle is a coboundary | EXACT | `section_iff_coboundary` (any graph, any group), `fixed_point_iff_trivial_holonomy` (single cycle) | Torsor identified with `G` by a base point, as in the paper's proof. |
| C11 | 6, "H^1 is holonomy" (prose) | Gauge-fix to a spanning tree; H^1 = fundamental holonomies modulo simultaneous conjugation; rank `|E| - |V| + 1`; trivial iff every fundamental loop is trivial | EXACT | `gauge_fix`, `gauge_fixed_holonomy`, `H1_classification`, `betti_number`, `tree_vertex_count`, `cycle_basis_criterion`, `sat_iff_trivial_holonomy`, `tree_unique`; instance `tri_flip_not_cohomologous_to_identity` | On the graph (1-skeleton). |
| C12 | 6, rank on the nerve as a 2-complex | Triangle relations can lower the rank | NOT | none | Stated as paper-level. L (WP10); ROADMAP lists it as lower value. |
| C13 | 6, "the two regimes are one picture" (prose) | Obstruction vanishes in exactly two ways: acyclic (no cycles) and monotone (lfp) | PARTIAL | `tree_has_section`, `betti_number` (acyclic); `kleene_lfp`, `cyc_N_lfp` (monotone) | "Exactly two ways" is IMPRECISE: trivial holonomy on a cyclic nerve is a third. |
| C14 | `ex:diag` | Copy-back settles, negation orbits | DIFF | `identity_holonomy_has_section`, `flip_no_section`, `copyback_zero_coordination`, `negation_one_coordinated` | The mathematics is mechanized; `DiagnoseCycle`'s behavior is gsm code. |
| C15 | 7, reading the diagnostic's result (prose) | Non-convergence from one seed is definitive; the diagnostic is a sound refuter | NOT | `nonfree_holonomy_counterexample` is a counterexample to the general claim | FALSE AS STATED for non-free or non-invertible composites (finding 12). S: counterexample plus the correct statement (sound for the regular action). |
| C16 | `prop:minimal` | Invertible fragment: coordination-free SEC iff `H^1 = 0`; coordinating a cycle basis suffices, strongly consistent only on those loops | PARTIAL | `tree_has_section`, `keep_balanced_suffices`, `unbalanced_blocks`, `coordinated_sound`, `coordinated_unique_nf`, `plan_exact`, `coordination_needed`, `coordinated_events_converge` | The "iff" with an implementation notion is not formalized and needs the qualifiers of finding 10. S to state the qualified iff from existing results. |
| C17 | 8, minimum coordination complexity | Group feedback edge set; NP-hard (abelian, edge bipartization); no constant approximation under UGC; FPT; polynomial on planar | CITED | none | |
| C18 | 8, "a correct polynomial size `<= b` coordination is always available" | Coordinate the orbiting fundamental cycles of any spanning tree | DIFF | `tree_has_section`, `keep_balanced_suffices`, `betti_number` | Size bound is `betti_number`; "polynomial" (time) is not stated and is evident from the construction. |
| C19 | 8, edge-disjoint obstructions | One coordinated edge per obstructing cycle, any `G` | PARTIAL | `simultaneous_section_iff` (bouquet of loops sharing one value) | General edge-disjoint (cactus) graphs not stated. S to M. |
| C20 | 8, `min_G >= min_{G^ab}` (general) | Every `G`-feasible coordination is abelian-feasible | PARTIAL | `section_G_implies_ab` (theta instance only), `sign_hom` | General statement (push a section forward along any group homomorphism, any graph) is S. |
| C21 | 8, `S_3` separation | Theta graph: `min_G = 2 > 1 = min_{G^ab}` | EXACT | `theta_separation`, `min_G_lower`, `min_G_attained`, `min_ab_lower`, `min_ab_attained`, `sign_hom`, `section_G_implies_ab`, `S3Sep.*` | |
| C22 | 8, non-invertible case (prose) | A cycle basis still suffices, same minimum | NOT | `noninvertible_balance_not_static` is related | Suspected FALSE AS STATED (finding 11). S for the counterexample and the root-oriented corrected form. |
| C23 | 3, background | WFC makes `rho_R` idempotent and its valid set non-empty | NOT | idempotence is a hypothesis (`idem` in `Categorical.v`) | S, with B12 (WP1). |
| C24 | 2, related work | "The monotone regime coincides with state-based CRDTs (machine-checked)" | PARTIAL | `cvrdt_SEC`, `cvrdt_absorbs_duplicates` | Only the CRDT-is-an-instance direction. |

## Gaps: proposed work packages

Each package owns one new Coq file, so packages run in parallel without editing each other's files.
The shared files (`_CoqProject`, `Makefile`, `verify.sh` gate list and its count, `coq/README.md`)
are touched by every package; dispatch each package on its own branch and let a final integration
step merge those lines and set the gate count. Every package must add each new headline theorem to
the gate and give a non-vacuity instance for every abstract result, matching the development's
existing practice.

Rows marked FALSE AS STATED or REFUTED need a corrected paper statement. Packages state the
corrected form in Coq and record a counterexample to the original as a theorem; the paper text is
revised in WP-P.

| Package | Items | New file | Builds on | Difficulty | Depends on |
|---|---|---|---|---|---|
| WP1. `rho*` and base facts | B12 (construct `rho*` from WFC; discharge `rho_star_reach`, `rho_star_valid`; idempotence), C23, B15 (CC2 lifts to `rho*`), B34 (strong absorption), B18 step bound under UBC, B8 (finite implies UBC), B10 (deps-based enabledness discharges `enabled_after_remove`, `enabled_after_comp`), B29 per-event step bound | `RhoStar.v` | `Governance.v`, `GovernanceCausal.v`, `GovernanceWF.v`, `Newman.v` | M (all S items) | none |
| WP2. Concrete instances | B17 (order fulfillment, exhaustive CC, both processors, naive revert failing at `(pending, 1)`), B25 + B26 (`R_infinity`, more than `M` steps, with `apply(e_n, -)` total), B27 (4-state instance via `cc1_fail_diverge`), F13 (paper's exact flip/identity oscillation), F14 (M1 oscillation), F21 (R2 oscillation with a resolver), F32 (manufacturer and supplier via `fed_permutations_converge`) | `PaperInstances.v` | `Governance.v`, `GovernanceConverse.v`, `FederationEvents.v`, `CoordinatedCycles.v` | M (all S items) | none |
| WP3. Verification calculus | B35, B36 (true lemmas), B37 (record both counterexamples of finding 3 as theorems; prove a corrected footprint theorem), B38 (counterexample), B31 (pattern 1 counterexample and corrected pattern), B40 (product lifting: WFC, CC1, CC2, decomposability) | `Calculus.v` | `Governance.v`, `GovernanceWF.v`, `Gsm.v` (`disjoint_events_commute`) | L (B37's corrected statement is a mathematical decision; the rest S to M) | none for Coq; WP-P adopts the corrected B37 |
| WP4. Stream processor model | B16 (formalize processors: time-indexed received sets, causal application, incremental compensation), B21 (a), (b), (c), B22, B23, B32 at stream level | `Stream.v` | `GovernanceCausal.v`, `GovernanceWF.v`, `CausalReplay.v` (`causal_convergence`), `Trace.v` | M | soft on WP1 (can use the current hypotheses and switch to WP1's `rho*` later) |
| WP5. Federated theorems in corrected form | F6 (a), (b) as stated plus F6 (c) recorded as refuted by `audit_counterexample`, F7 and F17 from arbitrary states, F10 and F19 corrected constructive normal form, bridge from Fed's federated GRS (apply plus `rho_Fed` compensation) to `Governance.step`, with unique normal forms iff C1/C2 at reachable witnesses (reuse `cc_exact_from`, `fed_exact`), and named corrected versions of F8, F9, F18 | `FederationGRS.v` | `FederationEvents.v`, `FederationEventsConverse.v`, `GovernanceConverse.v`, `Categorical.v` | M to L | none for Coq; WP-P adopts the statements |
| WP6. Monotone cycles completion | F23 (validity of the lfp from M1/R2 plus a hypothesis on bottom, or a counterexample showing the paper's claim fails; `Phi` built from morphisms and resolvers instantiating `FederationEventsCycles` hypotheses), F31 (decide; likely counterexample), F24, F27 (reword; mechanize only the ACC statement already present) | `MonotoneFederation.v` | `Federation.v`, `Chaotic.v`, `ChaoticACC.v`, `FederationEventsCycles.v` | M | none. Coordinate with ROADMAP item 6 (C1/C2 sufficiency on cycles), which touches the same theorem. |
| WP7. Categorical bridge | C2 (`L_F` with the component normal-form conjunct; product of equalizers), C3 (`ConsistentList` equals `L_F` under M1/R2 and local idempotence; `rhoFold` equals `FederationOrder.run` on a topological order, so `rhoFold` inherits `order_independent`) | `CategoricalBridge.v` | `Categorical.v`, `FederationOrder.v`, `FederationEvents.v` (`frun_solves`), `CoordinatedCycles.v` (`frun_run`, `topo_topoF`) | M | none |
| WP8. Compositional collapse | F29 (a) with corrected hypotheses, (b), (c); convex blocks are contiguous in some topological order and contraction preserves acyclicity; effective registry; F30; C4's collapse claim; C5 port refinement | `Collapse.v` | `Categorical.v` (`rhoF_from_app`), WP7, WP5 | M to L | WP7, WP5 |
| WP9. Cohomology completion | C9 (general maps: section of a cycle iff fixed point of the loop composite), C15 (refuter counterexample and the regular-action version), C16 (qualified iff from existing results), C19 (edge-disjoint cycles), C20 (functoriality along any group homomorphism, any graph), C22 (non-invertible counterexample and root-oriented corrected statement), C13 | `CohomologyGeneral.v` | `Cohomology.v`, `CohomologyGraph.v`, `CohomologyMin.v`, `CoordinatedCycles.v` | M (all S items) | none |
| WP10. Sheaf layer and nerve rank (optional) | C7, C8 (after reformulation), C12 (rank on the nerve as a 2-complex) | `Sheaf.v`, `NerveRank.v` | `Cohomology.v`, `CohomologyGraph.v` | L | WP-P reformulation of C7, C8 |
| WP-P. Paper revision (not a Coq package) | Replace F8, F9, F18, F23's last clause, F24, F33 and Fed's abstract, contributions and conclusion with the C1/C2 and GC forms; fix B31, B37, B38, B17's witness, the "CC is necessary" framing (B28), B30, B25/B26 imprecision; add the qualifiers to C15, C16, C22 and define "reachable" in C9; update both "Machine-checked" remarks | the three `.tex` files | this map | M | WP3 (B37), WP5, WP6, WP9 for the final corrected statements |

Out of scope for item 7 (recommend recording as such in ROADMAP): C17 (cited), the asymptotic part of
B29 (data-structure cost; WP1 covers the step bound), F20 (decidability of R1/R2; ROADMAP item 5).

Suggested dispatch: wave 1 runs WP1, WP2, WP3, WP4, WP5, WP6, WP7, WP9 in parallel (comparable
size, M each, WP3 and WP5 at the upper end); wave 2 runs WP8 after WP5 and WP7, and WP-P after
WP3, WP5, WP6 and WP9; WP10 is optional and last.
