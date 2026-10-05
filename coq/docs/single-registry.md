# Single registry

Detailed results for the single-registry modules: the Convergence Theorem and Newman's Lemma, its
non-vacuity, gsm's certification arguments, the exact converses (free delivery, any enabledness, any
well-founded potential, enabledness a compensation step can disable), the constructed `rho*`, and
the verification calculus. Each module's one-line summary is in the [module
index](../README.md#modules-by-regime); the status of each question in this regime is in
[REGIME-AUDIT.md](../../REGIME-AUDIT.md#1-single-registry), section 1.

## What is proven

- **`Newman.v`**: Newman's Lemma, fully self-contained (no external libraries, no axioms): a
  strongly-normalizing, locally confluent abstract rewrite system is confluent (`newman`,
  `confluent_of_SN`) and therefore has unique normal forms (`unique_normal_forms`). This is the
  exact inference the paper invokes to conclude global confluence from termination + local
  confluence.
- **`Governance.v`**: the paper's Governance Rewrite System (Def. "Governance Rewrite System"),
  with its two rules (apply / compensation), and the derivations:
  - `terminating`: Lemma "Termination": the lexicographic measure `(|B|, Phi(sigma))` strictly
    decreases at every step, so the system is strongly normalizing.
  - `locally_confluent_step`: Lemma "Local Confluence": the three critical-pair cases
    (apply/apply, apply/compensation, compensation/compensation) close, using CC1 and CC2.
  - `governance_confluent`, `governance_unique_normal_forms`: Cor. "Unique Normal Forms":
    confluence and unique normal forms, obtained by applying the machine-checked Newman's Lemma.

## What it rests on (and what it does not)

`Print Assumptions governance_confluent` reports **"Closed under the global context"**: the
theorem depends on no axioms and no admitted lemmas. Its only inputs are the paper's own named
conditions, taken as Coq hypotheses (each annotated in `Governance.v`):

| Coq hypothesis | Paper counterpart |
|---|---|
| `wfc` | Axiom WFC (Well-Founded Compensation): compensation strictly decreases the potential |
| `rho_star_valid`, `rho_star_reach` | Def. "Iterated Compensation": rho* reaches validity and is reachable by compensation steps |
| `cc1` | Axiom CC1 (order independence) |
| `cc2` | Axiom CC2 (compensation absorption) |
| `enabled_after_remove`, `enabled_after_comp` | the enabledness-persistence facts used in the Local Confluence proof (Case 1 and Case 2) |

Scope: the registry operators (`apply`, `rho`, `valid`, `Phi`, `enabled`) are abstract,
**exactly at the paper's level of abstraction**: the paper likewise treats them abstractly and
states WFC/CC as conditions a registry must satisfy. So this development mechanizes *the paper's
theorem*: given any registry meeting WFC and CC, confluence and unique normal forms follow, with
no gaps and no hidden assumptions. It does not (and the paper does not) prove that a particular
registry satisfies WFC/CC; that is a per-registry obligation, discharged in the paper's
worked examples and, for the reference implementation, exercised by `gsm`'s `confluence_test.go`.

## Defensibility (`Defensibility.v`)

A mechanized proof that merely compiles can still be weak in ways `coqc` does not catch. This
file rules out the two that matter:

- **Non-vacuity.** If the hypotheses (WFC, CC1, CC2, rho* reachability, enabledness) were jointly
  unsatisfiable, the theorem would be about nothing. `Defensibility.v` exhibits a concrete
  registry (debt counter: `apply = S`, `rho = pred`, valid at zero, `rho*` repairs to zero) that
  discharges *every* hypothesis and yields `example_confluent : confluent step_` and
  `example_unique_nf` with no hypotheses and no axioms. `Print Assumptions example_confluent`
  is "Closed under the global context". `instance_has_a_real_peak` shows the instance genuinely
  branches (two applies + a compensation from one configuration), so this is closing real
  nondeterminism, not a degenerate system.
- **Discrimination.** If `confluent` were provable for every relation, proving it would say
  nothing. `not_confluent_tri` proves a concrete three-element relation is *not* confluent, so
  the predicate is falsifiable.

Together with the axiom-free `Print Assumptions` on the abstract theorem, this is the argument
that the mechanization is strong: correct definitions (standard rewriting theory), satisfiable
hypotheses (a real model), a discriminating conclusion, and no hidden assumptions.

## Implementation soundness (`Gsm.v`)

The theorem is conditional on WFC and CC. `Gsm.v` mechanizes the soundness of the two arguments
the reference implementation (`gsm`) uses to *certify* those conditions at build time, so the
result attaches to how gsm actually establishes its hypotheses, not just to an illustrative
model:

- **CC by footprint disjointness** (`disjoint_events_commute`): over a valuation state model
  mirroring gsm's bitpacked `State` (a write touches only its variable's field),
  `write_comm` proves disjoint-variable writes commute (Leibniz, no funext), from which two
  events with disjoint footprints commute compositionally. This is gsm's `PairsDisjoint`
  certification path (the one that avoids brute-force enumeration).
- **WFC by a well-founded potential** (`repair_terminates`): a repair that strictly decreases a
  natural-number potential whenever the state is invalid is strongly normalizing. This is the
  fact behind gsm's cycle-detection WFC check.

Concrete witnesses (`inc0_inc1_commute`, `ex_repair_terminates`) discharge both with no
hypotheses; `Print Assumptions` on all four results is "Closed under the global context". The
brute-force CC path is a finite decidable enumeration whose soundness is definitional, so it is
not mechanized; the disjointness path is the substantive one.

## The converse: CC and causal convergence are exact (`GovernanceConverse.v`)

`Governance.v` (above) and the causal modules ([causal.md](causal.md)) prove CC (single
registry) and commutation of concurrent pairs (causal delivery) sufficient. `GovernanceConverse.v` proves the converses, in the strongest form that is
true, and records where the naive converse fails. Axiom-free. Write `gov e s = rho_star (apply e s)`
for the governed step.

**Single registry, free delivery** (every buffered event may fire; the rewrite system is
`Governance.v`'s, reused verbatim), with WFC and canonical repair (`rho_star` returns a valid
state):

- `cc1_runs`, `cc2_runs`: the two sides of CC1 at `s` are the normal forms of the runs
  `e1` then `e2` and `e2` then `e1` from `(s, [e1; e2])`; the two sides of CC2 at an invalid `s`
  are the normal forms of apply-then-repair and repair-then-apply from `(s, [e])`. So
  `cc1_fail_diverge` and `cc2_fail_diverge`: a CC failure is two runs with distinct normal forms.
- `reach_run`, `cc1_fail_diverge_from`, `cc2_fail_diverge_from`: every state reachable from `s0`
  (by events and compensation) is reached by delivering some word `w` first, so a CC failure at a
  reachable state is a divergence of two event orders from `(s0, w ++ [e1; e2])` or
  `(s0, w ++ [e])`.
- `cc_exact_from` (headline): every event buffer delivered from `s0` has a unique normal form
  **if and only if** CC1 and CC2 hold on the states reachable from `s0`. `cc_exact`: the same for
  every configuration over a reachable state. `cc_exact_global`: CC everywhere iff unique normal
  forms everywhere.
- Sufficiency only needs CC on reachable states, for any enabledness: `newman_on` (Newman's Lemma
  localized to a step-closed set) gives `cc_reach_unique_normal_forms`, which generalizes
  `governance_unique_normal_forms` and `causal_governance_unique_normal_forms` (CC1 on co-enabled
  pairs and CC2, both only at reachable states).

**Single registry, any enabledness (causal, guarded).** Here CC1 is not necessary, and the exact
condition is CC modulo the rest of the run:

- `jc_exact`: from a start configuration `c0`, the system is confluent iff `JC c0`: at every
  configuration reachable from `c0`, the governed successors of each critical pair are joinable
  (`(gov e1 s, B \ e1)` with `(gov e2 s, B \ e2)` for co-enabled `e1 <> e2`; `(gov e s, B \ e)`
  with `(gov e (rho s), B \ e)` for invalid `s`). CC1 and CC2 are the case where the join is an
  equality (`cc_reach_jc`). `jc_unique_normal_forms`: `JC c0` gives unique normal forms from `c0`.

**Counterexamples to the naive converse.**

- `rho_star_qualifier`: the qualifier "canonical repair" is needed. `Governance.v` only asks that
  `rho_star s` be a reduct of `s`, which the identity satisfies; with it CC1 fails (set-true and
  flip do not commute), yet every configuration has a unique normal form (repair resets to the
  only valid state).
- `masked_cc1`: under causal enabledness, CC1 can fail for two co-enabled events at a reachable
  configuration while every run reaches the same normal form. `M1` writes 1, `M2` writes 2, and a
  reset `MR`, enabled only after both, erases the difference: from `(0, [M1; M2; MR])` every
  normal form is `(0, [])`. So "CC fails at a reachable state, hence two orders diverge" is false
  once the future of the run is constrained; `JC` is the exact condition there.

**Causal delivery** (the run model of `CausalReplay.v`):

- `CCR s0`: for every concurrent pair `a`, `b` and every prefix `p` such that `p ++ [a; b]` is
  causally consistent, the governed steps of `a` and `b` commute at `run p s0`.
- `causal_exact`: causal convergence from `s0` (any two causally consistent permutations reach the
  same state) **if and only if** `CCR s0`. Sufficiency (`ccr_convergence`) goes through
  `causal_tequiv` and the fact that swapping a concurrent adjacent pair preserves causal
  consistency (`causal_swap`, `tequiv_causal`); necessity (`ccr_diverge`) exhibits the two
  causally consistent permutations `p ++ [a; b]` and `p ++ [b; a]` with different results.
- `causal_convergence_exact`: with happens-before irreflexive, causal convergence from every start
  iff governed steps commute on every concurrent pair at every state: the converse of
  `causal_convergence`. Irreflexivity is needed: an event with `hb a a` appears in no causal order.
- `naive_causal_converse_fails`: `NA` and `NB` are concurrent and do not commute at state 1, which
  the causally consistent run `[NC]` reaches from 0, yet causal convergence holds from 0, because
  `NC` is causally after both and neither can be delivered after it. Reachability of the
  non-commuting state is not enough; the pair must be deliverable after the prefix, as in `CCR`.

## Finiteness only for checking (`GovernanceWF.v`, `ChaoticACC.v`)

The convergence theorems of this development never needed a finite state space, but two of them used a
natural-number measure: the WFC potential (`Governance.v`) and the rank of finite height
(`Chaotic.v`). These modules remove both, axiom-free:

- `governance_wf_confluent`, `governance_wf_unique_normal_forms` (`GovernanceWF.v`): the
  Convergence Theorem with WFC over an **arbitrary well-founded order**: the potential
  `Phi : State -> P` takes values in any type `P` with any well-founded strict order `ltP`, and
  compensation lowers it (`ltP (Phi (rho s)) (Phi s)` for invalid `s`). Termination is
  lexicographic on `(|B|, Phi s)` (`wf_lex2`, `governance_wf_terminating`); local confluence is
  `Governance.v`'s lemma unchanged. The causal theorem generalizes the same way
  (`causal_governance_wf_confluent`). Corollaries: the nat-valued theorems of `Governance.v` and
  `GovernanceCausal.v` with identical statements (`governance_confluent_from_wf`,
  `causal_governance_confluent_from_wf`), a potential into a lexicographic product
  (`governance_lex_confluent`), and no potential at all, only well-founded compensation
  (`governance_comp_wf_confluent`).
- Non-vacuity on an infinite domain: a withdrawal registry on `Z` (any balance, overdrafts of any
  depth; repair adds 1 up to the floor 0; potential `-s` under `Zwf 0`) discharges every
  hypothesis (`zw_confluent`, `zw_unique_normal_forms`, `zw_any_overdraft_repairs`).
- `chaotic_acc_reaches_lfp`, `chaotic_acc_terminates` (`ChaoticACC.v`): chaotic iteration reaches
  the least fixed point under the **ascending chain condition below the least fixed point**
  (well-foundedness of the converse of the strict order there), with no rank into `nat`.
  `chaotic_reaches_lfp_from_acc` recovers `Chaotic.chaotic_reaches_lfp` with an identical
  statement.
- Kleene iteration under ACC: `kleene_acc_not_forever` (constructive, no extra assumption: the
  iteration from bottom cannot strictly ascend forever) and `kleene_acc_lfp_nn` (a least fixed
  point cannot fail to exist); with the stabilization test `f x = x` decidable,
  `kleene_acc_stabilizes` and `kleene_acc_lfp` compute the stabilizing index and the least fixed
  point. `finite_height_acc` and `kleene_finite_height_lfp` recover the finite-lattice reading.
- Non-vacuity: `option nat` with `None` at the bottom and `Some n` in reverse order satisfies ACC
  (`ole_acc`) but has ascending chains of every length and admits no strictly increasing rank
  (`ole_no_rank`), so `Chaotic.v`'s hypotheses cannot be met on it. On its square with a monotone
  two-component operator, chaotic iteration and Kleene iteration both reach the least fixed point
  (`ple_acc`, `ple_no_rank`, `pl_chaotic_reaches_lfp`, `pl_chaotic_from_bot`,
  `pl_kleene_lfp_value`).

What still uses finiteness: deciding the hypotheses. Exhaustive checking (gsm, the table and
rules oracles) needs a finite state space to be a decision procedure; the theorems do not.
Computing the Kleene limit needs the stabilization test to be decidable; without it the
development proves only the double-negated existence, which is the constructive limit (deciding
`f x = x` in general is not possible).

## rho* constructed from WFC (`RhoStar.v`)

Earlier modules take iterated compensation `rho_star` as a parameter, with the hypotheses
`rho_star_reach` (and `rho_star_valid` in `GovernanceConverse.v`). The paper defines it instead
(Base, Def. "Iterated Compensation"): `rho*(s) = rho^m(s)` for the least `m` with `V(rho^m(s))`.
`RhoStar.v` constructs that operator from WFC (and a decidable validity test, which the paper's
Boolean `V_R` is) and proves every base fact that rests on it, axiom-free (61 gated results):

- Construction: `rho_star` (nat measure, computable by fuel) and `rho_star_wf` (any well-founded
  order, by well-founded recursion). `base_def_rhostar` and `base_def_rhostar_least_unique` are the
  paper's definition exactly (the least `m` exists and determines `rho*`); `rho_star_canonical`
  shows the operator does not depend on the measure. Notation (i) to (iii) of Base section
  "Calculus": `rho_star_valid`, `rho_star_fix`, `rho_star_idem`; `rho_star_rho` (rho(s) lies on
  the chain of an invalid s).
- Headline theorems with no rho* hypothesis: `wfc_governance_confluent`,
  `wfc_governance_unique_normal_forms`, `wfc_causal_governance_confluent`,
  `wfc_causal_governance_unique_normal_forms`, `wfc_governance_wf_confluent`,
  `wfc_causal_governance_wf_confluent`, `wfc_cc_exact_from` (both rho* hypotheses discharged).
- Deps-based enabledness (Base def:config: `e` in `B` is enabled iff `deps(e)` is disjoint from
  `B`) discharges `enabled_after_remove` and `enabled_after_comp` in both rewrite systems
  (`deps_enabled_after_remove`, `deps_enabled_after_comp`, `deps_causal_enabled_after_remove`,
  `deps_causal_enabled_after_comp`), and co-enabled events are causally independent
  (`deps_coenabled_independent`). So Base cor:unique-nf holds in the paper's own terms with only
  WFC, CC1 and CC2 as hypotheses: `paper_causal_governance_confluent`,
  `paper_causal_governance_unique_normal_forms` (CC1 on distinct, independent, co-enabled pairs),
  and the all-pairs versions `paper_governance_confluent`, `paper_governance_unique_normal_forms`.
- Absorption: `base_rem_absorption` (CC2 lifts to `rho*(apply(e, s)) = rho*(apply(e, rho*(s)))`),
  `base_rem_absorption_enabled` (CC2 for enabled events only), `base_thm_strong_absorption` (strong
  absorption implies CC2), and the equivalence `strong_absorption_iff_cc2`.
- UBC: `base_lem_finite_implies_ubc` (a listed state space gives `M = max Phi`, attained when there
  is a state); the step bound of Lemma "Termination", every reduction from `(s, E)` has at most
  `|E| + (|E| + 1) M` steps (`base_lem_termination_bound`, `causal_lem_termination_bound`), attained
  (`lv_termination_bound_tight`); the model-level part of Theorem "Convergence Complexity": at most
  `M` compensation steps per applied event plus `M` before the first
  (`base_thm_complexity_comp_total`, `base_thm_complexity_per_event`, `rho_star_steps_le_measure`).
- Cat section 3 background: WFC makes the normalizer idempotent (`cat_bg_rho_idempotent`), reaches
  a valid state from any state (`cat_bg_valid_from_any_state`), and Lemma 0 holds for it with the
  idempotence hypothesis of `Categorical.v` discharged (`cat_bg_lemma_zero`). The unqualified
  "its valid set is non-empty" needs a state: the empty registry satisfies WFC with an empty valid
  set (`cat_bg_nonempty_needs_a_state`).
- Non-vacuity: a four-level saturating counter (`lv_*`: finite, WFC, UBC with `M = 1`, CC1, CC2,
  strong absorption, deps-based enabledness for any dependency map) discharges every hypothesis
  set; the unbounded withdrawal registry of `GovernanceWF.v` gets its rho* constructed
  (`zw_rho_star_built`, `zw_confluent_built`).

## The exact converses over any well-founded order (`GovernanceWFConverse.v`)

`GovernanceConverse.v` states its exact converses (`jc_exact`, `cc_exact_from`) and `RhoStar.v`
its constructed form (`wfc_cc_exact_from`) with a potential `Phi : State -> nat`. The proofs use
the potential only for termination. This module lifts all three to WFC over any well-founded order
(the setting of `GovernanceWF.v`), with lexicographic and potential-free forms, axiom-free (50
gated results):

- Termination, exactly. With `comp_rel s' s := ~ V s /\ s' = rho s`: the Governance Rewrite System
  terminates from every configuration iff `comp_rel` is well-founded (`terminating_iff_comp_wf`,
  any enabledness), and `comp_rel` is well-founded iff WFC holds for some potential into some
  well-founded order (`comp_wf_iff_wfc`). With `V` decidable a well-founded `comp_rel` already has a
  nat potential, the number of compensation steps to validity (`comp_wf_nat_potential`): the lift
  adds generality where `V` is not decidable, and elsewhere accepts an ordinal or lexicographic
  measure as is instead of requiring a nat-valued one.
- Canonical repair implies termination: if `rho*` is reached by compensation steps and is valid,
  `comp_rel` is well-founded (`canonical_comp_wf`, `canonical_free_comp_wf`). WFC is a consequence
  of canonical repair, not an extra hypothesis.
- `sn_jc_exact`: for any enabledness and any `c0` from which the system terminates, confluence from
  `c0` iff `JC c0`. Termination is needed only from `c0`. Corollaries: `wf_jc_exact` (any
  well-founded potential), `lex_jc_exact` (a lexicographic product), `comp_wf_jc_exact`
  (compensation well-founded, no potential), `canonical_jc_exact` (canonical repair, no potential
  and no termination hypothesis).
- `canonical_cc_exact_from`: free delivery and canonical repair, with no termination hypothesis:
  every event buffer delivered from `s0` has a unique normal form iff CC1 and CC2 hold on the
  states reachable from `s0`. `wf_cc_exact_from` is the same statement with a potential into any
  well-founded order. The canonical-repair qualifier is still needed (`rho_star_qualifier`).
- rho* constructed by `RhoStar.rho_star_wf` (no rho* hypothesis): `wf_cc_exact_from_built`,
  `wf_jc_exact_built` (any well-founded potential), `comp_wf_cc_exact_from_built`,
  `comp_wf_jc_exact_built` (rho* built from a well-founded `comp_rel`, `rho_star_comp`).
- The nat statements recovered with identical types (checked by unification):
  `jc_exact_from_wf` (`GovernanceConverse.jc_exact`), `cc_exact_from_from_wf`
  (`GovernanceConverse.cc_exact_from`), `wfc_cc_exact_from_from_wf` (`RhoStar.wfc_cc_exact_from`).
- Non-vacuity. The `Z` withdrawal registry of `GovernanceWF.v` (potential `-s` under `Zwf 0`):
  `zw_unique_from` (rho* given), `zw_unique_from_built` (rho* built from the `Z` potential),
  `zw_comp_wf` and `zw_unique_from_comp_wf` (potential-free), `zw_jc` (JC at every configuration).
  A lexicographic escalation queue on `nat * nat` (an escalated item repairs into two routine
  items, routine items over a cap of 3 drain one at a time, potential the state itself under
  `lex2 lt lt`): `qe_built` (the constructed rho* is the closed form), `qe_unique_from` (arrival
  events: CC1, CC2, unique normal forms from every start). Adding a "clear routine" event breaks
  CC1 at the start state (`qr_cc1_fails`), and the iff turns that into a failure of unique normal
  forms (`qr_not_unique`).

## Compensation that disables a buffered event (`EnabledAfterComp.v`)

`jc_exact` and `sn_jc_exact` assume `enabled_after_comp`: a compensation step never disables a
buffered event that was enabled. JC uses it to close the event/compensation critical pair by firing
the event after the compensation, comparing with `rho* (apply e (rho sigma))`. This module drops
the hypothesis and gives the exact condition for any enabledness (51 gated results, axiom-free):

- The critical pairs at `(sigma, B)` are event/event (distinct `e1`, `e2` enabled) and
  event/compensation (`sigma` invalid, `e` enabled at `sigma`), whose successors are
  `(apply e sigma, B - e)` and `(rho sigma, B)` whether or not compensation disables `e`. An event
  that compensation enables creates no peak at `(sigma, B)`, only later steps.
- `JCg c0` (JC'): at every configuration reachable from `c0`, the event/event clause of JC, and for
  every `e` enabled at an invalid `sigma`, `(rho* (apply e sigma), B - e)` joinable with
  `(rho sigma, B)` itself. **`jcg_exact`**: for any enabledness and any `c0` from which the system
  terminates, confluence from `c0` iff `JCg c0` (Newman localized, `newman_on`).
  `jcg_iff_critical`, `cr_iff_critical`: `JCg c0` is exactly joinability of every critical pair at
  every configuration reachable from `c0`.
- `JCsplit c0` splits the event/compensation clause: JC's clause when `e` stays enabled at
  `(rho sigma, B)`, the join with `(rho sigma, B)` when compensation disables it.
  `jcsplit_exact`: under termination from `c0` and decidability of enabledness after compensation
  (`emloc`, implied by `enabled_after_comp`), confluence from `c0` iff `JCsplit c0`.
- Reduction to JC. `jcsplit_iff_jc`: under `enabled_after_comp` the disabled clause is vacuous and
  `JCsplit c0 <-> JC c0` (no termination hypothesis); `jc_jcg`, `jcg_iff_jc`. The old results are
  corollaries: `jc_exact_recovered` and `sn_jc_exact_recovered` are derived from `jcg_exact`, with
  types checked against `GovernanceConverse.jc_exact` and `GovernanceWFConverse.sn_jc_exact`.
- Normal forms. `gnf_iff`: `(sigma, B)` is a normal form iff `sigma` is not invalid and every event
  of `B` is disabled at `(sigma, B)`. The buffer need not be empty (`stuck_nf`, `stuck_nf_iff`), and
  uniqueness of normal forms is uniqueness of the pair (state, residual buffer). Under free
  delivery no event is ever stuck (`free_nf_empty`).
- Counterexample: JC is not sufficient. A `Pending` payment (invalid) is compensated to
  `Cancelled`; the guarded event `Settle` may not fire on a cancelled payment and moves any state to
  `Settled`. JC holds at every configuration (`dc_jc`), compensation disables `Settle`
  (`dc_eac_fails`), and from `(Pending, [Settle])` there are two normal forms, `(Settled, [])` and
  the stuck `(Cancelled, [Settle])` (`dc_two_normal_forms`, `dc_stuck`, `dc_jc_insufficient`,
  `dc_not_cr`); JC' fails there (`dc_not_jcg`). With the guard removed the same data are confluent
  (`fr_confluent`, through `jc_exact_recovered`).
- Non-vacuity, and JC is not necessary either. An account `Over` its limit is compensated to
  `Locked` (mid-repair, invalid) and then to `Ok`; `Reset` is guarded off while `Locked` (applied
  there it would give a `Torn` snapshot). Compensation `Over -> Locked` disables `Reset` and
  `Locked -> Ok` enables it again (`nv_disables`, `nv_enables`, `nv_not_eac`). JC' holds at every
  configuration (`nv_jcg`, also `nv_jcsplit`), so every configuration is confluent
  (`nv_confluent`, `nv_unique`), while the old JC fails at `(Over, [Reset])` (`nv_not_jc`,
  `nv_jc_not_necessary`): it asks for a join with `rho* (apply Reset Locked) = Torn`, which no run
  reaches. Without `enabled_after_comp`, JC is neither sufficient nor necessary; JC' is exact.

## Verification calculus for CC (`Calculus.v`)

The Base paper's section "Verification Calculus for CC" (`sec:calculus`), its "Practical import"
remark, pattern 1 of section 8.2 and product composition (PAPER-MAP rows B31, B33, B35 to B40).
A registry has invariants `psi i` indexed by a list `all`, validity is their conjunction, `rho`
fixes valid states and decreases a measure on invalid ones, and `N = rho*` (`IsRegistry`).
Per-invariant repairs (`PerInv`: R1 to R3), `Decomposable`, `IsFootprint`, `RepairLocal` and
`DisjointFP` are the paper's definitions.

Exact: `base_lem_repair_commute` (`lem:repair-commute`), `base_lem_repair_idempotent`
(`lem:repair-idempotent`), `calc_decomp_normalizer` (the Notation facts (i) to (iii) for a
decomposable normalizer), `base_thm_product` (`thm:product`: WFC, `rho*`, CC1 and CC2 lift; CC1
for a product pair holds iff it holds in both components) and `base_thm_product_decomposable`
(repairs, footprints composed by union, repair locality and disjointness lift).

Refuted. `thm:footprint-cc1` is false as stated: `base_thm_footprint_cc1_refuted` (no
invariants, `x := 1` and `x := 2`) and `base_thm_footprint_cc1_raw_refuted` (four states, raw
events commute, CC1 fails at an invalid state). The "Practical import" remark is false:
`base_rem_practical_import_refuted` (every footprint of approve and of credit contains the one
invariant); its other half is true (`calc_order_credit_repair_commute`). Pattern 1 ("canonical
state gives CC1 and CC2 trivially") fails for both conditions: `base_pattern1_cc1_refuted`,
`base_pattern1_cc2_refuted`.

Corrected footprint theorem. Under the paper's hypotheses (H1) disjoint footprints and (H2)
repair locality:

- `calc_footprint_cc1_iff`: CC1 at `s` iff
  `N(A_e2(A_e1(R_F(e2) s))) = N(A_e1(A_e2(R_F(e1) s)))` (exact, every state).
- `calc_footprint_cc1_valid_iff`, `calc_footprint_cc1_valid`: at a valid state, CC1 iff the two
  events commute up to `N` (`N(A_e2(A_e1 s)) = N(A_e1(A_e2 s))`). This is the form gsm checks
  (CC1 on valid states).
- `calc_footprint_cc1`: at every state, CC1 follows from (H2), footprint absorption
  (`FPAbsorb`: `N(A_e(R_F(e) s)) = N(A_e s)`, a per-event check on the event's own footprint
  repairs) and commutation up to `N`. Disjointness is not needed.
- `calc_fp_absorb_iff_sa`, `calc_cc2_strong_absorption`, `calc_cc1_iff_commute_under_cc2`:
  footprint absorption is strong absorption for a repair-local event, CC2 implies strong
  absorption, and under CC2 the CC1 of a pair is exactly commutation up to `N`.
- `calc_components_cc1_valid`, `calc_components_cc1_iff`: gsm's footprint components (state
  `S1 * S2`, normalizer componentwise, each event inside one component) satisfy CC1 at every valid
  state with no further hypothesis; at an invalid state CC1 holds iff each event absorbs `N` in
  its own component.

Each added hypothesis is needed: `calc_valid_needs_commute`, `calc_valid_needs_disjoint`,
`calc_valid_needs_repair_local`, `calc_all_needs_commute`, `calc_all_needs_absorb`,
`calc_all_needs_repair_local` (every other hypothesis holds, CC1 fails). Non-vacuity:
`calc_clamp_instance` (two clamped counters, disjoint footprints), `calc_order_cc1` (the paper's
order-fulfillment registry: overlapping footprints, CC1 at every state by `calc_footprint_cc1`,
CC2 for both events), `calc_components_instance`, `calc_product_instance`.

Corrected pattern 1: `calc_canonical_cc2_iff` (with canonical compensation to `bot`, CC2 for `e`
iff `N(A_e s) = N(A_e bot)` for every invalid `s`) and `calc_canonical_pattern` (with that check
for both events, CC1 iff commutation up to `N`); non-vacuity `calc_canonical_instance`.
