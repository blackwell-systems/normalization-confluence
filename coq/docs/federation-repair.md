# Acyclic federation: the repair normal form

Detailed results for the acyclic-federation repair modules: the categorical core (limit, retraction,
compositionality, order-independence), the bridge to the companion paper's statements, the federated
theorems in corrected form, sheaf gluing over sub-federation covers, and the categorical-layer
roadmap. Each module's one-line summary is in
the [module index](../README.md#modules-by-regime); the status of each question in this regime is in
[REGIME-AUDIT.md](../../REGIME-AUDIT.md#6-acyclic-federation-the-repair-normal-form), section 6.

## Categorical core (`Categorical.v`)

The first structural results of the companion paper's federation-as-limit account, mechanized at the
paper's level of abstraction: the normalizer is an abstract idempotent endomap, exactly as
`Governance.v` treats the registry operators. All axiom-free.

- **Lemma 0 (a registry is an equalizer).** `image_iff_fixed`: for an idempotent `rho`, the image
  and the fixed-point set coincide (`(exists y, rho y = x) <-> rho x = x`), the forward direction
  being idempotence itself. `fixed_is_equalizer`: the fixed-point set is the equalizer of `id` and
  `rho` (its carrier is `{x | id x = rho x}`), a limit in `Set`.
- **Theorem 1 (retraction, abstract skeleton).** `retract_into_fixed` and `retract_fixes_fixed`:
  `rho` lands in the fixed set and fixes it, so it splits the inclusion of the fixed set into the
  state space, i.e. it is a retraction onto that set (the limit `L`). The equalizer universal
  property is given in its axiom-free fragment (`mediator_lands_in_fixed`, `mediator_values_unique`);
  full uniqueness into the subset type needs proof irrelevance of the membership predicate, which
  holds when the state type has decidable equality (gsm's finite states), so it is noted rather than
  assumed.
- **Proposition 1 (the consistent set is a finite limit).** `consistent_iff_equalizer`: the
  federated consistent set (every target's shared component equals its resolver value) is exactly
  the equalizer of the two parallel maps that send a state to the tuple of shared components and the
  tuple of resolver values over the targets. The product over targets is modeled as a list, so the
  equalizer characterization is axiom-free (no functional extensionality). Non-vacuity:
  `ex_consistent_zero` / `ex_inconsistent_one` exhibit a two-target instance where consistency is a
  genuine constraint.
- **Non-vacuity (retraction).** `clamp3` (clamp to a cap at 3, a genuinely collapsing normalizer of
  the shape a real compensation has) discharges idempotence with no hypotheses (`clamp3_idem`), its
  fixed set is exactly `{n | n <= 3}` (`clamp3_fixed_iff`), and the retraction results instantiate at
  it (`clamp3_retracts_into`, `clamp3_image_iff_fixed`). So the section is about something, not a
  vacuous hypothesis.

- **Theorem 1 (retraction), operator half.** `RetractionOntoConsistent` proves the note's Corollary
  in general: any operator that is sound (its image lands in a consistent set `L`, Lemma A) and
  complete (it fixes `L`, Lemma B) is the idempotent retraction onto `L`, with image and fixed-point
  set both `L` (`rhoL_idempotent`, `rhoL_image_iff_L`, `rhoL_L_iff_fixed`). `FederatedOperator` then
  discharges Lemma A and Lemma B for a concrete federated operator `rhoF` (a root with local
  normalizer, plus a morphism target whose shared component is fixed from the root's normal form),
  so `rhoF` is the idempotent retraction onto its consistent set (`rhoF_retraction`,
  `rhoF_image_iff_L2`).
- **Order-independence, commutation core.** `updates_commute`: updates to two independent registry
  components commute (the local step of Lemma C, incomparable registries having disjoint reads and
  writes). The full result, that all topological orders agree, is mechanized in
  `FederationOrder.v` (below) without assuming the linear-extension connectivity fact.
- **Order-independence for arbitrary acyclic federations (`FederationOrder.v`).** Registries read the
  state only through their sources (`f_local`); an order is topological when it is duplicate-free and
  every in-order source comes earlier. `order_independent`: any two topological orders of the same
  registries give the same final state, from any initial state. The proof bubbles the first registry
  of one order to the front of the other (`bubble`, via the adjacent commutation `step_comm`), so the
  classical connectivity of linear extensions is never assumed. States are compared pointwise (no
  functional extensionality). A three-registry instance (`ex_orders_agree`) discharges every
  hypothesis.
- **Theorem 1 for a general acyclic federation.** `GeneralFederatedFold` models `rho_F` as a
  left-to-right fold over a topological order (state is a positional list; `stepAt` reads the
  finalized prefix and returns a position's finalized value), defines the consistent set `L_F`
  intrinsically (every position fixed by its step given its prefix), and proves Lemma A
  (`rhoFold_sound`, needing `stepAt` idempotent given a fixed prefix) and Lemma B
  (`rhoFold_complete`, needing only the definition). It therefore instantiates the Corollary:
  `rhoFold_retraction` and `rhoFold_image_iff_consistent` give that `rho_F` is the idempotent
  retraction onto `L_F` for every acyclic federation, not just the two-registry instance. The
  supporting `app_split_snoc` (splitting a snoc) is axiom-free.
- **Theorem 2 (compositionality).** `rhoFold_compositional` (via the fold-append law
  `rhoF_from_app`): the flat normalization of a federation split along a topological cut `J ++ K`
  equals the staged one, finalize the upstream block `J`, then continue with `K` on top of the
  collapsed (finalized) `J`. So an upstream sub-federation collapses to its finalized block and the
  combined normalizer factors as (normalize `J`) then (normalize `K`). Axiom-free.

`Print Assumptions` on the categorical-core headline results is "Closed under the global context";
they are in the axiom-free gate ([coq/README.md](../README.md#verify-it-yourself)).

## Categorical bridge (`CategoricalBridge.v`)

The companion paper's Proposition 1 and Theorem 1 on one concrete federation model, joining the
three pieces `Categorical.v` and `FederationOrder.v` prove separately: the consistent set with every
conjunct the paper states, the retraction onto it, and order-independence. Registries are indexed
by `nat`; registry `i` has a local normalizer `rho i`, sources `src i`, and (as a target) a shared
component read by `get i`, written by `ovr i`, and a resolver `res i`. `stepN i` overwrites the
shared component with the resolver value and then normalizes locally. All axiom-free.

- **Proposition 1 (`prop:one`), with the component conjunct.** `LF` is the paper's `L_F`: the tuple
  lies in the product of the valid sets `Phi_{R_i} = im(rho_i)` (`ProdPhi`) and every target's shared
  component equals its resolver value. `cat_LF_split`: `LF` is `ProdPhi` plus `Categorical.Consistent`.
  `cat_prop_one`: on the product of the valid sets, `L_F = eq(g, h)`. `cat_prop_one_product`: the
  product of valid sets is the equalizer of the identity and the product normalizer, factorwise
  Lemma 0's `eq(id, rho_i)` (via `fixed_is_equalizer`). `cat_prop_one_limit`: `L_F` is a single
  equalizer of two maps into a finite product, a finite limit in `Set`.
- **The bridge (`thm:one`).** `rhoFold_run`: `Categorical.rhoFold`, instantiated on
  (registry, value) pairs over a topological order, computes `FederationOrder.run` on that order.
  `consistentList_iff_LF`: Categorical's intrinsic `ConsistentList` is exactly the paper's `L_F`,
  given local idempotence, the lens law `putget`, and `sh_fixed` (the local normalizer fixes the
  overwritten shared component). `rhoFold_order_independent` and `rhoFold_order_perm`: the fold
  inherits `order_independent`.
- **Theorem 1 as stated.** `cat_thm_one_sound` (Lemma A, from `rhoFold_sound`),
  `cat_thm_one_complete` (Lemma B, from `rhoFold_complete`), `cat_thm_one_idempotent`,
  `cat_thm_one_image` and `cat_thm_one_fixed` (`im(rho_F) = Fix(rho_F) = L_F`),
  `cat_thm_one_order_independent`, and `cat_thm_one_fold_image` for the positional fold.
- **Corrected hypothesis.** `cat_thm_one_m1_counterexample`: with M1 read as validity preservation
  under overwrite (the paper's Background definition) plus local idempotence, Theorem 1 fails:
  `rho_F` does not land in `L_F` and is not idempotent, because compensation rewrites the shared
  component the morphism wrote. The hypothesis that makes Theorem 1 true is `sh_fixed`, the paper's
  own Section 3.3 reading of M1/R2.
- **Non-vacuity.** `nv_*`: three registries (2 reads 0 and 1), clamping normalizers and a summing
  resolver discharge `idem`, `putget` and `sh_fixed`; `nv_sound`, `nv_s0_not_LF` (L_F is a genuine
  constraint), `nv_orders_agree` (two topological orders) and `nv_prop_one`.

The gate also covers the Cat-cited `Categorical.v` names that were not in it: `fixed_is_equalizer`,
`retract_fixes_fixed`, `rhoL_idempotent`, `rhoL_image_iff_L`, `rhoL_L_iff_fixed`, `rhoFold_sound`,
`rhoFold_complete`, `rhoF_from_app`.

## Sheaf gluing over sub-federation covers (`SheafGluing.v`)

Audit gap 13 (the sheaf half): the categorical paper's Section 5, `prop:gluing` ("R1 + R2 is the
gluing axiom") and "the sheaf assembly over the full cover", which the paper states at the paper
level. Built on `CategoricalBridge.v` (the federation model of Theorem 1), `FederationOrder.v`,
`Collapse.v` and `Cohomology.v`, with no category-theory library: the site is finite and every
statement is about lists of registries. All axiom-free.

**The site and the presheaf.** An open set is a sub-federation `U`, a finite list of registries; a
cover of `W` is a list `C` of sub-federations with `concat C = W`. The presheaf `F` sends `U` to the
states consistent on `U` (`Sec U s`): every registry of `U` holds a normal form
(`InImage (rho i)`), and every target `B` whose constraint lies inside `U` (`Internal U B`: `B` in
`U`, `B` a target, all of `src B` in `U`, the paper's "rules whose footprint lies in `U`") has its
shared component equal to its resolver value. Sections over `U` are compared on `U` only
(`Agree U`), and restriction to `U'` included in `U` keeps the state (`sec_restrict`). `R1`
(source-determinacy: a resolver reads only its sources) makes `F(U)` depend on the values in `U`
alone (`sec_local`), so `F` is a presheaf of `U`-states; without `R1` it need not be
(`r1_failure`, last conjunct).

**Separation and gluing, separately.**

- `separation`: two states restricting to the same sections on every member agree on the union.
  No hypothesis.
- `gluing`, `sheaf_condition`: under `R1`, if the cover refines the constraints (`Refines C`: every
  target whose constraint lies inside the union has its whole footprint, the target and all its
  sources, inside one member), a family of local sections agreeing on the overlaps (`Compatible`)
  glues (`glue`, first member wins) to a section over the union restricting to each member; it is
  unique on the union by `separation`.
- `sheaf_exact`: on a refining cover, a family is the restriction of a global section iff it is a
  compatible family of local sections.
- `gluing_iff_local_global`: for fixed data under `R1`, gluing holds on `C` iff every state whose
  restriction to each member is a section is a section over the union.
- `sheaf_iff_refines` (exact and uniform in the data): gluing holds on `C` for every federation on
  the graph that satisfies `R1` iff `C` refines the constraints. Qualifier in the statement: the
  value type is inhabited and there are two distinct shared values (the refuting federation needs
  them).

The precise hypothesis is a condition on members, not on overlaps. "The overlaps contain every
morphism's source and target" is stronger than needed: in `chain_glues` the overlap `{1}` of the
cover `{0,1}`, `{1,2}` of the chain `0 -> 1 -> 2` contains no constraint, and gluing holds. What
the overlaps carry is the compatibility of the family.

**Which hypothesis each counterexample breaks.**

| Counterexample | Hypothesis broken | What fails |
|---|---|---|
| `triangle_fails` | `Refines`: the edge `0 -> 2` of the triangle lies in no member of the cover `{0,1}`, `{1,2}`, though the members overlap at `1` | a compatible family of local sections with no global section restricting to it |
| `r1_failure` | `R1`: registry 2's resolver reads registry 0, not a declared source; `Refines` holds for the declared footprints | no global section restricts to a compatible family; and `F` is not a presheaf of `U`-states (two states agreeing on `{1,2}`, one a section over `{1,2}`, one not) |
| `gluing_cex_overlap` (`Cohomology.v`'s `gluing_order_dependent`) | compatibility of the certificates on the overlap: two subsystems write one variable | the state sections agree on the overlap (the same valid set), the normalizers do not, no certificate restricts to both, and the union is order-dependent |

A federation has one writer per registry (a multi-source target merges its writers through its
resolver), so on a closed cover its certificates are always compatible (`cert_glue`). That is the
formal content of `prop:gluing`'s "R1 makes the merged normal form single-valued".

**Certificates.** On `CategoricalBridge.v`'s model (resolvers read the source values in order, so
`R1` holds by construction, `resL_R1`), the certificate of `U` is `rhoU o U`: the federated
normalizer run over the members of `U` in `o`'s order, registries outside `U` read as external
inputs.

- `cert_restrict_closed`: if `U` is closed under sources (`ClosedIn U`), the global normalizer
  restricted to `U` is `U`'s certificate, for any order. No other hypothesis.
- `cert_restrict`: for every `U` (with `o` topological), the global normal form on `U` is `U`'s
  certificate run on the state whose external inputs are replaced by their global normal forms
  (`patch`). `cert_pointwise` is the case `U = [i]`: each registry's normal form is one step from
  its sources' normal forms.
- `cert_restrict_iff` (exact): in a federation `o` closed under sources, the plain restriction
  equation holds for every data satisfying Theorem 1's hypotheses (idempotence, the lens law and
  `SC`) iff `U` is closed under sources.
- `sec_iff_LF`, `cert_retraction`: on a closed `U` the sections are `L_F` of `U`'s order, and under
  idempotence, the lens law and `SC` (the corrected Theorem 1 hypothesis, as in
  `cat_thm_one_sound` and `cat_thm_one_complete`) the certificate lands in `F(U)` and fixes it.
- `cert_glue`, `cert_sheaf`: on a cover by closed members, the certificates form a compatible family
  of local sections over a refining cover (`closed_refines`: a closed cover refines every
  constraint); their gluing is the certificate of the union and the global normalizer there; it
  lands in the sections over the union and fixes every one of them.
- `cert_needs_sc`: with `M1` (validity preservation) in place of `SC`, the certificate of the closed
  sub-federation `{0,1}` misses its sections (the federation of `cat_thm_one_m1_counterexample`).
  `prop:gluing`'s "R2 makes it land in the agreed valid set" holds with `SC` in the role the paper
  gives `R2`; `R2` itself is not the condition.
- `collapse_restrict`: `Collapse.v`'s convex form. For a convex `J`, the federated normal form on
  `J` is `rho_J` run after the upstream block `P` (from `collapse_nf_factor`, which rests on
  `collapse_nf_agree`). Convexity is what makes the patched inputs of `cert_restrict` computable
  before `J` as one block; for a closed `J` the patch is invisible (`cert_restrict_closed`).

**Non-vacuity.** `chain_glues` (the three-registry chain covered by two overlapping pairs; the
union's consistency is a genuine constraint), `triangle_fails`, `r1_failure`,
`sheaf_iff_refines_instance`, `vs_cert_sheaf` (the closed cover `{0,1}`, `{0,2}` of a fork
`0 -> 1`, `0 -> 2`, overlap `{0}`, glued certificate computed to `(3,3)` everywhere),
`chain_cert_nonclosed` (`{1,2}` is not closed: its certificate gives `(5,3)` at `1`, the global
normal form `(3,3)`), `cert_restrict_iff_instance`, `collapse_restrict_instance`.

**The boundary.** The sheaf condition for certificates is proved on covers by sub-federations
closed under sources. On other covers a certificate depends on external inputs; only the relative
restriction equation (`cert_restrict`) is proved, and no sheaf condition for relative certificates
is stated. The site is the registry-level one; the paper's variable-level site, where two subsystems
may write one variable, enters only through `gluing_cex_overlap`. The monotone-overlap regime
(cycles, least fixed points) is not covered: everything here is acyclic. The certificates are repair
certificates; event-order convergence of the glued system still needs the event-layer conditions.

## The federated theorems in corrected form (`FederationGRS.v`)

ROADMAP item 7, work package WP5 (rows F6 to F10 and F17 to F19 of `PAPER-MAP.md`). The federation
paper's Section "Federated Convergence" states its results for the federated rewrite system
`G_Fed`: apply steps run an event on its registry, and the compensation step is `rho_Fed` (phase 1:
`rho^*` on every component; phase 2: in topological order, overwrite each target's shared component
with its morphism image or resolver value). `FederationGRS.v` builds `G_Fed` as an instance of
`Governance.step` (federated states as lists, so Leibniz equality is the paper's state equality),
states the paper's hypotheses as a record, and mechanizes each result by label. Axiom-free.

The model:

- `PaperNet` (Part B) is the hypothesis set of `thm:resolved-convergence`: a shared/local
  decomposition of every state space (`mk`, `sh`, `lc`, Def. "Registry Morphism"), an acyclic network
  with a resolver `Gam j` per target reading only its sources (R1) and preserving validity (R2; M1
  for a single source), component WFC (`cj`, `Phij`, with `rho j` the iterate to validity) and
  component CC (CC1 on every same-registry pair, CC2 with the one-step compensation).
  `PaperTree` adds "each non-source has one incoming edge" (`thm:fed-cc`, `thm:fed-convergence`).
  `paper_common` derives the `Common` conditions of `FederationEvents.v` from them.
- `gapply`, `grho`, `gvalid` (Part A) are the apply step, `rho_Fed` and federal validity on list
  states; `gov e = grho o gapply e` is the governed step, and `gov_eq` shows it is
  `FedMachine.Apply`. The GUARDED system (`genab`: an event fires only at a federally valid state,
  compensation first) is `FedMachine.Apply` semantics as a rewrite system.
- `XU` is C1 for every valid target state, not only consistent ones (`FederationEvents.v`).

Results, by paper label:

| Label | Status | Coq |
|---|---|---|
| `lem:authority` (a) | exact (at every normal form) | `fed_lem_authority_a` (non-vacuity `fed_lem_authority_a_instance`); generic `source_projection`, `fed_authority_a_gen` |
| `lem:authority` (b) | exact | `fed_lem_authority_b` |
| `lem:authority` (c) | first clause exact; convergence clause refuted, corrected | `fed_lem_authority_c_local`; `fed_lem_authority_c_refuted`; `fed_lem_authority_c_corrected` |
| `lem:fed-termination` | exact, from ANY state | `fed_lem_fed_termination`, `single_round`, `phase2_invariant`, `fed_phase1_bound`, `grho_valid` |
| `lem:resolved-termination` | exact, from ANY state | `fed_lem_resolved_termination` |
| `thm:fed-cc` | refuted; corrected | `fed_thm_fed_cc_refuted`; `fed_thm_fed_cc_corrected` (XU), `fed_thm_fed_cc_corrected_machine` (C1 + C2, at valid states) |
| `thm:fed-convergence` | refuted; corrected; exact | `fed_thm_fed_convergence_refuted`, `fed_c2_paper_counterexample`; `fed_thm_fed_convergence_corrected` (XU), `fed_thm_fed_convergence_guarded` (C1 + C2); `fed_thm_fed_convergence_exact` |
| `thm:resolved-convergence` | refuted; corrected; exact | `fed_thm_resolved_convergence_refuted`; `fed_thm_resolved_convergence_corrected`, `fed_thm_resolved_convergence_guarded`; `fed_thm_resolved_convergence_exact` |
| `cor:fed-nf` | refuted; corrected | `fed_cor_fed_nf_refuted`; `fed_cor_fed_nf_corrected` (generic `fed_nf_constructive`, `fed_nf_recipe_xu`) |
| `cor:resolved-nf` | corrected (refuted by the tree case) | `fed_cor_resolved_nf_corrected` |

The bridge to `Governance.step`: `fed_grs_exact` (an instance of `cc_exact_from`: `G_Fed` has unique
normal forms from `s0` for every buffer iff its CC1 and CC2 hold on the states reachable from
`s0`), `fed_grs_un_c1_c2` (unique normal forms imply C1 and C2 at the reachable witnesses of
`fed_exact`), `grs_unique_nf` (XU and component CC give CC1 and CC2 everywhere, then
`governance_unique_normal_forms`, the paper's proof route), and `fed_guarded_exact` (the guarded
system has unique normal forms from a federally valid `s0` for every buffer iff C1 and C2 hold at
the reachable witnesses, via `jc_unique_normal_forms` and `fed_exact`).

Corrected statements (the network hypotheses H are those of the paper: a tree, or an acyclic
resolved network, with M1 or R1 and R2, component WFC and component CC):

- `thm:fed-cc`: H and XU imply that `G_Fed` satisfies CC1 and CC2 at every federated state. H, C1
  and C2 imply CC1 at every federally valid state. H, C1 and C2 do not imply CC2 of `G_Fed`
  (`fed_grs_c1_c2_insufficient`).
- `thm:fed-convergence`, `thm:resolved-convergence`: H and XU imply unique normal forms of `G_Fed`
  from every configuration, and every configuration reaches a federally valid one. H, C1 and C2
  imply unique normal forms of the guarded system from every federally valid start. Exactly: the
  guarded system converges from `s0` iff C1 and C2 hold at the witnesses reachable from `s0`.
- `cor:fed-nf`, `cor:resolved-nf`: under C1 and C2, the normal form `Z` of any event sequence from a
  federally valid start is the unique solution, in topological order, of
  `Z_j = ow_Z(x_m)`, `x_0 = ow_Z(s_j)`, `x_t = ow_Z(sig_{e_t}(x_{t-1}))` over the events of `j`
  in order, where `ow_Z` overwrites the shared component from the FINALIZED sources. Under XU this
  collapses to the paper's recipe `Z_j = ow_Z(sig_{e_m}(...sig_{e_1}(s_j)))`.

Counterexamples, each discharging every paper hypothesis (`au_paper`, `cw_paper`, `gg_paper`):

- `fed_thm_fed_cc_refuted`, `fed_thm_fed_convergence_refuted`, `fed_thm_resolved_convergence_refuted`,
  `fed_lem_authority_c_refuted`: the audit federation (`audit_counterexample` as a paper network).
  From one federally valid state and the buffer `[recall; sell]`, `G_Fed` reaches two federally
  valid normal forms; they agree on the source and on the target's shared flag and differ in the
  target's local `sold` (0 versus 1).
- `fed_c2_paper_counterexample`: C1 holds as well (the `c2_counterexample` as a paper network,
  with the source's compensation made WFC); `G_Fed` still diverges.
- `fed_grs_c1_c2_insufficient`: C1 and C2 hold, every FedMachine permutation converges and the
  guarded system has unique normal forms, but the unrestricted `G_Fed` has two normal forms: two
  target events applied before compensation, the second reading the shared value the first wrote.
- `fed_cor_fed_nf_refuted`: in the same federation the paper's recipe gives `(false, true)`, every
  event order gives `(false, false)`, and the corrected recipe `Gc` gives `(false, false)`.

Non-vacuity: `fed_supply_paper_instance` (the supply chain as a paper network: H, XU, C1, C2, and
the unique-normal-form conclusion instantiated) and `fed_grs_c1_c2_insufficient` (H, C1 and C2
without XU). The list encoding adds bookkeeping hypotheses only: registries are `0 .. n-1`, indices
outside the network are unconstrained, validity and state equality are decidable (the paper's state
spaces are finite).

## Roadmap: mechanizing the categorical layer (companion paper)

The companion paper (categorical structure of federated convergence) rests on a small structural
core that is elementary in `Set` and finite posets, so it mechanizes by leaning on the other modules
rather than pulling in heavy category-theory libraries. Progress, in priority order:

1. **Lemma 0 (a registry is an equalizer).** DONE (`Categorical.v`): `image_iff_fixed`,
   `fixed_is_equalizer`. `Fix(rho) = im(rho) = eq(id, rho)`, axiom-free.
2. **Proposition 1 (the consistent set is a finite limit).** DONE (`Categorical.v`):
   `consistent_iff_equalizer`. The federated consistent set is the equalizer of the shared-component
   and resolver-value maps, axiom-free (product over targets modeled as a list).
3. **Theorem 1 (federation retraction, acyclic).** DONE (`Categorical.v`) for the operator content:
   the general Corollary (`RetractionOntoConsistent`), a concrete two-registry operator
   (`FederatedOperator`), and the general acyclic fold `rho_F` over a topological order
   (`GeneralFederatedFold`: `rhoFold_retraction`, `rhoFold_image_iff_consistent`) discharging Lemma A
   and Lemma B, so `rho_F` is the idempotent retraction onto `L_F` for every acyclic federation.
   Full order-independence is DONE (`FederationOrder.v`: `order_independent`), proved by bubbling
   rather than through linear-extension connectivity.
4. **Theorem 2 (compositionality).** DONE (`Categorical.v`): `rhoFold_compositional` (via
   `rhoF_from_app`). The flat normalization over a topological cut `J ++ K` equals finalizing `J`
   then continuing with `K`, so an upstream sub-federation collapses to its finalized block.

With Lemma 0, Proposition 1, Theorem 1 (retraction, general acyclic fold), and Theorem 2
(compositionality) mechanized axiom-free, the structural core of the companion is complete. The development
was then extended past the structural core: full order-independence (`FederationOrder.v`) and the
cohomological completion through `H^1` as a quotient (`Cohomology.v`, `CohomologyMin.v`,
`CohomologyGraph.v`). The loop-composite fixed-point diagnostic is implemented in gsm as
`Federation.DiagnoseCycle`.

Kept at paper level after the first mechanization pass, and since mechanized:

- The general non-invertible case reduces to the loop-composite fixed-point condition, a dynamical
  statement rather than group cohomology. It is now mechanized: on a single cycle a section exists
  iff the loop composite has a fixed point, iff some seed reaches one (`thm_obstruction_general`,
  `thm_obstruction_reachable`, `CohomologyGeneral.v`); with a root, iff the driven state satisfies
  every non-tree edge (`rooted_criterion`); and on any graph, iff some assignment of a root set's
  values drives a consistent state (`root_set_criterion_graph`, `RootSet.v`), where deciding it is
  NP-complete in general (the 3-SAT reduction's correctness, parsimony and size, and the NP
  certificate, are mechanized in `LossyHardness.v`; NP-completeness follows by the standard
  argument).
- The operational core of that story is `gsm`'s `Federation.DiagnoseCycle` (the loop-composite
  fixed-point / orbit test). Its reading is mechanized: no section iff no seed reaches a fixed point
  (`c15_exact_refuter`), and one seed is definitive on the regular action
  (`c15_regular_definitive`) but not in general (`c15_definitive_claim_false`).

The rank on the nerve as a 2-complex is mechanized: `H^1` with the triangle relations is classified
for any group and counted over Z/2 (`nerve_H1_classification`, `nerve_H1_Z2_count`,
[`CohomologyNerve.v`](non-monotone-invertible.md#h1-on-the-nerve-as-a-2-complex-cohomologynervev)).
The sheaf gluing assembly is mechanized for consistent states on every refining cover and for
certificates on covers closed under sources, with its boundary stated
([`SheafGluing.v`](#sheaf-gluing-over-sub-federation-covers-sheafgluingv)).

Status: these are targets for the companion submission, tracked here so the axiom-free gate
(currently 3030 theorems; [coq/README.md](../README.md#verify-it-yourself)) stays legible. Nothing in this roadmap is claimed proven until it lands in a
module and passes the gate.
