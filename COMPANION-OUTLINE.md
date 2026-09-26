# Companion paper: outline and decisions

Status: planning artifact for the companion to the two published papers. Not prose yet. This
records the thesis, contribution ranking, framing decisions, the inhabitation verdict, related-work
positioning, and the mechanization status, so drafting starts from settled ground.

## Working title
The Categorical Structure of Federated Convergence: Limits, Sheaves, and Minimal Coordination.

## Thesis (one sentence)
A federation's convergent states are a limit and its convergence certificates form a sheaf, so the
obstruction to global convergence is cohomological (a holonomy class); this explains the two known
convergence regimes as one picture, yields a computable obstruction diagnostic, and refines the
CALM / I-confluence coordination boundary into a minimal, localized coordinated core.

One paper (decided), not a split: the arc is cohesive (limit motivates the sheaf, the sheaf yields
the cohomology, the cohomology yields the minimal-coordination decomposition) and each half is thin
alone.

## Framing decision (gate 2, pressure-tested)
Do NOT headline "cohomology." Lead with "when must a federation coordinate, and how little
suffices." The general, motivation-aligned results lead; the cohomology is the mechanism that
sharpens the answer on a characterized fragment. Rationale: the cohomology-as-machinery is the most
exposed and least novel component (adjacent to Abramsky-Brandenburger contextuality), and the clean
H^1 classification holds only in the invertible fragment. Leading with it would invite rejection;
leading with the diagnostic and the coordination decomposition puts the implemented, general,
NC-specific results in front.

## Contributions, ranked (novelty over risk)
1. Minimal-coordination decomposition. A federation splits into a coordination-free majority and a
   minimal coordinated core, the core being a cycle basis of the obstruction (first-Betti-number
   many loops), not the whole network. Refines CALM and I-confluence from a global yes/no into a
   localized mixed-consistency partition. SCOPED: the clean Betti-number minimality is rigorous in
   the invertible (lossless) fragment; see the inhabitation verdict below.
2. The completion: H^0 = convergent states, H^1 = holonomy obstruction, cycle-basis generators, the
   two ways H^1 vanishes = the acyclic and monotone regimes unified.
3. Computable obstruction diagnostic. The loop composite over the shared subspace as the witness,
   bounded by the shared subspace not the product, implemented as `DiagnoseCycle`. General
   (monoid transitions), a real new capability.
4. Federation-as-limit and free compositionality. Normal forms are a limit (Lemma 0, Prop 1,
   Theorem 1/1'); compositionality (Theorem 2) is a corollary of one structural fact; assume-guarantee
   via ports (Theorem 2') is the certificate story.

## The capability the inhabitation investigation surfaced
gsm today rejects the cyclic-invertible-nontrivial-holonomy case (non-monotone cycle; Build refuses;
`DiagnoseCycle` explains the orbit). Minimal coordination turns this into a new capability: accept it
with a coordination boundary on a cycle basis, provably minimal in the lossless fragment. This
completes the regime picture into three ways a cycle resolves: monotone repair (converges by order),
invertible with trivial holonomy (converges), invertible with non-trivial holonomy (cannot converge
coordination-free; minimal coordination on a cycle basis is the fix). The third line is where H^1
earns its place.

## Inhabitation verdict (grounds the scoping)
A morphism is invertible on the shared fiber exactly when it is a lossless relabeling (copy, boolean
NOT, bijective enum/unit/format map). It is non-invertible when it collapses information (max, min,
most-restrictive-wins, clamp-to-cap, reset), which includes every multi-source resolver. Checked
against gsm's actual example federations:

- Resolvers are structurally non-invertible AND structurally acyclic (multi-source targets live on
  DAGs), so the collapsing maps never touch the cyclic case; they sit where H^1 is trivial anyway.
- The cyclic examples split into invertible (copy/flip/NOT loops, where the obstruction phenomenon
  lives, the negation loop being the canonical orbit witness) and monotone-collapsing (the max mesh,
  handled by the monotone route).

So the invertible fragment is non-empty and characterizable (lossless relabeling morphisms), and it
is exactly where cyclic obstruction is resolved by coordination rather than by order. But the
cyclic-and-invertible intersection that the Betti-number minimality needs is a real but non-dominant
corner (most federations are acyclic, or monotone-cyclic). Verdict: minimality is a scoped theorem,
not a universal headline. The characterization (invertible = lossless relabeling) is itself a
contribution, since it states precisely when the sharp classification applies.

## Section outline
1. Introduction: the local-to-global question for convergence; the two-regime puzzle the base papers
   leave unexplained; contributions.
2. Background: registries, normalizers, WFC/CC, federation M1/R1/R2 (cited, not reproved).
3. Normal forms are a limit: Lemma 0, Prop 1, Theorem 1/1'.
4. Compositionality for free: Theorem 2, Theorem 2' (ports), the resolver boundary.
5. Certificates form a sheaf: the presheaf, the non-naive gluing counterexample, R1 + R2 as the
   gluing axiom, the single-writer and monotone regimes.
6. The cohomological completion: H^0, H^1, cycle-basis generators, the two routes to H^1 = 0.
7. Minimal coordination: the proposition, the coordination-free-majority + coordinated-core
   decomposition, the accept-with-coordination capability, positioning against CALM and I-confluence.
8. The diagnostic: loop composite as computable witness; `DiagnoseCycle`; worked settle-vs-orbit
   examples.
9. Scope, limitations, related work, future work.

## Elevate vs. keep as note / future work
- Elevate to stated theorems: Lemma 0, Prop 1, Theorem 1/1', Theorem 2/2', the completion theorem
  (invertible fragment), the minimal-coordination proposition (scoped).
- Keep as candid limitation: the clean cohomological iff holds only in the invertible/torsor
  fragment; the general non-invertible case reduces to the loop-composite fixed-point condition (a
  dynamical, not group-cohomological, statement). Computing the H^1 class itself and the non-abelian
  analogue are open.
- Leave out of this paper: the free-monoid / event-sourcing bridge (belongs with the single-registry
  paper) and Squier / higher-dimensional rewriting (a different paper).

## Related-work positioning (review-critical, literature-checked September 2026)

Verdict of the check: the novelty holds, and it is sharper than "we apply cohomology to
convergence." The sheaf-cohomology-as-obstruction TEMPLATE is not new and must not be claimed as
such; what is new is the OBJECT (federated normalization convergence), the OPERATIONAL diagnostic,
and the MINIMALITY-of-coordination result. Position accordingly and cite the closest work up front.

Closest prior art and the precise delineation:

- Sheaf cohomology for distributed systems, SAME tool, DIFFERENT object. "A Sheaf-Theoretic
  Characterization of Tasks in Distributed Systems" (arXiv:2503.02556, 2025) uses cellular-sheaf
  cohomology so that terminating solutions are the global sections and the cohomology encodes
  obstructions, but for decision-TASK solvability (the Herlihy-Shavit-Rajsbaum lineage: consensus,
  k-set agreement, under failures and message adversaries), not convergence of a replicated /
  federated normalization. Abramsky-Brandenburger sheaf contextuality is the same template for
  quantum non-locality. NC's object is different: the presheaf is over subsystem overlaps of a
  NORMALIZER structure (WFC/CC + M1/R1/R2); H^0 is the convergent states, H^1 is the holonomy
  obstruction to a global consistent NORMAL FORM. No sheaf-cohomology work targets the
  eventual-consistency / CRDT convergence obstruction. Cite 2503.02556 and Abramsky-Brandenburger
  prominently and state the object difference in the first related-work paragraph.
- Herlihy-Shavit-Rajsbaum combinatorial topology: task solvability / wait-freedom via simplicial
  complexes, the lineage 2503.02556 sits in. Different question from convergence; cite to preempt
  conflation.
- CALM and its recent refinements give a GLOBAL verdict; NC LOCALIZES it. CALM (Hellerstein-Ameloot,
  monotone iff coordination-free), "Complete CALM: A Coordination Criterion for Specifications"
  (arXiv:2602.09435, 2026, monotone at the semantic level), and "A Preliminary Model of
  Coordination-free Consistency" (arXiv:2504.01141, 2025) all answer WHETHER coordination is
  avoidable, as a global yes/no. NC's minimal-coordination result refines this into WHERE and HOW
  LITTLE: a minimal coordinated core equal to a cycle basis of H^1 (first-Betti-number many loops), a
  localized mixed-consistency partition. The literature check found no prior work localizing
  coordination to a cycle basis / Betti number for convergence; this is the novel edge.
- I-confluence (Bailis, coordination avoidance) and mixed-consistency programming models (e.g.
  Gallifrey's branch/merge): I-confluence is a global avoidability criterion; mixed-consistency
  models are developer-specified mechanisms, not a topological minimality theorem. NC gives the
  minimality result they lack.
- CRDTs / join-semilattices and category-theoretic CRDT work (commutative co-semigroups / quantales):
  the monotone route is the CRDT case (machine-checked in `CRDT.v`); the well-founded-compensation
  regime is strictly broader. These are algebraic foundations, not a cohomological obstruction or a
  coordination-minimality result.

Novel contributions, defended against the above:
1. Sheaf / cohomological obstruction for federated NORMALIZATION convergence (a new object for a
   known tool), with H^0 = convergent states and H^1 = holonomy.
2. The loop-composite fixed-point DIAGNOSTIC: general (monoid transitions, not just the invertible
   fragment) and IMPLEMENTED as `Federation.DiagnoseCycle`. An operational capability the prior
   sheaf-obstruction work does not have.
3. Minimal-coordination decomposition via a cycle basis (localizes CALM / I-confluence). No prior
   hit at this intersection.
4. Axiom-free MECHANIZATION of the limit / retraction / compositionality core (`Categorical.v`),
   rare among category-theory-flavored submissions and absent from all the above.

Residual risk: do not overclaim the cohomology template. Lead with object + diagnostic + minimality,
cite 2503.02556 / Abramsky-Brandenburger / Complete CALM early, and a final fresh arXiv sweep right
before submission is still prudent (the field is active: three of the closest works are 2025-2026).

Sources checked: arXiv:2503.02556, arXiv:2602.09435, arXiv:2504.01141, arXiv:2411.16355, plus the
canonical CALM (CACM 2020), I-confluence (Bailis 2014), CRDTs (Shapiro 2011), and
Herlihy-Shavit-Rajsbaum.

## Mechanization status (coq/, axiom-free gate)
The structural core is mechanized axiom-free in `Categorical.v` (gate at 29 theorems):
- Lemma 0: image = fixed-point set = equalizer of (id, rho).
- Proposition 1: the consistent set is the equalizer of the shared-component and resolver-value maps
  (a finite limit), product over targets modeled as a list, no functional extensionality.
- Theorem 1 (retraction): the general Corollary (sound + complete give the idempotent retraction
  onto a consistent set L), a concrete two-registry operator, and the GENERAL acyclic `rho_F` as a
  topological-order fold discharging Lemma A / Lemma B, so `rho_F` is the idempotent retraction onto
  `L_F` for every acyclic federation.
- Theorem 2 (compositionality): the fold-append law, flat normalization over a topological cut
  `J ++ K` equals finalizing `J` then continuing with `K` (an upstream sub-federation collapses to
  its finalized block).

Cohomological layer, single-cycle essence mechanized axiom-free (`Cohomology.v`, gate at 33):
- The gluing counterexample (agreement on valid values is not enough).
- The completion theorem's single-cycle essence: in the invertible fragment a section exists iff the
  holonomy is trivial (`fixed_point_iff_trivial_holonomy`), with the negation-orbits and
  identity-settles witnesses.

Deliberately paper-level (not mechanized):
- The assembly of the per-cycle holonomies into the nerve's `H^1` as a quotient, with cycle-basis
  generators and Betti-number rank; the cohomology-proper class computation and the non-abelian
  analogue. The general non-invertible case reduces to the loop-composite fixed-point condition,
  implemented in gsm as `DiagnoseCycle`.
- Full order-independence: the commutation core is mechanized; the linear-extension connectivity that
  lifts it to all topological orders is cited as classical.

## Open gates before drafting prose
- Confirm venue target (LMCS or a theory-leaning systems venue; ACT if the categorical framing
  leads).
- Decide the invertible-fragment framing exactly as above (settled: lead general, cohomology sharp on
  the lossless fragment).
