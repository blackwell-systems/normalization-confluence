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

## Related-work positioning (review-critical)
- Abramsky-Brandenburger sheaf contextuality: closest prior art (local consistency, global
  impossibility via Cech cohomology). Distinguish: our presheaf is over subsystem overlaps of a
  normalizer structure; the obstruction is to a global convergent normal form; it is tied to an
  operational diagnostic and a coordination decomposition, not measurement contexts.
- Herlihy-Shavit-Rajsbaum combinatorial topology of distributed computing: topology for task
  solvability / wait-freedom, a different question. Cite to preempt conflation.
- CALM (Hellerstein-Ameloot) and I-confluence (Bailis): the minimal-coordination result refines
  these, localizing a global verdict to a cycle basis.
- CRDTs / join-semilattices: the monotone route is the CRDT case (machine-checked in `CRDT.v`); the
  well-founded-compensation regime is strictly broader.

## Mechanization status (coq/, axiom-free gate)
- DONE (`Categorical.v`): Lemma 0 (image = fixed = equalizer), Theorem 1 retraction skeleton, Prop 1
  (consistent set = equalizer, a finite limit), with non-vacuity witnesses. In the axiom-free gate.
- IN PROGRESS: Theorem 1 at the concrete federated operator `rho_F` (soundness + completeness, so it
  instantiates the abstract retraction) and order-independence; Theorem 2 (compositionality).
- Paper-level only: the cohomological completion (invertible fragment); the general case reduces to
  the loop-composite fixed-point condition, which is implemented as `DiagnoseCycle`.

## Open gates before drafting prose
- Confirm venue target (LMCS or a theory-leaning systems venue; ACT if the categorical framing
  leads).
- Decide the invertible-fragment framing exactly as above (settled: lead general, cohomology sharp on
  the lossless fragment).
